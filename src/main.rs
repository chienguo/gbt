use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use anyhow::Context;
use anyhow::Result;
use clap::Parser;
use clap::Subcommand;
use thiserror::Error;

// Available if you need it!
// use serde_bencode

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  #[command(subcommand)]
  command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
  Decode { value: String },
  Info { torrent: PathBuf },
}

#[derive(Debug, PartialEq, Eq)]
enum Bencode {
  Int(i64),
  Bytes(Vec<u8>),
  List(Vec<Bencode>),
  Dict(HashMap<Vec<u8>, Bencode>),
}

impl fmt::Display for Bencode {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Bencode::Int(i) => write!(f, "{i}"),
      Bencode::Bytes(b) => {
        if let Ok(s) = std::str::from_utf8(b) {
          if s.chars().all(|c| c.is_ascii() && !c.is_control()) {
            return write!(f, "\"{s}\"");
          }
        }
        write!(f, "{b:?}")
      }
      Bencode::List(l) => {
        write!(f, "[")?;
        for (idx, item) in l.iter().enumerate() {
          if idx != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{item}")?;
        }
        write!(f, "]")
      }
      Bencode::Dict(d) => {
        write!(f, "{{")?;
        let mut sorted: Vec<_> = d.iter().collect();
        sorted.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

        for (idx, (k, v)) in sorted.iter().enumerate() {
          if idx != 0 {
            write!(f, ", ")?;
          }
          if let Ok(s) = std::str::from_utf8(k) {
            write!(f, "\"{s}\"")?;
          } else {
            write!(f, "{k:?}")?;
          }
          write!(f, ":{v}")?;
        }
        write!(f, "}}")
      }
    }
  }
}

#[derive(Debug, Error)]
enum BencodeParseError {
  #[error("Invalid bencode format at position {position}")]
  InvalidFormat { position: usize },

  #[error("Unterminated value starting at {start}")]
  UnterminatedValue { start: usize },

  #[error("Invalid integer format: {source}")]
  InvalidInteger {
    #[source]
    source: std::num::ParseIntError,
  },

  #[error("Invalid string length: {source}")]
  InvalidStringLength {
    #[source]
    source: std::num::ParseIntError,
  },

  #[error("Dictionary key must be byte string")]
  DictKeyNotString,

  #[error("Dictionary keys not lexically ordered")]
  DictKeysNotSorted,
}

type ParseResult<'a, T> = Result<(T, &'a [u8]), BencodeParseError>;

fn parse_bencode(input: &[u8]) -> Result<Bencode> {
  let original_len = input.len();
  let (result, remaining) =
    parse_value(input).with_context(|| format!("Parsing failed for input: {input:?}"))?;

  if !remaining.is_empty() {
    let consumed = original_len - remaining.len();
    anyhow::bail!(BencodeParseError::InvalidFormat { position: consumed });
  }

  Ok(result)
}

fn parse_value(input: &[u8]) -> ParseResult<Bencode> {
  let start_pos = input.as_ptr() as usize;

  match input.first() {
    Some(b'i') => parse_int(input),
    Some(b'l') => parse_list(input),
    Some(b'd') => parse_dict(input),
    Some(b'0'..=b'9') => parse_bytes(input),
    _ => Err(BencodeParseError::InvalidFormat {
      position: input.as_ptr() as usize - start_pos,
    }),
  }
}

fn parse_int(input: &[u8]) -> ParseResult<Bencode> {
  let start = input.as_ptr() as usize;
  let mut cursor = &input[1..]; // Skip 'i'

  let end = cursor
    .iter()
    .position(|&c| c == b'e')
    .ok_or(BencodeParseError::UnterminatedValue { start })?;

  let num_str = &cursor[..end];
  let num = std::str::from_utf8(num_str)
    .map_err(|_| BencodeParseError::InvalidFormat { position: start })?
    .parse::<i64>()
    .map_err(|e| BencodeParseError::InvalidInteger { source: e })?;

  cursor = &cursor[end + 1..];
  Ok((Bencode::Int(num), cursor))
}

fn parse_bytes(input: &[u8]) -> ParseResult<Bencode> {
  let colon_pos =
    input
      .iter()
      .position(|&c| c == b':')
      .ok_or(BencodeParseError::InvalidFormat {
        position: input.as_ptr() as usize,
      })?;

  let len_str = &input[..colon_pos];
  let len = std::str::from_utf8(len_str)
    .map_err(|_| BencodeParseError::InvalidFormat {
      position: input.as_ptr() as usize,
    })?
    .parse::<usize>()
    .map_err(|e| BencodeParseError::InvalidStringLength { source: e })?;

  let start = colon_pos + 1;
  let end = start + len;
  if end > input.len() {
    return Err(BencodeParseError::UnterminatedValue {
      start: input.as_ptr() as usize,
    });
  }

  let bytes = input[start..end].to_vec();
  Ok((Bencode::Bytes(bytes), &input[end..]))
}

fn parse_list(input: &[u8]) -> ParseResult<Bencode> {
  let mut elements = Vec::new();
  let mut cursor = &input[1..]; // Skip 'l'

  while !cursor.is_empty() && cursor[0] != b'e' {
    let (element, new_cursor) = parse_value(cursor)?;
    elements.push(element);
    cursor = new_cursor;
  }

  if cursor.is_empty() {
    return Err(BencodeParseError::UnterminatedValue {
      start: input.as_ptr() as usize,
    });
  }

  Ok((Bencode::List(elements), &cursor[1..])) // Skip 'e'
}

fn parse_dict(input: &[u8]) -> ParseResult<Bencode> {
  let mut dict = HashMap::new();
  let mut cursor = &input[1..]; // Skip 'd'
  let mut prev_key: Option<Vec<u8>> = None;

  while !cursor.is_empty() && cursor[0] != b'e' {
    // Parse key
    let (key, new_cursor) = match parse_value(cursor)? {
      (Bencode::Bytes(k), rem) => (k, rem),
      _ => return Err(BencodeParseError::DictKeyNotString),
    };

    // Parse value
    let (value, new_cursor) = parse_value(new_cursor)?;

    // Check ordering
    if let Some(prev) = &prev_key {
      if &key < prev {
        return Err(BencodeParseError::DictKeysNotSorted);
      }
    }
    prev_key = Some(key.clone());

    dict.insert(key, value);
    cursor = new_cursor;
  }

  if cursor.is_empty() {
    return Err(BencodeParseError::UnterminatedValue {
      start: input.as_ptr() as usize,
    });
  }

  Ok((Bencode::Dict(dict), &cursor[1..])) // Skip 'e'
}

// Usage: your_program.sh decode "<encoded_value>"
fn main() -> Result<()> {
  let args = Args::parse();

  match args.command {
    Command::Decode { value } => {
      let v = parse_bencode(value.as_bytes()).unwrap();
      println!("{v}");
    }
    Command::Info { torrent } => {
      let mut file = File::open(torrent)?;
      let mut data = vec![];
      file.read_to_end(&mut data)?;
      let value = parse_bencode(&data).unwrap();
      println!("{value}");
    }
  }

  Ok(())
}
