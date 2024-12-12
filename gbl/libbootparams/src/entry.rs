// Copyright 2024, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Entities to parse and iterate over both kernel command line and bootconfig.

use core::fmt::{Display, Formatter};
use liberror::{Error, Result};

/// A struct representing a key-value entry inside kernel command line or bootconfig.
#[derive(Debug, PartialEq, Eq)]
pub struct Entry<'a> {
    /// Boot parameters entry key.
    pub key: &'a str,
    /// Boot parameters entry value (may be not presented).
    pub value: Option<&'a str>,
}

/// Convert Entry into kernel command line / bootconfig compatible string.
impl<'a> Display for Entry<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.value {
            Some(value) => write!(f, "{}={}", self.key, value),
            None => write!(f, "{}", self.key),
        }
    }
}

/// To iterate over kernel command line entries.
pub struct CommandlineParser<'a> {
    data: &'a str,
    pos: usize,
}

impl<'a> CommandlineParser<'a> {
    /// Creates a new iterator from raw command line.
    pub fn new(data: &'a str) -> Self {
        CommandlineParser { data, pos: 0 }
    }

    fn remains(&self) -> &'a str {
        &self.data.get(self.pos..).unwrap_or("")
    }

    fn peek(&self) -> Option<char> {
        self.remains().chars().next()
    }

    fn skip(&mut self, n: usize) {
        self.pos += n;
    }

    fn take_while<F>(&mut self, predicate: F) -> &'a str
    where
        F: Fn(char) -> bool,
    {
        let remains = self.remains();
        let n = match remains.find(|c: char| !predicate(c)) {
            Some(end) => end,
            // Take everything if we cannot find.
            None => remains.len(),
        };

        self.pos += n;
        &remains[..n]
    }

    fn skip_whitespaces(&mut self) {
        self.pos += self.remains().len() - self.remains().trim_start().len();
    }

    fn parse_key(&mut self) -> Option<&'a str> {
        self.skip_whitespaces();

        let key = self.take_while(|c| !c.is_whitespace() && c != '=');

        match key.is_empty() {
            true => None,
            false => Some(key),
        }
    }

    fn parse_value(&mut self) -> Result<Option<&'a str>> {
        match self.peek() {
            // Skip the '=' character.
            Some('=') => self.skip(1),
            // No value.
            Some(c) if c.is_whitespace() => return Ok(None),
            // End of input.
            None => return Ok(None),
            // Invalid input
            _ => {
                self.skip(self.remains().len());
                return Err(Error::InvalidInput);
            }
        }

        let value = match self.peek() {
            // Check for the open quote.
            Some('"') => {
                // Skip it.
                self.skip(1);
                let value = self.take_while(|c| c != '"');

                // Check for the close quote.
                match self.peek() {
                    Some('"') => {
                        // Skip it.
                        self.skip(1);
                        value
                    }
                    _ => {
                        self.skip(self.remains().len());
                        return Err(Error::InvalidInput);
                    }
                }
            }
            _ => self.take_while(|c| !c.is_whitespace()),
        };

        Ok(Some(value))
    }
}

/// Parse kernel command line format, so we can iterate over key-value entries.
/// https://www.kernel.org/doc/html/v4.14/admin-guide/kernel-parameters.html
impl<'a> Iterator for CommandlineParser<'a> {
    type Item = Result<Entry<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.parse_key() {
            Some(key) => match self.parse_value() {
                Ok(value) => Some(Ok(Entry { key, value })),
                Err(e) => Some(Err(e)),
            },
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kernel_command_line_valid_key_value() {
        let mut iterator = CommandlineParser::new(
            "video=vfb:640x400,bpp=32,memsize=3072000 console=ttyMSM0,115200n8 earlycon bootconfig",
        );

        assert_eq!(
            iterator.next(),
            Some(Ok(Entry { key: "video", value: Some("vfb:640x400,bpp=32,memsize=3072000") }))
        );
        assert_eq!(
            iterator.next(),
            Some(Ok(Entry { key: "console", value: Some("ttyMSM0,115200n8") }))
        );
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "earlycon", value: None })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "bootconfig", value: None })));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_multiple_spaces_between_entries() {
        let mut iterator = CommandlineParser::new("key1=val1   key2    key3=val3   key4=val4   ");
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key1", value: Some("val1") })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key2", value: None })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key3", value: Some("val3") })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key4", value: Some("val4") })));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_no_values() {
        let mut iterator = CommandlineParser::new("key1 key2 key3");
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key1", value: None })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key2", value: None })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key3", value: None })));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_empty_values() {
        let mut iterator = CommandlineParser::new(r#"key1="" key2="" key3="""#);
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key1", value: Some("") })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key2", value: Some("") })));
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key3", value: Some("") })));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_quoted_values() {
        let mut iterator = CommandlineParser::new(r#"key1="value with spaces" key2="value""#);
        assert_eq!(
            iterator.next(),
            Some(Ok(Entry { key: "key1", value: Some("value with spaces") }))
        );
        assert_eq!(iterator.next(), Some(Ok(Entry { key: "key2", value: Some("value") })));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_value_with_new_line() {
        let mut iterator = CommandlineParser::new("key1=\"value with \n new line\"");
        assert_eq!(
            iterator.next(),
            Some(Ok(Entry { key: "key1", value: Some("value with \n new line") }))
        );
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_invalid_missing_closing_quote() {
        let mut iterator = CommandlineParser::new(r#"key="value without closing quote key2=val2"#);
        assert_eq!(iterator.next(), Some(Err(Error::InvalidInput)));
        // After encountering invalid input, the iterator may not produce more entries.
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_empty() {
        let mut iterator = CommandlineParser::new("");
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn test_kernel_command_line_whitespace_only() {
        let mut iterator = CommandlineParser::new("    \t   \n    ");
        assert_eq!(iterator.next(), None);
    }
}
