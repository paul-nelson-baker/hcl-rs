//! Formatter implementation used by the `Serializer` to construct HCL documents.

use super::escape::{CharEscape, ESCAPE};
use std::io;
use unicode_ident::{is_xid_continue, is_xid_start};

mod private {
    pub trait Sealed {}
}

/// Abstracts away serializing the HCL control characters.
///
/// This trait is sealed to prevent implementation outside of this crate as its specifics might
/// change in a breaking way.
pub trait Format: private::Sealed {
    /// Writes `null` to the writer.
    fn write_null<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"null")
    }

    /// Writes a boolean value to the writer.
    fn write_bool<W>(&mut self, writer: &mut W, value: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let s = if value {
            b"true" as &[u8]
        } else {
            b"false" as &[u8]
        };
        writer.write_all(s)
    }

    /// Writes an integer value to the writer.
    fn write_int<W, I>(&mut self, writer: &mut W, value: I) -> io::Result<()>
    where
        W: ?Sized + io::Write,
        I: itoa::Integer,
    {
        let mut buffer = itoa::Buffer::new();
        let s = buffer.format(value);
        writer.write_all(s.as_bytes())
    }

    /// Writes a float value to the writer.
    fn write_float<W, F>(&mut self, writer: &mut W, value: F) -> io::Result<()>
    where
        W: ?Sized + io::Write,
        F: ryu::Float,
    {
        let mut buffer = ryu::Buffer::new();
        let s = buffer.format_finite(value);
        writer.write_all(s.as_bytes())
    }

    /// Writes a quoted string to the writer. The quoted string will be escaped.
    fn write_quoted_string<W>(&mut self, writer: &mut W, s: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"\"")?;
        self.write_escaped_string(writer, s)?;
        writer.write_all(b"\"")
    }

    /// Writes a string fragment to the writer. No escaping occurs.
    fn write_string_fragment<W>(&mut self, writer: &mut W, s: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(s.as_bytes())
    }

    /// Writes an identifier to the writer. Ensures that `ident` is valid according to the [Unicode
    /// Standard Annex #31][unicode-standard] before writing it to the writer.
    ///
    /// [unicode-standard]: http://www.unicode.org/reports/tr31/
    fn write_ident<W>(&mut self, writer: &mut W, ident: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        if ident.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "identifiers must not be empty",
            ));
        }

        let mut chars = ident.chars();
        let first = chars.next().unwrap();

        if !is_xid_start(first) || !chars.all(is_xid_continue) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid identifier",
            ));
        }

        self.write_string_fragment(writer, ident)
    }

    /// Writes a string to the writer and escapes control characters and quotes that might be
    /// contained in it.
    fn write_escaped_string<W>(&mut self, writer: &mut W, value: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let bytes = value.as_bytes();

        let mut start = 0;

        for (i, &byte) in bytes.iter().enumerate() {
            let escape = ESCAPE[byte as usize];
            if escape == 0 {
                continue;
            }

            if start < i {
                self.write_string_fragment(writer, &value[start..i])?;
            }

            let char_escape = CharEscape::from_escape_table(escape, byte);
            char_escape.write_escaped(writer)?;

            start = i + 1;
        }

        if start != bytes.len() {
            self.write_string_fragment(writer, &value[start..])?;
        }

        Ok(())
    }

    /// Starts an interpolated string.
    fn begin_interpolated_string<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"\"${")
    }

    /// Ends an interpolated string.
    fn end_interpolated_string<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"}\"")
    }

    /// Signals the start of an array to the formatter.
    fn begin_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an array value to the formatter.
    fn begin_array_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the end of an array value to the formatter.
    fn end_array_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the end of an array to the formatter.
    fn end_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an object to the formatter.
    fn begin_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an object key to the formatter.
    fn begin_object_key<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an object value to the formatter.
    fn begin_object_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b" = ")
    }

    /// Signals the end of an object value to the formatter.
    fn end_object_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.end_array_value(writer)
    }

    /// Signals the end of an object to the formatter.
    fn end_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an attribute to the formatter.
    fn begin_attribute<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of an attribute value to the formatter.
    fn begin_attribute_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b" = ")
    }

    /// Signals the end of an attribute to the formatter.
    fn end_attribute<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of a block to the formatter.
    fn begin_block<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the start of a block body to the formatter.
    fn begin_block_body<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;

    /// Signals the end of a block to the formatter.
    fn end_block<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write;
}

#[derive(PartialEq)]
enum FormatState {
    Initial,
    AttributeStart,
    AttributeEnd,
    BlockStart,
    BlockEnd,
    BlockBodyStart,
}

/// Used during pretty printing to delimit how much or little newlines are used
#[derive(PartialEq)]
pub enum FormatDensity {
    /// Blocks are separated by a newline character
    Normal,
    /// Blocks are not separated by a newline character
    Dense,
}

/// A pretty printing HCL formatter.
///
/// ## Example
///
/// The `.builder()` method can be used to construct a `PrettyFormatter` for use with a
/// [`Serializer`][Serializer]:
///
/// ```
/// use hcl::ser::{PrettyFormatter, Serializer};
/// # let mut writer = Vec::new();
///
/// let formatter = PrettyFormatter::builder()
///     .indent(b"  ")
///     .dense(false)
///     .build();
///
/// let ser = Serializer::with_formatter(&mut writer, formatter);
/// ```
///
/// [Serializer]: ser/struct.Serializer.html
pub struct PrettyFormatter<'a> {
    state: FormatState,
    first_element: bool,
    current_indent: usize,
    has_value: bool,
    indent: &'a [u8],
    density: FormatDensity,
}

impl<'a> Default for PrettyFormatter<'a> {
    fn default() -> Self {
        PrettyFormatter::builder().build()
    }
}

/// A builder to create a `PrettyFormatter`.
///
/// See the documentation of [`PrettyFormatter`] for a usage example.
pub struct PrettyFormatterBuilder<'a> {
    indent: &'a [u8],
    density: FormatDensity,
}

impl<'a> PrettyFormatterBuilder<'a> {
    /// Set the indent for indenting nested HCL structures.
    pub fn indent(mut self, indent: &'a [u8]) -> Self {
        self.indent = indent;
        self
    }

    #[deprecated(since="0.7.0", note="please use `PrettyFormatterBuilder::density` instead")]
    /// If set, blocks are not visually separated by empty lines from attributes and adjacent
    /// blocks.
    pub fn dense(self, yes: bool) -> Self {
        self.density(if yes { FormatDensity::Dense } else { FormatDensity::Normal })
    }

    /// If set, separation between adjacent blocks and fields can be reduced
    pub fn density(mut self, density: FormatDensity) -> Self {
        self.density = density;
        self
    }

    /// Consumes the `PrettyFormatterBuilder` and turns it into a `PrettyFormatter`.
    pub fn build(self) -> PrettyFormatter<'a> {
        PrettyFormatter {
            state: FormatState::Initial,
            first_element: false,
            current_indent: 0,
            has_value: false,
            indent: self.indent,
            density: self.density,
        }
    }
}

impl<'a> PrettyFormatter<'a> {
    /// Creates a new [`PrettyFormatterBuilder`] to start building a new `PrettyFormatter`.
    pub fn builder() -> PrettyFormatterBuilder<'a> {
        PrettyFormatterBuilder {
            indent: b"  ",
            density: FormatDensity::Normal,
        }
    }
}

impl<'a> private::Sealed for PrettyFormatter<'a> {}

impl<'a> Format for PrettyFormatter<'a> {
    fn begin_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent += 1;
        self.has_value = false;
        self.first_element = true;
        writer.write_all(b"[")
    }

    fn begin_array_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        if self.first_element {
            self.first_element = false;
            writer.write_all(b"\n")?;
        } else {
            writer.write_all(b",\n")?;
        }

        indent(writer, self.current_indent, self.indent)
    }

    fn end_array_value<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.has_value = true;
        Ok(())
    }

    fn end_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent -= 1;

        if self.has_value {
            writer.write_all(b"\n")?;
            indent(writer, self.current_indent, self.indent)?;
        }

        writer.write_all(b"]")
    }

    fn begin_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent += 1;
        self.has_value = false;
        writer.write_all(b"{")
    }

    fn begin_object_key<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"\n")?;
        indent(writer, self.current_indent, self.indent)
    }

    fn end_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent -= 1;

        if self.has_value {
            writer.write_all(b"\n")?;
            indent(writer, self.current_indent, self.indent)?;
        }

        writer.write_all(b"}")
    }

    fn begin_attribute<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.maybe_write_newline(writer, FormatState::AttributeStart)?;
        indent(writer, self.current_indent, self.indent)
    }

    fn end_attribute<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.state = FormatState::AttributeEnd;
        writer.write_all(b"\n")
    }

    fn begin_block<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.maybe_write_newline(writer, FormatState::BlockStart)?;
        indent(writer, self.current_indent, self.indent)
    }

    fn begin_block_body<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent += 1;
        self.state = FormatState::BlockBodyStart;
        writer.write_all(b" {")
    }

    fn end_block<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.state = FormatState::BlockEnd;
        self.current_indent -= 1;
        indent(writer, self.current_indent, self.indent)?;
        writer.write_all(b"}\n")
    }
}

impl<'a> PrettyFormatter<'a> {
    // Conditionally writes a newline character depending on the formatter configuration and the
    // current and next state. Updates the state to `next_state`.
    fn maybe_write_newline<W>(&mut self, writer: &mut W, next_state: FormatState) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let delimiting_separator: Option<Vec::<u8>> = match (&self.density, &self.state, &next_state) {
            (FormatDensity::Normal, FormatState::AttributeEnd, FormatState::BlockStart) => { Some("\n") },
            (FormatDensity::Normal, FormatState::BlockEnd, FormatState::BlockStart | FormatState::AttributeStart) => { Some("\n") },
            (FormatDensity::Normal | FormatDensity::Dense, FormatState::BlockBodyStart, _) => { Some("\n") },
            (_, _, _) => { None },
        }.map(|i: &str| i.chars().map(|c| c as u8).collect::<Vec<_>>());

        if let Some(delimiting_separator) = delimiting_separator {
            writer.write_all(&delimiting_separator)?;
        }

        self.state = next_state;
        Ok(())
    }
}

fn indent<W>(writer: &mut W, n: usize, s: &[u8]) -> io::Result<()>
where
    W: ?Sized + io::Write,
{
    for _ in 0..n {
        writer.write_all(s)?;
    }

    Ok(())
}
