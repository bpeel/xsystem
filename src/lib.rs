// Copyright 2023 Neil Roberts
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! Conversion between the Esperanto x-system and Unicode
//! circumflexes.
//!
//! Provides a couple of utilites to convert between the Esperanto
//! x-system (like “ehxosxangxocxiujxauxde”) and Unicode characters
//! with circumflexes (like “eĥoŝanĝoĉiuĵaŭde”). When converting from
//! the x-system, the X can be either a capital X or a lower-case x
//! regardless of the case of the previous character. When converting
//! to the X system the X will match the case of the Esperanto letter.
//!
//! The simplest way to use the Crate is with the functions
//! [x_to_unicode] and [unicode_to_x]. These convert a string slice
//! with one coding system to a String with the other. For example:
//!
//! ```
//! use xsystem::{unicode_to_x, x_to_unicode};
//!
//! let unichars = x_to_unicode("acxajxo SxANGXEMA");
//! assert_eq!(unichars, "aĉaĵo ŜANĜEMA".to_string());
//!
//! let xchars = unicode_to_x("terpomkaĉo estas AĈA");
//! assert_eq!(xchars, "terpomkacxo estas ACXA".to_string());
//! ```
//!
//! You can also use the functions [x_chars] and [unicode_chars] which
//! adapt a char iterator to perform the conversion on the fly. For example:
//!
//! ```
//! use xsystem::{x_chars, unicode_chars};
//!
//! let shouty_x = x_chars("li estas ĉarma".chars())
//!     .map(|c| c.to_uppercase())
//!     .flatten()
//!     .collect::<String>();
//! assert_eq!(&shouty_x, "LI ESTAS CXARMA");
//!
//! let first_converted_char = unicode_chars("mi portas cxapelon".chars())
//!     .position(|c| !c.is_ascii());
//! assert_eq!(first_converted_char, Some(10));
//! ```

// This is sorted by unicode value so we can do a binary chop
static HATABLE_CHARS: [(char, char); 12] = [
    ('C', 'Ĉ'),
    ('G', 'Ĝ'),
    ('H', 'Ĥ'),
    ('J', 'Ĵ'),
    ('S', 'Ŝ'),
    ('U', 'Ŭ'),
    ('c', 'ĉ'),
    ('g', 'ĝ'),
    ('h', 'ĥ'),
    ('j', 'ĵ'),
    ('s', 'ŝ'),
    ('u', 'ŭ'),
];

// This is sorted by unicode value so we can do a binary chop
static UNHATABLE_CHARS: [(char, char); 12] = [
    ('Ĉ', 'C'),
    ('ĉ', 'c'),
    ('Ĝ', 'G'),
    ('ĝ', 'g'),
    ('Ĥ', 'H'),
    ('ĥ', 'h'),
    ('Ĵ', 'J'),
    ('ĵ', 'j'),
    ('Ŝ', 'S'),
    ('ŝ', 's'),
    ('Ŭ', 'U'),
    ('ŭ', 'u'),
];

/// An iterator adapter that returns the Unicode characters
/// corresponding to the characters in the X-system from source
/// iterator.
///
/// This `struct` is created by the [unicode_chars] function. See its
/// documentation for more details.
pub struct XToUnicode<I: Iterator<Item = char>> {
    queued_result: Option<Option<char>>,
    iter: I,
}

impl<I: Iterator<Item = char>> XToUnicode<I> {
    /// Constructor to create the iterator.
    ///
    /// You can also use the [unicode_chars] function which is
    /// probably more idiomatic.
    pub fn new(iter: I) -> Self {
        XToUnicode {
            queued_result: None,
            iter,
        }
    }
}

impl<I: Iterator<Item = char>> Iterator for XToUnicode<I> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let next_value = match self.queued_result.take() {
            Some(value) => value,
            None => self.iter.next(),
        };

        match next_value {
            None => None,
            Some(c) => match HATABLE_CHARS.binary_search_by(|x| x.0.cmp(&c)) {
                Err(_) => Some(c),
                Ok(pos) => match self.iter.next() {
                    None => {
                        self.queued_result = Some(None);
                        Some(c)
                    }
                    Some(next_c) if next_c == 'x' || next_c == 'X' => {
                        Some(HATABLE_CHARS[pos].1)
                    }
                    queue_result @ Some(_) => {
                        self.queued_result = Some(queue_result);
                        Some(c)
                    }
                },
            },
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = self.iter.size_hint();

        (
            min / 2 + min % 2,
            match max {
                None => None,
                max @ Some(_) => max,
            },
        )
    }
}

/// An iterator adapter that returns the X-system characters
/// corresponding to the Unicode characters from the source iterator.
///
/// This `struct` is created by the [x_chars] function. See its
/// documentation for more details.
pub struct UnicodeToX<I: Iterator<Item = char>> {
    queued_char: Option<char>,
    iter: I,
}

impl<I: Iterator<Item = char>> UnicodeToX<I> {
    /// Constructor to create the iterator.
    ///
    /// You can also use the [x_chars] function which is probably more
    /// idiomatic.
    pub fn new(iter: I) -> Self {
        UnicodeToX {
            queued_char: None,
            iter,
        }
    }
}

impl<I: Iterator<Item = char>> Iterator for UnicodeToX<I> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        if let res @ Some(_) = self.queued_char.take() {
            return res;
        }

        match self.iter.next() {
            None => None,
            Some(c) => {
                match UNHATABLE_CHARS.binary_search_by(|x| x.0.cmp(&c)) {
                    Err(_) => Some(c),
                    Ok(pos) => {
                        let replacement = UNHATABLE_CHARS[pos].1;

                        self.queued_char =
                            Some(if replacement >= 'a' { 'x' } else { 'X' });

                        Some(replacement)
                    }
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = self.iter.size_hint();

        (
            min,
            match max {
                None => None,
                Some(max) => Some(max.saturating_mul(2)),
            },
        )
    }
}

/// Adapts the character iterator `iter` to return characters with the
/// X-system.
///
/// Returns an iterator that adapts the source iterator so that
/// whenever an Esperanto special character is encountered its ASCII
/// equivalent is returned followed by an X character with the same
/// case as the special character.
///
/// See [unicode_chars] to go in the other direction.
///
/// # Examples
///
/// ```
/// let mut iter = xsystem::x_chars("aĵo".chars());
/// assert_eq!(iter.next(), Some('a'));
/// assert_eq!(iter.next(), Some('j'));
/// assert_eq!(iter.next(), Some('x'));
/// assert_eq!(iter.next(), Some('o'));
/// assert_eq!(iter.next(), None);
/// ```
pub fn x_chars<I: Iterator<Item = char>>(iter: I) -> UnicodeToX<I> {
    UnicodeToX::new(iter)
}

/// Adapts the character iterator `iter` to return Unicode characters
/// instead of the X-system.
///
/// Returns an iterator that adapts the source iterator so that
/// whenever an X is encountered following a letter that can have a
/// hat on it in Esperanto the equivalent Unicode character is
/// returned. The X’s in the source iterator can have either case
/// regardless of the case of the previous letter. Any X’s that aren’t
/// following an esperantisable letter are left alone.
///
/// See [x_chars] to go in the other direction.
///
/// # Examples
///
/// ```
/// let mut iter = xsystem::unicode_chars("ajxo".chars());
/// assert_eq!(iter.next(), Some('a'));
/// assert_eq!(iter.next(), Some('ĵ'));
/// assert_eq!(iter.next(), Some('o'));
/// assert_eq!(iter.next(), None);
/// ```
pub fn unicode_chars<I: Iterator<Item = char>>(iter: I) -> XToUnicode<I> {
    XToUnicode::new(iter)
}

/// Converts a str slice coded with the X-system to a String with
/// Unicode characters.
///
/// Returns a String where all of X’s in the source str slice that
/// follow an esperantisable letter are converted to their Unicode
/// equivalent. The X’s in the source string can have either case
/// regardless of the case of the previous letter. Any X’s that aren’t
/// following an esperantisable letter are left alone.
///
/// See [unicode_to_x] to go in the other direction.
///
/// # Examples
///
/// ```
/// let hats = xsystem::x_to_unicode("ajxo");
/// assert_eq!(hats, "aĵo".to_string());
/// ```
pub fn x_to_unicode(s: &str) -> String {
    unicode_chars(s.chars()).collect::<String>()
}

/// Converts a string slice by replacing all of the Esperanto letters
/// with their equivalent in the X system.
///
/// Returns a String that is a copy of the string slice where any
/// special Esperanto letters are replaced with their equivalent in
/// the X-system. The case of the X will be the same as that of the
/// special letter.
///
/// See [x_chars] to go in the other direction.
///
/// # Examples
///
/// ```
/// let exes = xsystem::unicode_to_x("AĈA spicaĵo");
/// assert_eq!(exes, "ACXA spicajxo".to_string());
/// ```
pub fn unicode_to_x(s: &str) -> String {
    x_chars(s.chars()).collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;

    struct NoCallAfterNoneIter<I: Iterator> {
        had_none: bool,
        iter: I,
    }

    impl<I: Iterator> Iterator for NoCallAfterNoneIter<I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            assert!(!self.had_none);

            match self.iter.next() {
                None => {
                    self.had_none = true;
                    None
                }
                res @ Some(_) => res,
            }
        }
    }

    impl<I: Iterator> NoCallAfterNoneIter<I> {
        fn new(iter: I) -> Self {
            Self {
                had_none: false,
                iter,
            }
        }
    }

    #[test]
    fn test_x_to_unicode() {
        // Lower-case
        assert_eq!(
            x_to_unicode("ehxosxangxocxiujxauxde"),
            "eĥoŝanĝoĉiuĵaŭde".to_string()
        );
        // Upper-case
        assert_eq!(
            x_to_unicode("EHXOSXANGXOCXIUJXAUXDE"),
            "EĤOŜANĜOĈIUĴAŬDE".to_string()
        );
        // Mixed lower-case
        assert_eq!(
            x_to_unicode("ehXosXangXocXiujXauXde"),
            "eĥoŝanĝoĉiuĵaŭde".to_string()
        );
        // Mixed upper-case
        assert_eq!(
            x_to_unicode("EHxOSxANGxOCxIUJxAUxDE"),
            "EĤOŜANĜOĈIUĴAŬDE".to_string()
        );

        // Unchanged characters
        assert_eq!(
            x_to_unicode("ehosangociujaude"),
            "ehosangociujaude".to_string()
        );
        assert_eq!(
            x_to_unicode("EHOSANGOCIUJAUDE"),
            "EHOSANGOCIUJAUDE".to_string()
        );

        // Hat placed on character that got queued
        assert_eq!(x_to_unicode("ccx"), "cĉ".to_string());

        // Conversion at the end of the string
        assert_eq!(x_to_unicode("cxcxcxcx"), "ĉĉĉĉ".to_string());

        // Non-conversion at the end of the string
        assert_eq!(x_to_unicode("pac"), "pac".to_string());

        // Ignored X’s
        assert_eq!(x_to_unicode("MDCCCLXXXVII"), "MDCCCLXXXVII".to_string());

        // Multiple X’s
        assert_eq!(x_to_unicode("CXXU?"), "ĈXU?".to_string());
    }

    #[test]
    fn test_no_call_after_none() {
        let iter = XToUnicode::new(NoCallAfterNoneIter::new("pac".chars()));
        let result = iter.collect::<String>();
        assert_eq!("pac", &result);

        let iter = XToUnicode::new(NoCallAfterNoneIter::new("pacx".chars()));
        let result = iter.collect::<String>();
        assert_eq!("paĉ", &result);

        let iter = XToUnicode::new(NoCallAfterNoneIter::new("zamcxjo".chars()));
        let result = iter.collect::<String>();
        assert_eq!("zamĉjo", &result);
    }

    #[test]
    fn test_unicode_to_x() {
        assert_eq!(
            unicode_to_x("eĥoŝanĝoĉiuĵaŭde"),
            "ehxosxangxocxiujxauxde".to_string()
        );
        assert_eq!(
            unicode_to_x("EĤOŜANĜOĈIUĴAŬDE"),
            "EHXOSXANGXOCXIUJXAUXDE".to_string()
        );
    }

    #[test]
    fn test_size_hint() {
        assert_eq!(
            unicode_chars(['a', 'b'].iter().map(|&c| c)).size_hint(),
            (1, Some(2))
        );
        assert_eq!(
            unicode_chars(['a', 'b', 'c'].iter().map(|&c| c)).size_hint(),
            (2, Some(3))
        );
        assert_eq!(
            unicode_chars(std::iter::repeat('c')).size_hint(),
            (usize::MAX / 2 + 1, None)
        );
        assert_eq!(
            x_chars(['a', 'b'].iter().map(|&c| c)).size_hint(),
            (2, Some(4))
        );
        assert_eq!(
            x_chars(['a', 'b', 'c'].iter().map(|&c| c)).size_hint(),
            (3, Some(6))
        );
        assert_eq!(
            x_chars(std::iter::repeat('c')).size_hint(),
            (usize::MAX, None)
        );
    }
}
