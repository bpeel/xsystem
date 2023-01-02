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

pub struct XToUnicode<I: Iterator<Item = char>> {
    queued_result: Option<Option<char>>,
    iter: I,
}

impl<I: Iterator<Item = char>> XToUnicode<I> {
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
}

pub struct UnicodeToX<I: Iterator<Item = char>> {
    queued_char: Option<char>,
    iter: I,
}

impl<I: Iterator<Item = char>> UnicodeToX<I> {
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
}

pub fn x_to_unicode(s: &str) -> String {
    XToUnicode::new(s.chars()).collect::<String>()
}

pub fn unicode_to_x(s: &str) -> String {
    UnicodeToX::new(s.chars()).collect::<String>()
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
}
