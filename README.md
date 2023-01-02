A small Rust library to convert between the Esperanto x-system and
Unicode circumflexes.

Provides a couple of utilites to convert between the Esperanto
x-system (like “ehxosxangxocxiujxauxde”) and Unicode characters
with circumflexes (like “eĥoŝanĝoĉiuĵaŭde”). When converting from
the x-system, the X can be either a capital X or a lower-case x
regardless of the case of the previous character. When converting
to the X system the X will match the case of the Esperanto letter.

To use the Crate, run the following command in your project’s
repository:

```
cargo add xsystem
```

The simplest way to use the Crate is with the functions
`x_to_unicode` and `unicode_to_x`. These convert a string slice
with one coding system to a String with the other. For example:

```rust
use xsystem::{unicode_to_x, x_to_unicode};

let unichars = x_to_unicode("acxajxo SxANGXEMA");
assert_eq!(unichars, "aĉaĵo ŜANĜEMA".to_string());

let xchars = unicode_to_x("terpomkaĉo estas AĈA");
assert_eq!(xchars, "terpomkacxo estas ACXA".to_string());
```

You can also use the functions `x_chars` and `unicode_chars` which
adapt a char iterator to perform the conversion on the fly. For example:

```rust
use xsystem::{x_chars, unicode_chars};

let shouty_x = x_chars("li estas ĉarma".chars())
    .map(|c| c.to_uppercase())
    .flatten()
    .collect::<String>();
assert_eq!(&shouty_x, "LI ESTAS CXARMA");

let first_converted_char = unicode_chars("mi portas cxapelon".chars())
    .position(|c| !c.is_ascii());
assert_eq!(first_converted_char, Some(10));
```
