A micro-crate for getting the next char in a string slice.

```rust
use utf8next::{
    NonEmtpyStr,
    next_char_with_len,
}
if let Some(non_empty) = NonEmptyStr::new("¢") {
    let (chr, chr_len) = next_char_with_len(non_emtpy);
    assert_eq!(chr, '¢');
    assert_eq!(chr_len, 2);
} else {
    panic!("String was empty.");
}
```