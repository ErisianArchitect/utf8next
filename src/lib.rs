use core::fmt;
use std::{borrow, ops, slice};


/// A [str] wrapper type that enforces that a string must be non-empty.
/// 
/// # Usage
/// 
/// ```rust, ignore
/// let some_string = "hello, world"
/// // ...
/// if let Some(non_empty) = NonEmptyStr::new(some_string) {
///     let (chr, len) = next_char_with_len(non_empty);
///     assert_eq!(chr, 'h');
///     assert_eq!(len, 1);
/// } else {
///     panic!("String was empty.");
/// }
/// ```
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmptyStr {
    s: str,
}

impl NonEmptyStr {
    /// Create a new [NonEmpty].
    /// 
    /// Returns [None] if `non_empty` is empty.
    #[must_use]
    #[inline(always)]
    pub const fn new(non_empty: &str) -> Option<&Self> {
        if non_empty.is_empty() {
            None
        } else {
            Some(unsafe { ::core::mem::transmute(non_empty) })
        }
    }
    
    /// Create a new [NonEmpty] without a check.
    /// 
    /// # SAFETY:
    /// `non_empty` must be non-empty. It must contain at least one valid utf-8 character.
    #[must_use]
    #[inline(always)]
    pub const unsafe fn new_unchecked(non_empty: &str) -> &Self {
        debug_assert!(!non_empty.is_empty());
        unsafe { ::core::mem::transmute(non_empty) }
    }
    
    /// Returns the inner string value.
    #[must_use]
    #[inline(always)]
    pub const fn as_str(&self) -> &str {
        &self.s
    }
    
    /// See [str::len].
    #[must_use]
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.s.len()
    }
    
    /// See [str::is_char_boundary].
    #[must_use]
    #[inline(always)]
    pub const fn is_char_boundary(&self, index: usize) -> bool {
        self.s.is_char_boundary(index)
    }
    
    /// See [str::floor_char_boundary].
    #[must_use]
    #[inline(always)]
    pub const fn floor_char_boundary(&self, index: usize) -> usize {
        self.s.floor_char_boundary(index)
    }
    
    /// See [str::ceil_char_boundary].
    #[must_use]
    #[inline(always)]
    pub const fn ceil_char_boundary(&self, index: usize) -> usize {
        self.s.ceil_char_boundary(index)
    }
    
    /// See [str::as_bytes].
    #[must_use]
    #[inline(always)]
    pub const fn as_bytes(&self) -> &[u8] {
        self.s.as_bytes()
    }
    
    /// See [str::as_ptr].
    #[must_use]
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const u8 {
        self.s.as_ptr()
    }
    
    #[must_use]
    #[inline]
    pub fn get<I: slice::SliceIndex<str, Output = str>>(&self, index: I) -> Option<&Self> {
        let slice = &self.s[index];
        if slice.is_empty() {
            return None;
        }
        // SAFETY: The slice has already been determined to be non-empty.
        Some(unsafe { NonEmptyStr::new_unchecked(slice) })
    }
    
    /// Resulting slice must be non-empty.
    #[must_use]
    #[inline]
    pub unsafe fn get_unchecked<I: slice::SliceIndex<str, Output = str>>(&self, index: I) -> &Self {
        let slice = &self.s[index];
        debug_assert!(!slice.is_empty());
        // SAFETY: The slice should have already been determined to be non-empty.
        unsafe { NonEmptyStr::new_unchecked(slice) }
    }
    
    /// See [str::is_ascii].
    #[must_use]
    #[inline(always)]
    pub const fn is_ascii(&self) -> bool {
        self.s.is_ascii()
    }
}

impl<I: slice::SliceIndex<str, Output = str>> ops::Index<I> for &NonEmptyStr
where
    str: ops::Index<I, Output = str> {
    type Output = NonEmptyStr;
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        let slice = &self.s[index];
        assert!(!slice.is_empty(), "Slice must be non-empty.");
        // SAFETY: The slice has already been determined to be non-empty.
        unsafe {
            NonEmptyStr::new_unchecked(slice)
        }
    }
}

impl AsRef<str> for NonEmptyStr {
    #[inline]
    fn as_ref(&self) -> &str {
        &self.s
    }
}

impl borrow::Borrow<str> for NonEmptyStr {
    #[inline]
    fn borrow(&self) -> &str {
        &self.s
    }
}

impl ops::Deref for NonEmptyStr {
    type Target = str;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.s
    }
}

impl fmt::Display for NonEmptyStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Returns the next character in the string with the length of the character in bytes.
/// 
/// This version of the function uses `inline(always)` and uses a Marker type to help
/// with inlining.
#[must_use]
#[inline(always)]
pub const fn next_char_with_len_inline(s: &NonEmptyStr) -> (char, usize) {
    // These constants are just meant to help make the match expression below more readable.
    /// Leading ones count for a codepoint that has a length of 1.
    const LEN1: u32 = 0;
    /// Leading ones count for a codepoint that has a length of 2.
    const LEN2: u32 = 2;
    /// Leading ones count for a codepoint that has a length of 3.
    const LEN3: u32 = 3;
    /// Leading ones count for a codepoint that has a length of 4.
    const LEN4: u32 = 4;
    
    let bytes = s.as_str().as_bytes();
    let first = bytes[0];
    match first.leading_ones() {
        // 1 byte
        LEN1 => {
            let codepoint = first & 0b01111111;
            // SAFETY: codepoint is a valid utf-8 codepoint, in accordance with Rust strings being enforced
            // to be valid utf-8.
            let chr = unsafe {
                char::from_u32_unchecked(codepoint as u32)
            };
            (chr, 1)
        }
        // 2 bytes
        LEN2 => {
            let mut codepoint = ((first & 0b00011111) as u32) << 6;
            let second = bytes[1];
            codepoint |= (second & 0b00111111) as u32;
            // SAFETY: codepoint is a valid utf-8 codepoint, in accordance with Rust strings being enforced
            // to be valid utf-8.
            let chr = unsafe {
                char::from_u32_unchecked(codepoint)
            };
            (chr, 2)
        }
        // 3 bytes
        LEN3 => {
            let mut codepoint = ((first & 0b00001111) as u32) << 6;
            let second = bytes[1];
            codepoint = (codepoint | (second & 0b00111111) as u32) << 6;
            let third = bytes[2];
            codepoint = codepoint | (third & 0b00111111) as u32;
            // SAFETY: codepoint is a valid utf-8 codepoint, in accordance with Rust strings being enforced
            // to be valid utf-8.
            let chr = unsafe {
                char::from_u32_unchecked(codepoint)
            };
            (chr, 3)
        }
        // 4 bytes
        LEN4 => {
            let mut codepoint = ((first & 0b00000111) as u32) << 6;
            let second = bytes[1];
            codepoint = (codepoint | (second & 0b00111111) as u32) << 6;
            let third = bytes[2];
            codepoint = (codepoint | (third & 0b00111111) as u32) << 6;
            let fourth = bytes[3];
            codepoint = codepoint | (fourth & 0b00111111) as u32;
            // SAFETY: codepoint is a valid utf-8 codepoint, in accordance with Rust strings being enforced
            // to be valid utf-8.
            let chr = unsafe {
                char::from_u32_unchecked(codepoint)
            };
            (chr, 4)
        }
        // SAFETY: It's UB for a string slice to contain invalid utf-8.
        _ => unsafe { ::std::hint::unreachable_unchecked() },
    }
}

/// Returns the next character in the string with the length of the character in bytes.
#[must_use]
pub const fn next_char_with_len(s: &NonEmptyStr) -> (char, usize) {
    next_char_with_len_inline(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn non_empty_test() {
        if let Some(non_empty) = NonEmptyStr::new("hello, world") {
            let (chr, len) = next_char_with_len(non_empty);
            assert_eq!(non_empty.as_str(), "hello, world");
            assert_eq!(chr, 'h');
            assert_eq!(len, 1);
        } else {
            panic!("Failure.")
        }
    }
}