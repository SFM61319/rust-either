//! The trait [`ApplyEither`] provides methods for conditionally applying methods
//! on a type `Self`, whose size is constant and known at compile-time.

use super::{Either, IntoEither};

/// Provides methods for conditionally applying methods on a type `Self`.
///
/// The [`apply_either`](ApplyEither::apply_either) method takes a [`bool`] to
/// determine whether to apply `f` or `g` on `self`.
///
/// The [`apply_if`](ApplyEither::apply_if) method takes a [`bool`] to determine
/// whether to apply `f` on `self` or not.
pub trait ApplyEither: Sized {
    /// Applies `f` on `self` if `condition` is `true`.
    /// Applies `g` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use either::ApplyEither;
    ///
    /// fn get_pairs(bytes: &[u8], overlap: bool) -> Vec<(u8, u8)> {
    ///     bytes
    ///         .apply_either(overlap, |bytes| bytes.windows(2), |bytes| bytes.chunks(2))
    ///         .map(|w| (w[0], w[1]))
    ///         .collect()
    /// }
    ///
    /// assert_eq!(get_pairs(b"abcd", false), vec![(b'a', b'b'), (b'c', b'd')]);
    /// assert_eq!(
    ///     get_pairs(b"abcd", true),
    ///     vec![(b'a', b'b'), (b'b', b'c'), (b'c', b'd')]
    /// );
    /// ```
    ///
    /// is the same as doing:
    ///
    /// ```
    /// fn get_pairs(bytes: &[u8], overlap: bool) -> Vec<(u8, u8)> {
    ///     if overlap {
    ///         bytes
    ///             .windows(2)
    ///             .map(|w| (w[0], w[1]))
    ///             .collect()
    ///     } else {
    ///         bytes
    ///             .chunks(2)
    ///             .map(|w| (w[0], w[1]))
    ///             .collect()
    ///     }
    /// }
    ///
    /// assert_eq!(get_pairs(b"abcd", false), vec![(b'a', b'b'), (b'c', b'd')]);
    /// assert_eq!(
    ///     get_pairs(b"abcd", true),
    ///     vec![(b'a', b'b'), (b'b', b'c'), (b'c', b'd')]
    /// );
    /// ```
    fn apply_either<L, R, F, G>(self, condition: bool, f: F, g: G) -> Either<L, R>
    where
        F: FnOnce(Self) -> L,
        G: FnOnce(Self) -> R,
    {
        self.into_either(condition).map_either(f, g)
    }

    /// Applies `f` on `self` if and only if `condition` is `true`.
    /// Does nothing otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use either::ApplyEither;
    ///
    /// fn u8_to_bools(value: u8, rtl: bool) -> [bool; 8] {
    ///     let mut result = [false; 8];
    ///     result
    ///         .iter_mut()
    ///         .apply_if(rtl, Iterator::rev)
    ///         .enumerate()
    ///         .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///
    ///     result
    /// }
    ///
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, false),
    ///     [true, false, true, true, false, true, false, false]
    /// );
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, true),
    ///     [false, false, true, false, true, true, false, true]
    /// );
    /// ```
    ///
    /// is the same as doing:
    ///
    /// ```
    /// fn u8_to_bools(value: u8, rtl: bool) -> [bool; 8] {
    ///     let mut result = [false; 8];
    ///     if rtl {
    ///         result
    ///             .iter_mut()
    ///             .rev()
    ///             .enumerate()
    ///             .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///     } else {
    ///         result
    ///             .iter_mut()
    ///             .enumerate()
    ///             .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///     }
    ///
    ///     result
    /// }
    ///
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, false),
    ///     [true, false, true, true, false, true, false, false]
    /// );
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, true),
    ///     [false, false, true, false, true, true, false, true]
    /// );
    /// ```
    fn apply_if<T, F>(self, condition: bool, f: F) -> Either<T, Self>
    where
        F: FnOnce(Self) -> T,
    {
        self.into_either(condition).map_left(f)
    }
}

impl<T> ApplyEither for T {}
