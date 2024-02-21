//! The trait [`IntoEither`] provides methods for converting a type `Self`, whose
//! size is constant and known at compile-time, into an [`Either`] variant.

use super::{Either, Left, Right};

/// Provides methods for converting a type `Self` into either a [`Left`] or [`Right`]
/// variant of [`Either<Self, Self>`](Either).
///
/// The [`into_either`](IntoEither::into_either) method takes a [`bool`] to determine
/// whether to convert to [`Left`] or [`Right`].
///
/// The [`into_left`](IntoEither::into_left) and [`into_right`](IntoEither::into_right)
/// methods directly convert to the respective variant without needing a [`bool`].
pub trait IntoEither: Sized {
    /// Converts `self` into a [`Left`] variant of [`Either<Self, Self>`](Either)
    /// if [`into_left`](IntoEither::into_left) is `true`.
    /// Converts `self` into a [`Right`] variant of [`Either<Self, Self>`](Either)
    /// otherwise.
    fn into_either(self, into_left: bool) -> Either<Self, Self> {
        if into_left {
            self.into_left()
        } else {
            self.into_right()
        }
    }

    /// Converts `self` into a [`Left`] variant of [`Either<Self, Self>`](Either).
    fn into_left(self) -> Either<Self, Self> {
        Left(self)
    }

    /// Converts `self` into a [`Right`] variant of [`Either<Self, Self>`](Either).
    fn into_right(self) -> Either<Self, Self> {
        Right(self)
    }
}

impl<T> IntoEither for T {}
