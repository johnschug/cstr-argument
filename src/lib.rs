//! A trait for converting function arguments to null terminated strings.
#![deny(missing_docs)]
// #![cfg_attr(any(nightly, feature = "nightly"), feature(specialization))]
// #[macro_use]
// extern crate cfg_if;
extern crate memchr;

use std::borrow::Cow;
use std::error;
use std::ffi::{CStr, CString};
use std::fmt;
use std::result;

use memchr::memchr;

/// An error returned from [`CStrArgument::try_into_cstr`] to indicate that a null byte
/// was found before the last byte in the string.
///
/// [`CStrArgument::try_into_cstr`]: trait.CStrArgument.html#tymethod.try_into_cstr
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct NulError<T> {
    inner: T,
    pos: usize,
}

impl<T> NulError<T> {
    /// Returns the position of the null byte in the string.
    #[inline]
    pub fn nul_position(&self) -> usize {
        self.pos
    }

    /// Returns the original string.
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner
    }
}

impl<T> fmt::Display for NulError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "nul byte found before end of provided data at position: {}",
            self.pos
        )
    }
}

impl<T: fmt::Debug> error::Error for NulError<T> {
    fn description(&self) -> &str {
        "nul byte found before end of data"
    }
}

type Result<T, S> = result::Result<T, NulError<S>>;

/// A trait for converting function arguments to null terminated strings. It can be used to convert
/// string arguments that are passed on to C APIs using the minimal amount of allocations.
///
/// Strings that are already null terminated are just wrapped in a CStr without any allocations.
/// Strings that are not already null terminated are converted to a CString possibly requiring one
/// or more allocations. Trying to convert strings with a null byte in any position other than the
/// final will result in an error.
///
/// # Example
///
/// ```no_run
/// use std::os::raw::c_char;
/// use cstr_argument::CStrArgument;
///
/// extern "C" {
///     fn foo(s: *const c_char);
/// }
///
/// fn bar<S: CStrArgument>(s: S) {
///     let s = s.into_cstr();
///     unsafe {
///         foo(s.as_ref().as_ptr())
///     }
/// }
///
/// fn baz() {
///     bar("hello "); // Argument will be converted to a CString requiring an allocation
///     bar("world\0"); // Argument will be converted to a CStr without any allocations
///     bar("!".to_owned()); // Argument will be converted to a CString possibly requiring an
///                          // allocation
/// }
/// ```
pub trait CStrArgument: fmt::Debug + Sized {
    /// The type of the string after conversion. The type may or may not own the resulting string.
    type Output: AsRef<CStr>;

    /// Returns the string with a null terminator or an error.
    ///
    /// # Errors
    ///
    /// This function will return an error if the string contains a null byte at any position
    /// other than the final.
    fn try_into_cstr(self) -> Result<Self::Output, Self>;

    /// Returns the string with a null terminator.
    ///
    /// # Panics
    ///
    /// This function will panic if the string contains a null byte at any position other
    /// than the final. See [`try_into_cstr`](#tymethod.try_into_cstr) for a non-panicking version
    /// of this function.
    fn into_cstr(self) -> Self::Output {
        self.try_into_cstr()
            .expect("string contained an interior null byte")
    }
}

// BUG in rustc (#23341)
// cfg_if! {
//     if #[cfg(any(nightly, feature = "nightly"))] {
//         impl<T> CStrArgument for T where Self: AsRef<CStr> {
//             default type Output = Self;
//
//             default fn try_into_cstr(self) -> Result<Self, Self> {
//                 Ok(self)
//             }
//         }
//
//         impl<'a, T> CStrArgument for &'a T where Self: AsRef<str> {
//             default type Output = Cow<'a, CStr>;
//
//             default fn try_into_cstr(self) -> Result<Self::Output, Self> {
//                 self.as_ref().try_into_cstr()
//             }
//         }
//     } else {
impl<'a> CStrArgument for CString {
    type Output = Self;

    #[inline]
    fn try_into_cstr(self) -> Result<Self, Self> {
        Ok(self)
    }
}

impl<'a> CStrArgument for &'a CString {
    type Output = &'a CStr;

    #[inline]
    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        Ok(self)
    }
}

impl<'a> CStrArgument for &'a CStr {
    type Output = Self;

    #[inline]
    fn try_into_cstr(self) -> Result<Self, Self> {
        Ok(self)
    }
}
// }
// }

impl CStrArgument for String {
    type Output = CString;

    #[inline]
    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        self.into_bytes().try_into_cstr().map_err(|e| NulError {
            inner: unsafe { String::from_utf8_unchecked(e.inner) },
            pos: e.pos,
        })
    }
}

impl<'a> CStrArgument for &'a String {
    type Output = Cow<'a, CStr>;

    #[inline]
    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        self.as_bytes().try_into_cstr().map_err(|e| NulError {
            inner: self,
            pos: e.pos,
        })
    }
}

impl<'a> CStrArgument for &'a str {
    type Output = Cow<'a, CStr>;

    #[inline]
    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        self.as_bytes().try_into_cstr().map_err(|e| NulError {
            inner: self,
            pos: e.pos,
        })
    }
}

impl<'a> CStrArgument for Vec<u8> {
    type Output = CString;

    fn try_into_cstr(mut self) -> Result<Self::Output, Self> {
        match memchr(0, &self) {
            Some(n) if n == (self.len() - 1) => {
                self.pop();
                Ok(unsafe { CString::from_vec_unchecked(self) })
            }
            Some(n) => Err(NulError {
                inner: self,
                pos: n,
            }),
            None => Ok(unsafe { CString::from_vec_unchecked(self) }),
        }
    }
}

impl<'a> CStrArgument for &'a Vec<u8> {
    type Output = Cow<'a, CStr>;

    #[inline]
    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        self.as_slice().try_into_cstr().map_err(|e| NulError {
            inner: self,
            pos: e.pos,
        })
    }
}

impl<'a> CStrArgument for &'a [u8] {
    type Output = Cow<'a, CStr>;

    fn try_into_cstr(self) -> Result<Self::Output, Self> {
        match memchr(0, self) {
            Some(n) if n == (self.len() - 1) => Ok(Cow::Borrowed(unsafe {
                CStr::from_bytes_with_nul_unchecked(self)
            })),
            Some(n) => Err(NulError {
                inner: self,
                pos: n,
            }),
            None => Ok(Cow::Owned(unsafe {
                CString::from_vec_unchecked(self.into())
            })),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{CStrArgument, NulError};

    fn test<T, F, R>(t: T, f: F) -> R
    where
        T: CStrArgument,
        F: FnOnce(Result<T::Output, NulError<T>>) -> R, {
        f(t.try_into_cstr())
    }

    #[test]
    fn test_basic() {
        let case = "";
        test(case, |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
            assert_ne!(s.as_ptr() as *const u8, case.as_ptr());
        });

        test(case.to_owned(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
        });

        test(case.as_bytes(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
            assert_ne!(s.as_ptr() as *const u8, case.as_ptr());
        });

        let case = "hello";
        test(case, |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
            assert_ne!(s.as_ptr() as *const u8, case.as_ptr());
        });

        test(case.to_owned(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
        });

        test(case.as_bytes(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len() + 1);
            assert_ne!(s.as_ptr() as *const u8, case.as_ptr());
        });
    }

    #[test]
    fn test_terminating_null() {
        let case = "\0";
        test(case, |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
            assert_eq!(s.as_ptr() as *const u8, case.as_ptr());
        });

        test(case.to_owned(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
        });

        test(case.as_bytes(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
            assert_eq!(s.as_ptr() as *const u8, case.as_ptr());
        });

        let case = "hello\0";
        test(case, |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
            assert_eq!(s.as_ptr() as *const u8, case.as_ptr());
        });

        test(case.to_owned(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
        });

        test(case.as_bytes(), |s| {
            let s = s.unwrap();
            assert_eq!(s.to_bytes_with_nul().len(), case.len());
            assert_eq!(s.as_ptr() as *const u8, case.as_ptr());
        });
    }

    #[test]
    fn test_interior_null() {
        let case = "hello\0world";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());
    }

    #[test]
    fn test_interior_and_terminating_null() {
        let case = "\0\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());

        let case = "hello\0world\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());

        let case = "hello world\0\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());
    }

    #[test]
    #[should_panic]
    fn test_interior_null_panic() {
        "\0\0".into_cstr();
    }
}
