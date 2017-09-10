// #![cfg_attr(any(nightly, feature = "nightly"), feature(specialization))]
// #[macro_use]
// extern crate cfg_if;

use std::borrow::Cow;
use std::ffi::{CStr, CString};
use std::result;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct NulError<T> {
    inner: T,
    pos: usize,
}

impl<T> NulError<T> {
    pub fn nul_position(&self) -> usize {
        self.pos
    }

    pub fn into_inner(self) -> T {
        self.inner
    }
}

type Result<T, S> = result::Result<T, NulError<S>>;

pub trait CStrArgument: Sized {
    type Output: AsRef<CStr>;

    fn into_cstr(self) -> Result<Self::Output, Self>;
}

// BUG in rustc (#23341)
// cfg_if! {
//     if #[cfg(any(nightly, feature = "nightly"))] {
//         impl<T> CStrArgument for T where Self: AsRef<CStr> {
//             default type Output = Self;
//
//             default fn into_cstr(self) -> Result<Self, Self> {
//                 Ok(self)
//             }
//         }
//     } else {
impl<'a> CStrArgument for CString {
    type Output = Self;

    fn into_cstr(self) -> Result<Self, Self> {
        Ok(self)
    }
}

impl<'a> CStrArgument for &'a CString {
    type Output = &'a CStr;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        Ok(self)
    }
}

impl<'a> CStrArgument for &'a CStr {
    type Output = Self;

    fn into_cstr(self) -> Result<Self, Self> {
        Ok(self)
    }
}
// }
// }

impl CStrArgument for String {
    type Output = CString;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        unsafe {
            self.into_bytes().into_cstr().map_err(|e| {
                NulError {
                    inner: String::from_utf8_unchecked(e.inner),
                    pos: e.pos,
                }
            })
        }
    }
}

impl<'a> CStrArgument for &'a String {
    type Output = Cow<'a, CStr>;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        self.as_bytes().into_cstr().map_err(|e| {
            NulError {
                inner: self,
                pos: e.pos,
            }
        })
    }
}

impl<'a> CStrArgument for &'a str {
    type Output = Cow<'a, CStr>;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        self.as_bytes().into_cstr().map_err(|e| {
            NulError {
                inner: self,
                pos: e.pos,
            }
        })
    }
}

impl<'a> CStrArgument for Vec<u8> {
    type Output = CString;

    fn into_cstr(mut self) -> Result<Self::Output, Self> {
        unsafe {
            match self.iter().position(|&x| x == 0) {
                Some(n) if n == (self.len() - 1) => {
                    self.pop();
                    Ok(CString::from_vec_unchecked(self))
                }
                Some(n) => Err(NulError {
                    inner: self,
                    pos: n,
                }),
                None => Ok(CString::from_vec_unchecked(self)),
            }
        }
    }
}

impl<'a> CStrArgument for &'a Vec<u8> {
    type Output = Cow<'a, CStr>;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        self.as_slice().into_cstr().map_err(|e| {
            NulError {
                inner: self,
                pos: e.pos,
            }
        })
    }
}

impl<'a> CStrArgument for &'a [u8] {
    type Output = Cow<'a, CStr>;

    fn into_cstr(self) -> Result<Self::Output, Self> {
        unsafe {
            match self.iter().position(|&x| x == 0) {
                Some(n) if n == (self.len() - 1) => Ok(Cow::Borrowed(
                    CStr::from_bytes_with_nul_unchecked(&self[..]),
                )),
                Some(n) => Err(NulError {
                    inner: self,
                    pos: n,
                }),
                None => Ok(Cow::Owned(CString::from_vec_unchecked(self.into()))),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{CStrArgument, NulError};

    fn test<T, F, R>(t: T, f: F) -> R
    where T: CStrArgument, F: FnOnce(Result<T::Output, NulError<T>>) -> R {
        f(t.into_cstr())
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
        let case = "\0\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());

        let case = "hello\0world";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());
    }

    #[test]
    fn test_interior_and_terminating_null() {
        let case = "hello\0world\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());

        let case = "hello world\0\0";
        test(case, |s| s.unwrap_err());
        test(case.to_owned(), |s| s.unwrap_err());
        test(case.as_bytes(), |s| s.unwrap_err());
    }
}
