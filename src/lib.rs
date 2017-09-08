use std::borrow::Cow;
use std::ffi::{CStr, CString};
use std::result;

#[derive(Debug, Copy, Clone)]
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

impl<'a> CStrArgument for String {
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
