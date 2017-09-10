cstr-argument
=============
A trait for converting function arguments to null terminated strings

[![Build Status](https://travis-ci.org/johnschug/cstr-argument.svg?branch=master)](https://travis-ci.org/johnschug/cstr-argument)
[![Version](https://img.shields.io/crates/v/cstr-argument.svg)](https://crates.io/crates/cstr-argument)

[Documentation](https://docs.rs/cstr-argument)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
cstr-argument = "0.0.1"
```

and this to your crate root:

```rust
extern crate cstr_argument;
```

## Example

```rust
use std::os::raw::c_char;
use cstr_argument::CStrArgument;

extern "C" {
  fn foo(s: *const c_char);
}

fn bar<S: CStrArgument>(s: S) {
  let s = s.into_cstr().expect("argument contained interior nulls");
  unsafe {
    foo(s.as_ref().as_ptr())
  }
}

fn baz() {
  bar("hello "); // Argument will be converted to a CString requiring an allocation
  bar("world\0"); // Argument will be converted to a CStr without allocation
  bar("!".to_owned()); // Argument will be converted to a CString possibly requiring an allocation
}
```
