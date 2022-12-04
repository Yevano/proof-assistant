#![allow(clippy::needless_borrow)] // allowed because there seems to be a bug in clippy which produces false positives

#![feature(box_patterns)]
#![feature(result_flattening)]
#![feature(let_chains)]
#![feature(arbitrary_self_types)]

#[macro_use]
pub mod result;
pub mod eval;
pub mod expr;
pub mod goals;
pub mod parse;
pub mod scope;
pub mod types;
