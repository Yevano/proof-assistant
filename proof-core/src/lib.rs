#![feature(box_patterns)]
#![feature(result_flattening)]
#![allow(clippy::needless_borrow)]
#![feature(let_chains)]

#[macro_use]
pub mod result;
pub mod eval;
pub mod expr;
pub mod goals;
pub mod parse;
pub mod scope;
pub mod types;
