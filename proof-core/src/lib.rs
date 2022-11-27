#![feature(box_patterns)]
#![feature(result_flattening)]

#[macro_use]
pub mod result;
pub mod eval;
pub mod expr;
pub mod goals;
pub mod parse;
pub mod types;
