#![allow(clippy::needless_borrow)] // allowed because there seems to be a bug in clippy which produces false positives
#![feature(box_patterns)]
#![feature(result_flattening)]
#![feature(let_chains)]
#![feature(arbitrary_self_types)]
#![feature(iter_intersperse)]
#![feature(result_option_inspect)]

#[macro_use]
pub mod result;
pub mod eval;
pub mod expr;
pub mod goals;
pub mod parse;
pub mod repl;
pub mod scope;
pub mod term_writer;
pub mod term;
pub mod types;