

#![feature(closure_to_fn_coercion)]
#![feature(conservative_impl_trait)]
#![feature(box_syntax)]
#![feature(specialization)]
#![feature(placement_in_syntax)]

extern crate itertools;

#[macro_use]
extern crate nom;

extern crate serde;

#[macro_use]
extern crate serde_derive;

extern crate serde_json;
extern crate serde_yaml;



//mod ast;
//mod grammar;
//mod parse;
pub mod book;
//mod ast_new;
pub mod ast_pull;