
use std::borrow::{Cow};
use std::borrow::Cow::*;
use super::node::{Node, Context, Parse};
use super::inline::{Phrase};
use nom::{self, IResult, space};
use std::fmt::{self, Write};

named!(pub one_newline(&str) -> &str, alt!(tag!("\n") | tag!("\r\n")));

fn word_char(input: &str) -> IResult<&str, &str> {
    alt_complete!(input,
        recognize!(none_of!(" \t\r\n\\")) |
        preceded!(tag!("\\"), recognize!(one_of!("-._,*+=(){}!@#$%^&?\'\"~<>|:;"))) |
        value!("\n", tag!("\\n")) |
        value!("\t", tag!("\\t"))
    )
}

pub struct Text<'a>(Vec<&'a str>);
impl<'a> Node for Text<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        for s in &self.0 {
            write!(out, "{}", s)?;
        }
        Ok(())
    }
}
impl<'a> Parse<'a> for Text<'a> {
    fn parse(input: &'a str) -> nom::IResult<&'a str, Self> {
        do_parse!(input,
            l_indent: space >>
            words: many1!(word_char) >>
            r_indent: space >>
            (l_indent, words, r_indent)
        ).map(|(l, mut words, r)| {
            let mut v = Vec::with_capacity(words.len() + 2);
            v.push(l);
            v.append(&mut words);
            v.push(r);
            Text(v)
        })
    }
}

