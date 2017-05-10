
use std::fmt::{self, Write};
use nom;
use nom::*;

use super::node::*;
use super::{text, inline};
use super::list::List;
use super::inline::*;


named!(space_sep<&str, &str>, eat_separator!(&b" \t"[..]));

macro_rules! spaced (
  ($i:expr, $($args:tt)*) => (
    {
      sep!($i, space_sep, $($args)*)
    }
  )
);

pub struct Span<'a>(Box<Node+'a>);
impl<'a> Node for Span<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        self.0.html_with_context(out, ctx)
    }
}
impl<'a> Parse<'a> for Span<'a> {
    fn parse(input: &'a str) -> IResult<&'a str, Self> {
        alt_complete!(input,
            map!(call!(List::parse), |n| Span((box n) as Box<Node>)) |
            map!(call!(Paragraph::parse), |n| Span((box n) as Box<Node>)))
    }
}

pub struct Paragraph<'a>(Vec<inline::Phrase<'a>>);
impl<'a> Node for Paragraph<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        write!(out, "<p {}>", ctx.attrs_html())?;
        for p in &self.0 {
            p.html_with_context(out, &mut ctx.clone().drop_attrs())?;
        }
        write!(out, "</p>")
    }
}
impl<'a> Parse<'a> for Paragraph<'a> {
    fn parse(input: &'a str) -> IResult<&'a str, Self> {
        do_parse!(input,
            txts: separated_nonempty_list!(text::one_newline, inline::Phrase::parse) >>
            (Paragraph(txts))
            //(Paragraph(txts.into_iter().map(|t| (box t) as Box<Node>).collect()))
        )
    }
}


pub struct Header<'a>(usize, inline::Phrase<'a>);
impl<'a> Node for Header<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        unimplemented!()
    }
}
impl<'a> Parse<'a> for Header<'a> {
    fn parse(input: &'a str) -> nom::IResult<&'a str, Self> {
        do_parse!(input,
            opt!(space) >>
            hashes: many1!(tag!("#")) >>
            opt!(space) >>
            text: alt_complete!(spaced!(terminated!(apply!(phrase_except, "#"), many1!(tag!("#")))) | call!(inline::Phrase::parse)) >> // TODO: should be a span.
            (Header(hashes.len(), Box::new(text)))
        )
    }
}

