
use std::fmt::{self, Write};

use nom::{self, IResult};

use super::text::{Text};
use super::node::*;

pub struct InlineElement<'a>(Box<Node+'a>);
impl<'a> Node for InlineElement<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        Ok(())
    }
}
impl<'a> Parse<'a> for InlineElement<'a> {
    fn parse(input: &'a str) -> nom::IResult<&'a str, Self> {
        map!(input,
            Text::parse,
            |t| InlineElement((box t) as Box<Node>)
        )
    }
}

pub struct Phrase<'a>(Vec<InlineElement<'a>>);
impl<'a> Node for Phrase<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        for n in &self.0 {
            n.html_with_context(out, &mut ctx.clone().drop_attrs())?;
        }
        Ok(())
    }
}
impl<'a> Parse<'a> for Phrase<'a> {
    fn parse(input: &'a str) -> IResult<&'a str, Self> {
        let (rem, txt) = try_parse!(input, many1!(InlineElement::parse));
        IResult::Done(rem, Phrase(txt))
    }
}

