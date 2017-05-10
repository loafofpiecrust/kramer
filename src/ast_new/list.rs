
use std::fmt::{self, Write};
use super::node::*;
use super::{text};
use super::stmt::*;
use nom::{self, IResult};


fn one_letter(input: &str) -> IResult<&str, &str> {
    if !input.is_empty() && nom::is_alphabetic(input.as_bytes()[0]) {
        IResult::Done(&input[1..], &input[0..1])
    } else {
        IResult::Incomplete(nom::Needed::Size(1))
    }
}
named!(unordered_marker(&str) -> bool, map!(one_of!("*-"), |_| false));
named!(list_marker(&str) -> bool,
    alt_complete!(
        map!(terminated!(one_letter, tag!(".")), |_| true) |
        map!(terminated!(nom::digit, tag!(".")), |_| true) |
        unordered_marker
    )
);


pub struct ListItem<'a>(Span<'a>); /// ordered?
impl<'a> Node for ListItem<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        write!(out, "<li {}>", ctx.attrs_html())?;
        self.0.html_with_context(out, &mut ctx.clone().drop_attrs())?;
        write!(out, "</li>")
    }
}
impl<'a> ListItem<'a> {
    fn parse(input: &'a str, prev_indent: usize) -> IResult<&'a str, (Box<Node+'a>, bool)> {
        use nom::space;
        
        let (rem, indent) = try_parse!(input, space);
        let indent = indent.len();
        let (rem, ordered) = try_parse!(rem, do_parse!(
            m: list_marker >>
            space >>
            (m))
        );
        if indent > prev_indent {
            List::inner(input, indent).map(|n| ((box n) as Box<Node>, false))
        } else {
            let (rem, n) = try_parse!(rem, Span::parse);
            IResult::Done(rem, ((box ListItem(n)) as Box<Node>, ordered))
        }
    }
}


pub struct List<'a>(Vec<Box<Node+'a>>, bool); /// ordered?
impl<'a> Node for List<'a> {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result {
        let tag = if self.1 { "ol" } else { "ul" };
        write!(out, "<{} {}>", tag, ctx.attrs_html())?;
        let mut new_ctx = ctx.clone().drop_attrs();
        for n in &self.0 {
            n.html_with_context(out, &mut new_ctx)?;
        }
        write!(out, "</{}>", tag)
    }
}
impl<'a> List<'a> {
    fn inner(input: &'a str, prev_indent: usize) -> IResult<&'a str, List> {
        map!(input,
            separated_nonempty_list!(text::one_newline, apply!(ListItem::parse, prev_indent)),
            |ns: Vec<(Box<Node+'a>, bool)>| {
                let ordered = ns.iter().any(|&(_, o)| o);
                let ns = ns.into_iter().map(|(n, _)| n).collect();
                List(ns, ordered)
            }
        )
    }
    
    pub fn parse(input: &'a str) -> IResult<&'a str, Self> {
        use nom::space;
        
        let (rem, indent) = try_parse!(input, space);
        let indent = indent.len();
        try_parse!(rem, do_parse!(
            m: list_marker >>
            space >>
            ())
        );
        
        List::inner(input, indent)
    }
}
