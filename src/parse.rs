

use nom::*;
use std;
use std::borrow::{Cow};
use ast::{Node, Mod, Attributes};
use std::default::Default;
use nom::whitespace::sp;
use itertools::Itertools;
use regex::{self, Regex};

type Result<'a, T> = IResult<&'a str, T>;

#[derive(Clone, Debug)]
struct Context {
    parent: Option<Node>,
    indent: usize,
}
impl Context {
    fn new(parent: Option<Node>, indent: usize) -> Self {
        Self {
            parent: parent,
            indent: indent,
        }
    }
}
impl Default for Context {
    fn default() -> Self {
        Self {
            parent: None,
            indent: 0,
        }
    }
}

macro_rules! named_ctx (
    ($name:ident($ctx:ident) -> $ret:ty, $submac:ident!( $($args:tt)* )) => (fn $name(input: &str, $ctx: Context) -> Result<$ret> { $submac!(input, $($args)*) })
);

named!(space_sep<&str, &str>, eat_separator!(&b" \t"[..]));

macro_rules! spaced (
  ($i:expr, $($args:tt)*) => (
    {
      sep!($i, space_sep, $($args)*)
    }
  )
);

named!(word_char(&str) -> &str,
    alt_complete!(simple_word_char | recognize!(none_of!(" \t\r\n")))
);

fn simple_word_char(input: &str) -> Result<&str> {
    alt_complete!(input,
        alphanumeric |
        preceded!(tag!("\\"), recognize!(one_of!("-._,*+=(){}!@#$%^&?\'\"~<>|:;"))) |
        value!("\n", tag!("\\n")) |
        value!("\t", tag!("\\t")) //|
//        do_parse!(
//            tag!("\\u") >>
//            code: delimited!(tag!("{"), hex_digit, tag!("}")) >>
//            (&std::char::from_u32(u32::from_str_radix(code, 16).unwrap()).unwrap().to_string())
//        )
    )
}

fn word_char_except<'a>(input: &'a str, excepts: &str) -> IResult<&'a str, &'a str> {
    if tag!(input, excepts).is_done() {
        IResult::Incomplete(Needed::Size(1))
    } else {
        word_char(input)
    }
}

fn word_char_except_one_of<'a>(input: &'a str, excepts: &str) -> IResult<&'a str, &'a str> {
    if one_of!(input, excepts).is_done() {
        IResult::Incomplete(Needed::Size(1))
    } else {
        word_char(input)
    }
}

named!(one_space(&str) -> &str, recognize!(one_of!(" \t")));

named!(spaces(&str) -> &str,
    recognize!(many0!(one_space))
);

named!(one_newline(&str) -> &str, alt!(tag!("\n") | tag!("\r\n")));

named!(newlines(&str) -> &str,
    recognize!(many0!(one_newline))
);

macro_rules! alt_complete_ctx (
    ($i:expr, $ctx:expr, $($arg:tt)|+) => {
        alt_complete!($i, $(apply!($arg, $ctx.clone()))|+)
    }
);

named!(inline_elem_special(&str) -> Node,
    alt_complete!(link | inline_tag | inline_code | strikethrough | bordered | superbold | bolded | italic | underlined)
);

pub fn inline_elem(input: &str) -> Result<Node> {
    alt_complete!(input, simple_word | styled_elem | inline_elem_special | word)
}
pub fn inline_elem_except<'a>(input: &'a str, c: &str) -> IResult<&'a str, Node> {
    alt_complete!(input, simple_word | styled_elem | inline_elem_special | apply!(word_except, c))
}

named!(word_s(&str) -> &str,
    recognize!(delimited!(spaces, many1!(word_char), spaces))
);

named!(simple_word(&str) -> Node,
    do_parse!(
        left_indent: spaces >>
        w: many1!(simple_word_char) >>
        right_indent: spaces >>
        (Node::Text(left_indent.to_string() + &w.into_iter().join("") + right_indent))
    )
);

named!(word(&str) -> Node,
    do_parse!(
        left_indent: spaces >>
        w: many1!(word_char) >>
        right_indent: spaces >>
        (Node::Text(left_indent.to_string() + &w.into_iter().join("") + right_indent))
    )
);

fn word_except<'a>(input: &'a str, c: &str) -> IResult<&'a str, Node> {
    word_except_s(input, c)
        .map(|s: &str| Node::Text(s.to_string()))
}

pub fn word_except_s<'a>(input: &'a str, c: &str) -> IResult<&'a str, &'a str> {
    recognize!(input, delimited!(spaces, many1!(apply!(word_char_except, c)), spaces))
}

pub fn word_except_one_of_s<'a>(input: &'a str, c: &str) -> IResult<&'a str, &'a str> {
    recognize!(input, delimited!(spaces, many1!(apply!(word_char_except_one_of, c)), spaces))
}

pub fn phrase(input: &str) -> Result<Node> {
    map!(input,
        many1!(inline_elem),
        |ns| Node::Span(ns)
    )
}

pub fn phrase_except<'a>(input: &'a str, c: &str) -> IResult<&'a str, Node> {
    map!(input,
        many1!(apply!(inline_elem_except, c)),
        |ns| Node::Span(ns)
    )
}



macro_rules! wrapped {
    
    ($i:expr, $left:expr, $submac:ident!($($args:tt)*), $right:expr) => ({
        let input = $i;
        let left = $left;
        let right = $right;
        let nestable: bool = $left != $right; // only nestable if using unique left and right.
        
        if !input.trim_left_matches(' ').starts_with(left) {
            return IResult::Incomplete(Needed::Unknown)
        }
        
        let l_idx = match input[0..].find(left) {
            Some(i) => i,
            _ => return IResult::Incomplete(Needed::Unknown)
        };
        
        let post_left = &input[(l_idx+left.len())..];
        let r_idx = if nestable {
            let mut closes = 0; // amt of closed ones.
            match post_left.match_indices(right).find(|&(ri, _)| {
                let middle = &post_left[0 .. (ri + 1)];
                closes += 1;
                middle.matches(left).count() < closes // opens<=closes?
            }) {
                Some((i, _)) => i,
                _ => return IResult::Incomplete(Needed::Unknown)
            }
        } else {
            let pat = Regex::new(&format!("[^\\\\]{}", regex::escape($right))).unwrap();
            match pat.find(post_left) {
                Some(m) => m.start() + 1,
                _ => return IResult::Incomplete(Needed::Unknown)
            }
        } + l_idx + left.len() - 1;

        let inner = $submac!(&input[(l_idx + left.len())..(r_idx + 1)], $($args)*);
        match inner {
            IResult::Done(_, done) => {
                IResult::Done(&input[(r_idx + right.len() + 1)..], done)
            },
            i => i,
        }
    });
    ($i:expr, $left:expr, $submac:ident, $right:expr) => (
        wrapped!($i, $left, call!($submac), $right)
//        do_parse!($i,
//            tag!($left) >>
//            p: apply!(phrase_except, $right) >>
//            tag!($right) >>
//            (p)
//        )
//        delimited!($i, tag!($left), apply!(phrase_except, $right), tag!($right))
    );
}

macro_rules! indented_node {
    ($i:expr, $submac:ident!($($args:tt)*)) => {
        do_parse!($i,
            s: spaces >>
            n: $submac!($($args)*) >>
            (if s.is_empty() { n } else { Node::Indented(Box::new(n)) })
        )
    };
}

named!(bolded(&str) -> Node,
    indented_node!(map!(
        wrapped!("*", phrase, "*"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Bold, Box::new(p)))
    ))
);
named!(underlined(&str) -> Node,
    indented_node!(map!(
        wrapped!("_", phrase, "_"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Underline, Box::new(p)))
    ))
);
named!(italic(&str) -> Node,
    indented_node!(map!(
        wrapped!("/", phrase, "/"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Italic, Box::new(p)))
    ))
);
named!(superbold(&str) -> Node,
    indented_node!(map!(
        wrapped!("**", phrase, "**"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Bold, Box::new(Node::Modded(Mod::Italic, Box::new(p)))))
    ))
);
fn bordered(input: &str) -> Result<Node> {
    map!(input,
        wrapped!("[=", phrase, "=]"),
        |p| Node::Modded(Mod::Border, Box::new(p))
    )
}

named!(inline_code(&str) -> Node,
    indented_node!(map!(
        wrapped!("`", phrase, "`"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Code(false), Box::new(p)))
    ))
);

named!(strikethrough(&str) -> Node,
    indented_node!(map!(
        wrapped!("~~", phrase, "~~"),
        |p: Node| p.map_inner(|p| Node::Modded(Mod::Strikethrough, Box::new(p)))
    ))
);

fn style_list(input: &str) -> Result<Vec<(String, String)>> {
    separated_nonempty_list!(input,
        tag!(","),
        map!(
            separated_pair!(take_until!("="), tag!("="), apply!(word_except_one_of_s, "},")),
            |(a, b): (&str, &str)| (a.trim().to_string(), b.trim().to_string())
        )
    )
}

named!(style_attrs(&str) -> Attributes,
    wrapped!("{", do_parse!(
        ty: opt!(take_until!(":")) >> spaces >>
        tag!(":") >> spaces >>
        s: style_list >>
        (Attributes::new(ty.map(|s| s.to_string()), s))
    ), "}")
);

/// Remove?
/// Styled *span*, so starting a line, *not* wrapped in a paragraph.
named!(styled_span(&str) -> Node,
    do_parse!(
        front: wrapped!("[", statement, "]") >>
        sp >>
        back: separated_list!(sp, style_attrs) >>
        (Node::WithAttributes(Box::new(front), back, false))
    )
);

named!(inline_tag(&str) -> Node,
    map!(
        do_parse!(
            tag!("!") >> spaces >>
            front: wrapped!("[", do_parse!(
                tag: recognize!(simple_word) >>
                content: many0!(inline_elem) >>
                (tag, Node::Span(content))
            ), "]") >>
            (front.0, front.1)
        ),
        |(tag, contents): (&str, Node)| {
            Node::SimpleTag(tag.to_string(), Box::new(contents))
        }
    )
);

/// Styled *element*, so only inline, wrapped in a paragraph or some other root span/statement.
fn styled_elem(input: &str) -> Result<Node> {
    do_parse!(input,
        front: alt_complete!(inline_elem_special | wrapped!("[", span, "]")) >>
        back: separated_list!(sp, style_attrs) >>
        (front, back)
    ).map(|(front, back)|
        if !back.is_empty() {
            Node::WithAttributes(Box::new(front), back, false)
        } else {
            front
        })
}

fn link(input: &str) -> Result<Node> {
    do_parse!(input,
        prefix: opt!(preceded!(tag!("!"), opt!(recognize!(simple_word)))) >>
        front: wrapped!("[", call!(span), "]") >> spaces >>
        back: wrapped!("(", delimited!(sp, word_s, sp), ")") >>
        (prefix, front, back)
    ).map(|(prefix, front, back)| match prefix {
        Some(Some("img")) => Node::Image(Box::new(front), back.to_string()),
        Some(_) => Node::Image(Box::new(front), back.to_string()),
        None => Node::Link(Box::new(front), back.to_string()),
    })
}

named!(newline_indented(&str) -> &str,
    recognize!(do_parse!(
        one_newline >>
        spaces >>
        ()
    ))
);

fn empty_line(input: &str) -> Result<Node> {
    match input.find('\n') {
        Some(rn) if input[0..(rn+1)].trim_left() == "" => {
            IResult::Done(&input[rn..], Node::Placeholder)
        },
        _ => IResult::Incomplete(Needed::Unknown)
    }
}

named!(paragraph(&str) -> Node,
    map!(
        separated_nonempty_list!(one_newline, span),
        |ns: Vec<Node>| Node::Paragraph(ns)
    )
);

named!(pub header(&str) -> Node,
    do_parse!(
        spaces >>
        hashes: many1!(tag!("#")) >>
        spaces >>
        text: alt_complete!(spaced!(terminated!(apply!(phrase_except, "#"), many1!(tag!("#")))) | phrase) >> // TODO: should be a span.
        (Node::Header(Box::new(text), hashes.len()))
    )
);

named!(blockquote_line(&str) -> Node,
    map!(
        spaced!(preceded!(tag!(">"), statement)),
        |n: Node| Node::Line(Box::new(n))
    )
);

named!(pub blockquote(&str) -> Node,
    map!(
        separated_nonempty_list!(newline_indented, blockquote_line),
        |ns: Vec<Node>| Node::Blockquote(Box::new(Node::Span(ns)))
    )
);

named!(pub var_decl(&str) -> Node,
    map!(
        do_parse!(
            spaces >>
            name: recognize!(preceded!(tag!("@"), word_s)) >>
            spaces >>
            tag!("=") >>
            spaces >>
            value: recognize!(many1!(not_line_ending)) >>
            (name, value)
        ),
        |(name, value): (&str, &str)| Node::VarDecl(name.to_string(), value.to_string())
    )
);

fn inner_list(input: &str, ctx: Context) -> Result<Node> {
    map!(input,
        separated_nonempty_list!(one_newline, apply!(list_item, ctx.clone())),
        |ns: Vec<(Node, bool)>| {
            let ordered = ns.iter().any(|&(_, ordered)| ordered);
            let ns = ns.into_iter().map(|(n, _)| n).collect();
            if ordered {
                Node::SimpleTag(format!("ol"), Box::new(Node::Span(ns)))
            } else {
                Node::SimpleTag(format!("ul"), Box::new(Node::Span(ns)))
            }
        }
    )
}

fn one_letter(input: &str) -> Result<&str> {
    if !input.is_empty() && is_alphabetic(input.as_bytes()[0]) {
        IResult::Done(&input[1..], &input[0..1])
    } else {
        IResult::Incomplete(Needed::Size(1))
    }
}

named!(unordered_marker(&str) -> bool, map!(one_of!("*-"), |_| false));
named!(list_marker(&str) -> bool,
    alt_complete!(
        map!(terminated!(one_letter, tag!(".")), |_| true) |
        map!(terminated!(digit, tag!(".")), |_| true) |
        unordered_marker
    )
);

fn list_item(input: &str, ctx: Context) -> Result<(Node, bool)> { // (node, ordered?)
    let (rem, indent) = try_parse!(input, spaces);
    let (rem, ordered) = try_parse!(rem, do_parse!(
        m: list_marker >>
        space >> (m))
    );
    let inside_list = ctx.parent.as_ref().map(|p| match p { &Node::List(..) => true, _ => false }).unwrap_or(false);
    if !inside_list || indent.len() > ctx.indent {
        return inner_list(input, Context::new(Some(Node::List(Vec::new(), false)), indent.len())).map(|n| (n, false));
    }
    
    let (rem, n) = try_parse!(rem, span);
    
    IResult::Done(rem, (Node::SimpleTag(format!("li"), Box::new(n)), ordered))
}

pub fn list(input: &str) -> Result<Node> {
    map!(input,
        apply!(list_item, Context::default()),
        |(n, _)| n
    )
}

// Full line element *inside* a paragraph
pub fn span(input: &str) -> Result<Node> {
    alt_complete!(input, list | header | blockquote | phrase)
}

named!(pub statement(&str) -> Node,
    alt_complete!(var_decl | header | list | blockquote | paragraph | empty_line)
);

named!(pub document(&str) -> Node,
    map!(
        do_parse!(
            sp >>
            stmts: separated_list!(newlines, statement) >>
            sp >>
            (stmts)
        ),
        |p: Vec<Node>| Node::Article(p)
    )
);


// inline_element = self-contained entity that can be nested alongside other inline_elements.
//      - word
//      - quotes, bold, italics, inline code
//      - issue: bolding in the middle of words??
// phrase = continuous list of inline_elements on 1 line or within a paragraph.
// span = element that consumes the rest of the line.
// statement = span that can only exist when starting a line, can't be nested.
//      - paragraphs, generally
//      - headers?
//      - lists
//      - code blocks

/// Instead of just duplicating, we should use different syntax elements for different things
/// Header:
///     #### It was dark...
///
/// Section:
///     Stuff
///     =========
///
/// Section + Header (Beginning of chapter maybe)
///     # Chapter 7
///     ============
///
/// Equivalent syntax:
///     # Chapter 8
///     ------------
///


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn words() {
        let ctx = Context::default();
        assert_eq!(Node::Text("hello".to_owned()),
                    word("hello", ctx.clone()).unwrap().1);
        assert_eq!(Node::Text("my-name-is-hyphenated".to_owned()),
                    word("my-name-is-hyphenated", ctx.clone()).unwrap().1);
        assert_eq!(Node::Text("got.dots".to_owned()),
                    word("got.dots", ctx.clone()).unwrap().1);
    }
    
    #[test]
    fn phrases() {
        let s = " hello world migo ";
        let ctx = Context::default();
        assert_eq!("", phrase(s, ctx).unwrap().0);
    }
    
    #[test]
    fn headers_work() {
        let s = "#  Im a header";
        assert_eq!(
            Node::Header(Box::new(Node::Text("Im a header".to_string())), 1),
            header(s).unwrap().1
        );
    }
    
    #[test]
    fn phrases_consume() {
        let ctx = Context::default();
        assert_eq!(
            "",
            phrase("Hi my name is \"Devon\"", ctx).unwrap().0
        );
    }
}
