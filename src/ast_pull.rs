
use nom::*;
use std::borrow::Cow;
use std::collections::{VecDeque, HashMap};
use std::default::{Default};
use std::fmt::{self, Formatter, Display, Write};
use itertools::Itertools;
use serde_yaml;

//pub type Config<'a> = HashMap<&'a str, &'a str>;

#[derive(Debug, Clone)]
pub struct Config<'b> {
    line_break: &'b str,
    //span_cmds: HashMap<&'b str, SpanCmd<'b, 'b>>,
    plugin_cfg: HashMap<&'b str, &'b str>,
}
impl<'b> Default for Config<'b> {
    fn default() -> Self {
        Self {
            line_break: "<br/>",
            //span_cmds: Default::default(),
            plugin_cfg: Default::default(),
        }
    }
}

pub trait FromElem<T> {
    fn from_elem(elem: T) -> Self;
}
impl<T> FromElem<T> for VecDeque<T> {
    fn from_elem(elem: T) -> Self {
        let mut r = Self::with_capacity(1);
        r.push_back(elem);
        r
    }
}
impl<T> FromElem<T> for Vec<T> {
    fn from_elem(elem: T) -> Self {
        vec![elem]
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Tag<'a> {
    Paragraph,
    Section(u32),
    Document,
    Header(u32),
    BlockQuote(usize),
    Bold,
    Italic,
    Highlight,
    Deletion,
    Insertion,
    DefList(u32),
    DefTerm(u32),
    DefDef(u32),
    List(u32, bool),
    ListItem(u32),
    Code(bool), // multiline?
    Checkbox(bool),
    Custom(&'a str),
    Image,
    Link,
    HorizontalRule,
    Nothing,
}

impl<'a> Tag<'a> {
    fn to_html(&self, out: &mut Write, cfg: &Config) -> fmt::Result {
        use self::Tag::*;
        match *self {
            Paragraph => write!(out, "p"),
            Section(..) => write!(out, "section"),
            Document => write!(out, "article"),
            Header(rank) => write!(out, "h{}", rank),
            Bold => write!(out, "strong"),
            Italic => write!(out, "em"),
            Highlight => write!(out, "mark"),
            Deletion => write!(out, "del"),
            Insertion => write!(out, "ins"),
            Link => write!(out, "a"),
            HorizontalRule => write!(out, "hr"),
            DefList(..) => write!(out, "dl"),
            DefTerm(..) => write!(out, "dt"),
            DefDef(..) => write!(out, "dd"),
            List(_, ordered) => write!(out, "{}", if ordered { "ol" } else { "ul" }),
            ListItem(..) => write!(out, "li"),
            Image => write!(out, "img"),
            BlockQuote(..) => write!(out, "blockquote"),
            Code(multiline) => if multiline {
                write!(out, "pre")
            } else {
                write!(out, "code")
            },
            Checkbox(checked) => write!(out, "input type=\"checkbox\" disabled {}", if checked {
                "checked"
            } else { "" }),
            Nothing => Ok(()),
            Custom(ref t) => write!(out, "{}", t),
        }
    }
}

pub enum Variable<'a> {
    Reference(&'a str),
    Named(&'a str, &'a str),
    Value(&'a str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Event<'a> {
    Start(Tag<'a>),
    End(Tag<'a>),
    SelfClosing(Tag<'a>),
    LineBreak,
    Attributes(Option<&'a str>, Vec<(&'a str, Cow<'a, str>)>),
    Text(&'a str),
    String(String),
    Span(Stream<'a>),
    FrontMatter(serde_yaml::Mapping),
    Empty,
}

impl<'a> Event<'a> {
    fn is_attrs(&self) -> bool {
        match *self {
            Event::Attributes(..) => true,
            _ => false
        }
    }

    fn to_html_help(&self, out: &mut Write, cfg: &Config, stack: &mut Vec<Event<'a>>) -> fmt::Result {
        use self::Event::*;
        match *self {
            Start(Tag::Nothing) => Ok(()),
            Start(ref t) | SelfClosing(ref t) => {
                write!(out, "<")?;
                t.to_html(out, cfg)?;
                if let &Tag::Section(_) = t {
                } else {
                    while stack.last().map(|e| e.is_attrs()).unwrap_or(false) {
                        if let Attributes(ty, attrs) = stack.pop().unwrap() {
                            match ty {
                                Some("css") => {
                                    write!(out, " style=\"")?;
                                    for (name, val) in attrs {
                                        write!(out, "{}:{};", name, val)?;
                                    }
                                    write!(out, "\"")?;
                                },
                                _ => {
                                    for (name, val) in attrs {
                                        write!(out, " {}=\"{}\"", name, val)?;
                                    }
                                },
                            }
                        }
                    }
                }

                if let SelfClosing(ref t) = *self {
                    write!(out, "/")?;
                }
                write!(out, ">")
            },
            End(Tag::Nothing) => Ok(()),
            End(ref t) => {
                write!(out, "</")?;
                t.to_html(out, cfg)?;
                write!(out, ">")
            },
            Text(ref s) => write!(out, "{}", s),
            String(ref s) => write!(out, "{}", s),
            Span(ref s) => {
                for evt in s {
                    evt.to_html_help(out, cfg, stack)?;
                }
                Ok(())
            },
            Attributes(ref ty, ref attrs) => {
                stack.push(Attributes(ty.clone(), attrs.clone()));
                Ok(())
            },
            LineBreak => {
                write!(out, "{}", cfg.line_break)
            },
            FrontMatter(..) => Ok(()),
            _ => Ok(())
        }
    }

    pub fn to_html(&self, cfg: &Config) -> Result<String, fmt::Error> {
        let mut res = String::new();
        let mut stack = Vec::new();
        self.to_html_help(&mut res, cfg, &mut stack)?;
        Ok(res)
    }
}

pub type Stream<'a> = VecDeque<Event<'a>>;
pub type Stack<'a> = Vec<Tag<'a>>;
pub type SpanCmd<'a, 'b> = fn(&'a str, Context<'a, 'b>) -> Option<Stream<'a>>;
type Parser<'a, 'b> = fn(&'a str, &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>>;

#[derive(Debug, Clone)]
pub struct Context<'a, 'b> {
    stack: Stack<'a>,
    cfg: Config<'b>,
    span_cmds: HashMap<&'a str, SpanCmd<'a, 'b>>,
}
impl<'a, 'b> Context<'a, 'b> {
    fn new(cfg: Config<'b>) -> Self {
        Self {
            stack: Stack::new(),
            span_cmds: Default::default(),
            cfg,
        }
    }
}


macro_rules! stream_ctx (
    ($name:ident < 'a > ($ctx:ident), $submac:ident!( $($args:tt)* )) => {
        #[allow(unused_variables)]
        fn $name<'a, 'b>(i: &'a str, $ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
            $submac!(i, $($args)*)
        }
    };
    (pub $name:ident < 'a > ($ctx:ident), $submac:ident!( $($args:tt)* )) => {
        #[allow(unused_variables)]
        pub fn $name<'a, 'b>(i: &'a str, $ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
            $submac!(i, $($args)*)
        }
    };
);

macro_rules! stream (
    ($name:ident < 'a >, $submac:ident!( $($args:tt)* )) => {
        #[allow(unused_variables)]
        fn $name<'a>(i: &'a str) -> IResult<&'a str, Stream<'a>> {
            $submac!(i, $($args)*)
        }
    };
    (pub $name:ident < 'a >, $submac:ident!( $($args:tt)* )) => {
        #[allow(unused_variables)]
        pub fn $name<'a>(i: &'a str) -> IResult<&'a str, Stream<'a>> {
            $submac!(i, $($args)*)
        }
    };
);


named!(whitespace(&str) -> &str, recognize!(opt!(is_a!(" \t\r\n"))));

named!(space_sep<&str, &str>, eat_separator!(&b" \t"[..]));

macro_rules! spaced (
  ($i:expr, $($args:tt)*) => (
    {
      sep!($i, space_sep, $($args)*)
    }
  )
);

const SPECIAL_CHARS: &str = " ~()-<>[]!#@*_`{}^*+-\\`\n\'\"?";

// Includes ligatures
named!(special_char(&str) -> &str,
    alt_complete!(
        map!(tag!(" > "), |_| " &gt; ") |
        map!(tag!(" < "), |_| " &lt; ") |
        map!(tag!("<-"), |_| "&larr;") |
        map!(tag!("->"), |_| "&rarr;") |
        map!(tag!(">="), |_| "&ge;") |
        map!(tag!("<="), |_| "&le;") |
        map!(tag!(" +- "), |_| " &plusmn; ") |
        map!(tag!("---"), |_| "&mdash;") |
        map!(tag!("--"), |_| "&ndash;") |
        map!(tag!("..."), |_| "&hellip;") |
        map!(preceded!(tag!("\\"), one_of!("\n")), |_| "<br/>") |
        preceded!(tag!("\\"), recognize!(one_of!(SPECIAL_CHARS))) |
        recognize!(none_of!("\r\n"))
    )
);


named!(word_char(&str) -> &str,
    alt_complete!(alphanumeric | is_not!(SPECIAL_CHARS))
);

named!(word_s(&str) -> &str,
    recognize!(many1!(word_char))
);
named!(special_word_s(&str) -> &str,
    call!(special_char)
);

named!(accent(&str) -> &str,
    alt_complete!(
        map!(tag!("^"), |_| "circ") |
        map!(tag!("~"), |_| "tilde") |
        map!(tag!("'"), |_| "acute") |
        map!(tag!("`"), |_| "grave") |
        map!(tag!("\""), |_| "uml") |
        map!(tag!(","), |_| "cedil") |
        map!(tag!("o"), |_| "ring")
    )
);

stream!(escape_code<'a>,
    alt_complete!(
        map!(preceded!(tag!("\\"), pair!(accent, delimited!(tag!("{"), one_letter, tag!("}")))), |(accent, letter)| {
            let mut res = Stream::from_elem(Event::Text("&"));
            res.push_back(Event::Text(letter));
            res.push_back(Event::Text(accent));
            res.push_back(Event::Text(";"));
            res
        }) |
        map!(separated_pair!(digit, tag!("/"), digit), |(num, denom)| {
            let mut res = Stream::new();
            // numerator
            res.push_back(Event::Start(Tag::Custom("sup")));
            res.push_back(Event::Text(num));
            res.push_back(Event::End(Tag::Custom("sup")));

            res.push_back(Event::Text("&frasl;"));

            // denominator
            res.push_back(Event::Start(Tag::Custom("sub")));
            res.push_back(Event::Text(denom));
            res.push_back(Event::End(Tag::Custom("sub")));
            res
        })
    )
);

fn eol_or_eof(input: &str) -> IResult<&str, &str> {
    if input.is_empty() {
        IResult::Done(input, "")
    } else if input.starts_with('\n') {
        IResult::Done(&input[1..], "\n")
    } else {
        IResult::Incomplete(Needed::Size(1))
    }
}

fn word<'a>(input: &'a str) -> IResult<&'a str, Stream<'a>> {
    alt_complete!(input,
        escape_code |
    map!(word_s, // ???
        |s: &'a str| Stream::from_elem(Event::Text(s))))
}

fn special_text<'a>(input: &'a str) -> IResult<&'a str, Stream<'a>> {
    map!(input, special_char, |s| Stream::from_elem(Event::Text(s)))
}

fn wrapped<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>, val: Tag<'a>, start: &str, end: &str) -> IResult<&'a str, Stream<'a>> {
    let (rem, mut ending) = {
        if let IResult::Done(rem, _) = tag!(input, start) {
            (rem, false)
        } else {
            (try_parse!(input, tag!(end)).0, true)
        }
    };
    let started = ctx.stack.last() == Some(&val);
    if start == end {
        // ending = false, always.
        ending = started;
    } else {
        // if start tag, ending = false.
        // if end tag, ending = true.
        if ending {
            if started {
                ending = true;
            } else {
                return IResult::Incomplete(Needed::Unknown);
            }
        }
    };

    let mut res = Stream::new();
    if ending {
        ctx.stack.pop();
        res.push_back(Event::End(val));
    } else {
        ctx.stack.push(val.clone());
        res.push_back(Event::Start(val));
    }
    IResult::Done(rem, res)
}

fn wrapped_span<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>, val: Tag<'a>, start: &'a str, end: &'a str) -> IResult<&'a str, Stream<'a>> {
    // Make sure we have the opening sequence.
    let (rem, start) = try_parse!(input, tag!(start));
    let can_balance = start != end;
    let eol = rem.find("\n");
    let line = match eol {
        Some(i) => &rem[0..i],
        None => rem
    };
    if line.trim_left().is_empty() {
        return IResult::Incomplete(Needed::Unknown);
    }
    let r_idx = if can_balance {
        // Look for the closing sequence, balancing any within
        let mut right_idx = 0;
        let mut rights = line.match_indices(end);
        match rights.find(|&(ri, _)| {
            right_idx += 1;
            line[0..(ri + 1)].matches(start).count() < right_idx
        }) {
            Some((i, _)) => i,
            _ => match rights.last() {
                Some((i, _)) => i,
                None => return IResult::Incomplete(Needed::Unknown),
            },
        }
    } else {
        // So, start == end.
        // Look for the next delimiting sequence, assuming that
        // delims immediately following the first one are all starts.
        let mut l_idx = 0;
        let mut adjacent_starts = 1;
        while line[l_idx..].starts_with(|c: char| !c.is_alphanumeric()) {
            if line[l_idx..].starts_with(start) {
                adjacent_starts += 1;
                l_idx += start.len();
            } else {
                l_idx += 1;
            }
        }
        let mut rights = line[l_idx..].match_indices(end);
        l_idx + match rights.find(|&(ri, _)| {
            adjacent_starts -= 1;
            adjacent_starts <= 0
        }) {
            Some((i, _)) => i,
            None => match rights.last() {
                Some((i, _)) => i,
                None => return IResult::Incomplete(Needed::Unknown),
            }
        }
    };

    let inner_text = &line[0..r_idx];
    //ctx.stack.push(val.clone());
    let (span_rem, mut s) = try_parse!(inner_text, apply!(span, ctx));
    //ctx.stack.pop();
    //let mut s: VecDeque<Event> = s.into_iter().flatten().collect();
    s.push_front(Event::Start(val.clone()));
    s.push_back(Event::End(val));
    let rem = &rem[r_idx+end.len()..];
    IResult::Done(rem, s)
}

stream_ctx!(italic<'a>(ctx),
    apply!(wrapped_span, ctx, Tag::Italic, "_", "_")
);

stream_ctx!(bold<'a>(ctx),
    apply!(wrapped_span, ctx, Tag::Bold, "*", "*")
);

named!(value_attrs(&str) -> Vec<(&str, Cow<str>)>,
    separated_list!(
        tag!(","),
        do_parse!(
            name: is_not!("= \t") >>
            tag!("=") >>
            val: is_not!(",}") >>
            (name, Cow::Borrowed(val))
        )
    )
);

named!(class_attrs(&str) -> Vec<(&str, Cow<str>)>,
    map!(do_parse!(
        opt!(space) >> tag!(".") >>
        val: is_not!("}") >>
        (val)
    ), |val: &str| {
        vec![("class", Cow::Owned(val.replace('.', " ")))]
    })
);

named!(attributes(&str) -> Event,
    spaced!(do_parse!(
        tag!("{") >>
        ty: opt!(alphanumeric) >>
        tag!(":") >>
        attrs: alt_complete!(class_attrs | value_attrs) >>
        tag!("}") >>
        (Event::Attributes(ty, attrs))
    ))
);

pub fn stricken<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    spaced!(input, do_parse!(
        del: apply!(wrapped_span, ctx, Tag::Deletion, "~~", "~~") >>
        ins: opt!(apply!(wrapped_span, ctx, Tag::Insertion, "[", "]")) >>
        //ins: opt!(delimited!("(", apply!(inner_span, ) ")"))
        (del, ins)
    )).map(|(del, ins)| {
        if let Some(ins) = ins {
            del.into_iter().chain(ins).collect()
        } else {
            del
        }
    })
}

pub fn bq_line<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    let (rem, _) = try_parse!(input, opt!(space)); // optional indent
    let (rem, carets) = try_parse!(rem, many1!(terminated!(tag!(">"), opt!(space))));
    let rank = carets.len();

    let last = ctx.stack.last().map(|x| *x);

    let (rem, mut elems) = try_parse!(rem, opt!(apply!(span, ctx)));
    let mut elems = elems.unwrap_or_default();

    if let Some(Tag::BlockQuote(prev_rank)) = last {
        if rank > prev_rank {
            elems.push_front(Event::Start(Tag::BlockQuote(rank)));
            ctx.stack.push(Tag::BlockQuote(rank));
        } else {
            while let Some(&Tag::BlockQuote(prev_rank)) = ctx.stack.last() {
                if rank < prev_rank {
                    ctx.stack.pop();
                    elems.push_front(Event::End(Tag::BlockQuote(prev_rank)));
                } else {
                    break;
                }
            }
        }
    } else {
        for curr in 1..rank+1 {
            ctx.stack.push(Tag::BlockQuote(curr));
            elems.push_front(Event::Start(Tag::BlockQuote(curr)));
        }
    }
    IResult::Done(rem, elems)
}


stream_ctx!(block_quote<'a>(ctx),
    map!(
        separated_nonempty_list!(line_ending, apply!(bq_line, ctx)),
        |s: Vec<Stream<'a>>| {
            let mut s: Stream<'a> = s.into_iter().flat_map(|mut s| {
                s.push_back(Event::LineBreak);
                s
            }).collect();
            while let Some(&Tag::BlockQuote(rank)) = ctx.stack.last() {
                ctx.stack.pop();
                s.push_back(Event::End(Tag::BlockQuote(rank)));
            }
            s
        }
    )
);

stream!(block_code<'a>,
    map!(do_parse!(
        indent: recognize!(opt!(space)) >>
        tag!("```") >>
        lang: opt!(alphanumeric) >>
        opt!(space) >>
        line_ending >>
        lines: many_till!(
        preceded!(many_m_n!(0, indent.len(), one_of!(" \t")), take_until_either_and_consume!("\n")),
            preceded!(opt!(space), tag!("```"))
        ) >>
        (indent.len(), lang, lines.0)
    ), |(indent, lang, lines): (_, _, Vec<&'a str>)| {
        let mut res = Stream::with_capacity(5);
        res.push_back(Event::Start(Tag::Code(true)));
        if let Some(lang) = lang {
            let lc = "language-".to_string() + lang;
            res.push_back(Event::Attributes(None, vec![("class", Cow::Owned(lc))]));
        }
        res.push_back(Event::Start(Tag::Code(false)));
        let mut started = false;
        for mut line in lines {
            let mut line = if started {
                "\n".to_owned() + line
            } else {
                started = true;
                line.to_owned()
            };
            line = line.replace('<', "&lt;");
            line = line.replace('>', "&gt;");
            res.push_back(Event::String(line));
        }
        res.push_back(Event::End(Tag::Code(false)));
        res.push_back(Event::End(Tag::Code(true)));
        res
    })
);

fn inline_code<'a>(input: &'a str) -> IResult<&'a str, Stream<'a>> {
    delimited!(input, tag!("`"), take_until_s!("`"), tag!("`"))
        .map(|contents| {
            let mut res = Stream::new();
            res.push_back(Event::Text(" "));
            res.push_back(Event::Start(Tag::Code(false)));
            res.push_back(Event::Text(contents));
            res.push_back(Event::End(Tag::Code(false)));
            res.push_back(Event::Text(" "));
            res
        })
}

stream_ctx!(smallcaps<'a>(ctx),
    map!(
        apply!(wrapped_span, ctx, Tag::Custom("span"), " ^", "^ "),
        |mut res: Stream<'a>| {
            res.push_front(Event::Attributes(Some("css"), vec![("font-variant", Cow::Borrowed("small-caps"))]));
            res
        }
    )
);

stream_ctx!(quote<'a>(ctx),
    map!(alt_complete!(
        apply!(wrapped_span, ctx, Tag::Custom("q"), " \"", "\"") |
        apply!(wrapped_span, ctx, Tag::Custom("q"), " \'", "\'")
    ), |mut res: Stream<'a>| {
        res.push_front(Event::Text(" "));
        res.push_back(Event::Text(" "));
        res
    })
);

stream_ctx!(element<'a>(ctx),
    alt_complete!(
        apply!(wrapped_span, ctx, Tag::Highlight, "[=", "=]") |
        apply!(command, ctx) |
        inline_code |
        apply!(wrapped_span, ctx, Tag::Custom("sub"), "_[", "]") |
        apply!(bold, ctx) |
        apply!(italic, ctx) |
        image |
        apply!(link, ctx) |
        apply!(stricken, ctx) |
        apply!(smallcaps, ctx) |
        // apply!(quote, ctx) |
        apply!(wrapped_span, ctx, Tag::Deletion, "~~", "~~") |
        apply!(wrapped_span, ctx, Tag::Custom("sup"), "^[", "]")
    )
);

stream_ctx!(special_elem<'a>(ctx),
    map!(
        pair!(apply!(element, ctx), many0!(attributes)),
        |(mut elem, attrs): (Stream<'a>, _)| {
            for a in attrs {
                elem.push_front(a);
            }
            elem
        }
    )
);

pub fn special_elem_old<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    if input.is_empty() {
        return IResult::Incomplete(Needed::Unknown);
    }

    let (rem, mut s) = try_parse!(input, apply!(element, ctx));
    let mut started = false;
    let mut ended = false;
    let mut balance: i32 = 0;
    for evt in s.iter().rev() {
        match evt {
            &Event::Start(_) => {
                balance -= 1;
                if balance <= 0 {
                    break;
                }
            },
            &Event::End(_) => {
                balance += 1;
            },
            _ => ()
        }
    }

    if balance == 0 {
        let (rem, attrs) = try_parse!(rem, many0!(attributes));
        for a in attrs {
            s.push_front(a);
        }
        IResult::Done(rem, s)
    } else {
        IResult::Done(rem, s)
    }
}

pub fn span<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    if input.is_empty() {
        return IResult::Incomplete(Needed::Unknown);
    }

    let mut res = VecDeque::new();
    let mut rem = input;
    while !rem.trim_left().is_empty() && !rem.starts_with('\n') {
        let r = alt_complete!(rem, apply!(special_elem, ctx) | word | special_text);
        match r {
            IResult::Done(r, mut evt) => {
                rem = r;
                res.append(&mut evt);
            },
            _ => break,
        }
    }
    IResult::Done(rem, res)
}

named!(one_newline(&str) -> &str, alt_complete!(tag!("\n") | tag!("\r\n")));
named!(newlines(&str) -> &str,
    recognize!(many1!(one_newline))
);

pub fn paragraph<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    ctx.stack.push(Tag::Paragraph);
    let res = separated_nonempty_list!(input, one_newline, alt_complete!(apply!(special_stmt, ctx) | apply!(span, ctx)))
        .map(|spans| {
            let mut s: Stream = spans.into_iter().flat_map(|mut x| {
                x.push_back(Event::LineBreak);
                x
            }).collect();
            s.pop_back();
            s.push_front(Event::Start(Tag::Paragraph));
            s.push_back(Event::End(Tag::Paragraph));
            s
        });
    ctx.stack.pop();
    res
}

fn header<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    map!(input,
        do_parse!(
            opt!(space) >>
            hashes: is_a!("#") >> space >>
            s: apply!(span, ctx) >>
            (s, hashes.len())
        ),
        |(mut s, rank): (Stream<'a>, usize)| {
            let tag = Tag::Header(rank as u32);
            s.push_front(Event::Start(tag));
            s.push_back(Event::End(tag));
            s
        }
    )

}

stream_ctx!(headers<'a>(ctx),
    map!(
        separated_nonempty_list!(one_newline, apply!(header, ctx)),
        |hs: Vec<Stream<'a>>| {
            let h_count = hs.len();
            let mut res: Stream = hs.into_iter().flatten().collect();
            let rank = match res.front().unwrap() {
                &Event::Start(Tag::Header(rank)) => rank,
                _ => unreachable!(), // must be a header, otherwise wouldn't get here.
            };
            if h_count > 1 { // Is this necessary? Maybe even wrap singular headers.
                let t = Tag::Custom("header");
                res.push_front(Event::Start(t.clone()));
                res.push_back(Event::End(t));
            }

            let sec = Tag::Section(rank);
            if !ctx.stack.iter().any(|t| match *t {
                Tag::Section(_) => false,
                _ => true,
            }) {
                // Sectioning
                res.push_front(Event::Start(sec.clone()));
                let mut lowest_rank = rank;

                ctx.stack = ctx.stack.iter().filter(|tag| {
                    if let &Tag::Section(some_rank) = *tag {
                        if some_rank < lowest_rank {
                            lowest_rank = some_rank;
                            true
                        } else {
                            // Close section, keep closing until some_rank < lowest_rank or no more tags.
                            res.push_front(Event::End(Tag::Section(some_rank)));
                            false
                        }
                    } else {
                        true
                    }
                }).map(|x| x.clone()).collect();
                ctx.stack.push(sec);
            }

            res
        }
    )
);

named!(var_list(&str) -> Vec<(&str, &str)>,
    spaced!(separated_list!(
        tag!(","),
        separated_pair!(is_not!("=,"), tag!("="), is_not!(","))
    ))
);

named!(arg_list(&str) -> Vec<&str>,
    spaced!(separated_list!(tag!(","), is_not!(",")))
);

stream_ctx!(link<'a>(ctx),
    map!(do_parse!(
        inner: apply!(wrapped_span, ctx, Tag::Link, "[", "]") >>
        url: delimited!(tag!("("), do_parse!(
            url: is_not!(") ") >> opt!(space) >>
            alt: opt!(delimited!(tag!("\""), is_not!(")\""), tag!("\""))) >>
            (url, alt)
        ), tag!(")")) >>
        (inner, url)
    ), |(mut s, (url, title)): (Stream<'a>, _)| {
        let mut attrs = vec![("href", Cow::Borrowed(url))];
        if let Some(t) = title {
            attrs.push(("title", Cow::Borrowed(t)));
        }
        s.push_front(Event::Attributes(None, attrs));
        s
    })
);

stream!(image<'a>,
    map!(do_parse!(
        //tag!("!") >> opt!(tag!("img")) >>
        alt: delimited!(tag!("!["), recognize!(opt!(is_not!("]"))), tag!("]")) >>
        //front: apply!(wrapped_span, ctx, Tag::Image, "![", "]") >>
        url: delimited!(tag!("("), do_parse!(
            url: is_not!(") ") >> opt!(space) >>
            alt: opt!(delimited!(tag!("\""), is_not!(")\""), tag!("\""))) >>
            (url, alt)
        ), tag!(")")) >>
        (alt, url)
    ), |(alt, (url, title))| {
        let mut res = VecDeque::new();
        res.push_back(Event::SelfClosing(Tag::Image));
        let mut attrs = vec![("src", Cow::Borrowed(url)), ("alt", Cow::Borrowed(alt))];
        if let Some(t) = title {
            attrs.push(("title", Cow::Borrowed(t)));
        }
        res.push_front(Event::Attributes(None, attrs));
        res
    })
);

stream_ctx!(command<'a>(ctx),
    map_opt!(do_parse!(
        tag!("!") >>
        cmd_to_call: alphanumeric >>
        tag!("[") >>
        content: take_until_s!("]") >>
        tag!("]") >>
        (cmd_to_call, content)
    ), |(c, content)| {
        match ctx.span_cmds.get(c) {
            Some(cmd) => (cmd)(content, ctx.clone()),
            None => match span(content, &mut ctx.clone()) {
                IResult::Done(_, mut res) => {
                    res.push_front(Event::Start(Tag::Custom(c)));
                    res.push_back(Event::End(Tag::Custom(c)));
                    Some(res)
                },
                _ => None
            }
        }
    })
);

stream!(horizontal_rule<'a>,
    map!(
        many_m_n!(3, 999, one_of!("-=")),
        |_| Stream::from_elem(Event::SelfClosing(Tag::HorizontalRule))
    )
);

fn one_letter(input: &str) -> IResult<&str, &str> {
    if !input.is_empty() && input.starts_with(|c: char| c.is_alphabetic()) {
        IResult::Done(&input[1..], &input[0..1])
    } else {
        IResult::Incomplete(Needed::Size(1))
    }
}

named!(unordered_marker(&str) -> &str, recognize!(one_of!("*-+")));
named!(list_marker(&str) -> (&str, bool),
    alt_complete!(
        map!(terminated!(one_letter, tag!(".")), |s| (s, true)) |
        map!(terminated!(digit, tag!(".")), |s| (s, true)) |
        map!(unordered_marker, |s| (s, false))
    )
);

pub fn desc_item<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    let prev_rank = if let Some(&Tag::DefList(rank)) = ctx.stack.last() {
        rank as u32
    } else {
        return IResult::Incomplete(Needed::Unknown);
    };

    let (rem, indent) = try_parse!(input, opt!(space));
    let (rem, dot) = try_parse!(rem, opt!(spaced!(unordered_marker)));
    let rank = indent.map_or(0, |i| i.len()) as u32;
    let is_term = dot.is_some();
    let tag = if is_term {
        Tag::DefTerm(rank)
    } else {
        Tag::DefDef(rank)
    };

    if is_term {
        if rank > prev_rank {
            ctx.stack.push(Tag::DefList(rank));
        } else if rank < prev_rank {
            ctx.stack.pop();
        }
    }

    ctx.stack.push(tag);
    let res = span(rem, ctx).map(|mut contents| {
        contents.push_front(Event::Start(tag));
        contents.push_back(Event::End(tag));
        if is_term {
            if rank > prev_rank {
                contents.push_front(Event::Start(Tag::DefList(rank)));
                contents.push_front(Event::Start(Tag::DefDef(rank)));
            } else if rank < prev_rank {
                contents.push_front(Event::End(Tag::DefDef(prev_rank)));
                contents.push_front(Event::End(Tag::DefList(prev_rank)));
            }
        }
        contents
    });
    ctx.stack.pop();
    res
}

pub fn desc_list<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    ctx.stack.push(Tag::DefList(0));
    let res = spaced!(input, do_parse!(
        tag!("!dl") >>
        items: many1!(preceded!(line_ending, apply!(desc_item, ctx))) >>
        (items)
    )).map(|items| {
        let mut res: Stream = items.into_iter().flatten().collect();
        res.push_front(Event::Start(Tag::DefList(0)));
        res.push_back(Event::End(Tag::DefList(0)));
        res
    });
    ctx.stack.pop();
    res
}


pub fn list_item_pretext<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    alt_complete!(input,
        map!( // checkbox
            spaced!(delimited!(tag!("["), opt!(one_of!("Xx*+")), tag!("]"))),
            |check: Option<char>| {
                Stream::from_elem(Event::SelfClosing(Tag::Checkbox(check.is_some())))
            }
        )
    )
}

pub fn list_item<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    let (rem, indent) = try_parse!(input, opt!(space));
    let (rem, (marker, ordered)) = try_parse!(rem, terminated!(list_marker, space));
    let rank = indent.map_or(0, |i| i.len()) as u32;
    let (prev_rank, started, nested) = if let Some(&Tag::ListItem(rank)) = ctx.stack.last() {
        (rank as u32, false, true)
    } else if let Some(&Tag::List(rank, _)) = ctx.stack.last() {
        (rank as u32, false, false)
    } else {
        (rank, true, false)
    };
    let tag = Tag::ListItem(rank);

    // possibly a checklist item
    let (rem, pretext) = try_parse!(rem, opt!(apply!(list_item_pretext, ctx)));

    let (rem, first) = try_parse!(rem, delimited!(opt!(space), alt_complete!(apply!(header, ctx) | block_code | apply!(span, ctx)), eol_or_eof));
    many_till!(rem,
        delimited!(
            many_m_n!(rank as usize, 999, one_of!(" \t")),
            alt_complete!(apply!(header, ctx) | block_code | apply!(span, ctx)),
//            apply!(span, ctx),
            line_ending
        ),
        peek!(alt_complete!(
            delimited!(opt!(space), recognize!(list_marker), space) |
            delimited!(opt!(space), line_ending, not!(one_of!(" \t"))) |
            preceded!(whitespace, eof!())
        ))
    ).map(move |(elems, _)| {
        let mut elems: Stream<'a> = first.into_iter().chain(elems.into_iter().flat_map(|mut e| {
            e.push_front(Event::Text(" "));
            e
        })).collect();
        let mut denesting = false;
        let started = match ctx.stack.last() {
            Some(&Tag::List(prev_rank, _)) => false,
            Some(&Tag::ListItem(prev_rank)) => {
                if rank < prev_rank {
                    denesting = true;
                    ctx.stack.pop();
                }
                rank > prev_rank
            },
            _ => true,
        };

        if started {
            ctx.stack.push(Tag::List(rank, ordered));
        }
        if nested {
            ctx.stack.pop();
        }
        ctx.stack.push(tag);


        if let Some(pt) = pretext {
            for elem in pt.into_iter().rev() {
                elems.push_front(elem);
            }
        }
        elems.push_front(Event::Start(tag));
        if started {
//            let t = ctx.stack.pop().unwrap();
            elems.push_front(Event::Start(Tag::List(rank, ordered)));
//            elems.push_back(Event::End(t));
            if ordered && marker.chars().all(char::is_numeric) {
                elems.push_front(Event::Attributes(None, vec![("start", Cow::Borrowed(marker))]));
            }
        }
        if denesting {
            elems.push_front(Event::End(Tag::ListItem(rank)));
            for t in ctx.stack.iter().rev() {
                if let &Tag::List(..) = t {
                    elems.push_front(Event::End(*t));
                    break;
                }
            }
        }
        if nested && !started {
            elems.push_front(Event::End(tag));
        }
        elems
    })
}
pub fn list_item_old<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    let (rem, indent) = try_parse!(input, opt!(space));
    if rem.is_empty() {
        return IResult::Incomplete(Needed::Unknown);
    }
    let (rem, marker) = try_parse!(rem, opt!(terminated!(list_marker, space)));
    if marker.is_none() {
        if let Some(&Tag::ListItem(_)) = ctx.stack.last() {
        } else {
            return IResult::Incomplete(Needed::Unknown);
        }
    }

    let rank = indent.map_or(0, |i| i.len()) as u32;
    let (prev_rank, started, nested) = if let Some(&Tag::ListItem(rank)) = ctx.stack.last() {
        (rank as u32, false, true)
    } else if let Some(&Tag::List(rank, _)) = ctx.stack.last() {
        (rank as u32, false, false)
    } else {
        (rank, true, false)
    };
    let tag = Tag::ListItem(rank);


    let (rem, pretext) = try_parse!(rem, opt!(apply!(list_item_pretext, ctx)));

    alt_complete!(rem, apply!(header, ctx) | block_code | apply!(span, ctx)).map(move |mut contents| {
        if let Some((m, ordered)) = marker {
            if let Some(pt) = pretext {
                for elem in pt.into_iter().rev() {
                    contents.push_front(elem);
                }
            }
            contents.push_front(Event::Start(tag));
            if !nested || rank > prev_rank {
                // if nested, list item is open here; else, beginning of a list.
                // leave item open, start list and start item.
                ctx.stack.push(Tag::List(rank, ordered));
                contents.push_front(Event::Start(Tag::List(rank, ordered)));
                if ordered && m.chars().all(char::is_numeric) {
                    contents.push_front(Event::Attributes(None, vec![("start", Cow::Borrowed(m))]));
                }
            } else if rank < prev_rank {
                // list item is open here, it was a nested.
                // de-nest back to prev. level of list.
                contents.push_front(Event::End(tag));
                let mut prev_rank = prev_rank;
                while rank < prev_rank {
                    ctx.stack.pop(); // pop nested list item.
                    ctx.stack.pop(); // pop nested list
                    contents.push_front(Event::End(Tag::List(prev_rank, ordered)));
                    contents.push_front(Event::End(Tag::ListItem(prev_rank)));
                    prev_rank = match ctx.stack.last() {
                        Some(&Tag::ListItem(r)) => r,
                        Some(&Tag::List(r, _)) => r,
                        _ => break
                    };
                }
                ctx.stack.pop(); // pop root item
            } else {
                // inside a list item, at same level.
                // this is another item, then.
                ctx.stack.pop();
                contents.push_front(Event::End(Tag::ListItem(prev_rank)));
            }
            ctx.stack.push(tag);
        }

        contents
    })
}

pub fn list<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    try_parse!(input, preceded!(opt!(space), list_marker));
    //println!("trying list on: {}", input);

//    separated_nonempty_list!(input, maybe_multispace, apply!(list_item, ctx))
    many1!(input, apply!(list_item, ctx))
    .map(|res: Vec<Stream<'a>>| {
        let mut res = res.into_iter().flat_map(|mut s| {
            s.push_back(Event::Text(" "));
            s
        }).collect::<Stream>();
        println!("got a list, stack={:?}", ctx.stack);
        loop {
            let unclosed = ctx.stack.pop();
            match unclosed {
                Some(Tag::ListItem(..)) | Some(Tag::List(..)) => {
                    res.push_back(Event::End(unclosed.unwrap()));
                    continue;
                },
                Some(u) => ctx.stack.push(u),
                None => (),
            }
            break;
        }
        println!("closed unclosed, stack={:?}", ctx.stack);
        res
    })
}

pub fn special_stmt_front<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    map!(input,
        alt_complete!(apply!(headers, ctx) | apply!(desc_list, ctx) | apply!(list, ctx) | apply!(block_quote, ctx) | block_code | horizontal_rule),
        |mut res: Stream<'a>| {
            if ctx.stack.last() == Some(&Tag::Paragraph) {
                ctx.stack.pop();
                res.push_front(Event::End(Tag::Paragraph));
            }
            res
        }
    )
}

stream_ctx!(special_stmt<'a>(ctx),
    map!(
        pair!(apply!(special_stmt_front, ctx), many0!(preceded!(opt!(one_newline), attributes))),
        |(mut s, attrs): (Stream<'a>, _)| {
            for a in attrs {
                s.push_front(a);
            }
            s
        }
    )
);

pub fn statement<'a, 'b>(input: &'a str, ctx: &mut Context<'a, 'b>) -> IResult<&'a str, Stream<'a>> {
    alt_complete!(input, apply!(special_stmt, ctx) | apply!(paragraph, ctx))
}

stream!(front_matter<'a>,
    map_opt!(delimited!(
        tag!("---"),
        take_until_s!("---"),
        tag!("---")
    ), |s| {
        // We only need the first document.
        let data = match serde_yaml::from_str(s) {
            Ok(serde_yaml::Value::Mapping(doc)) => doc,
            _ => return None
        };
        Some(Stream::from_elem(Event::FrontMatter(data)))
    })
);

fn document_help<'a, 'b>(input: &'a str, cfg: &Config<'b>) -> IResult<&'a str, Event<'a>> {
    let mut ctx = Context::new(cfg.clone());

    ctx.span_cmds.insert("lit", |input: &'a str, ctx: Context| {
        let mut res = Stream::new();
        res.push_back(Event::Text(input));
        Some(res)
    });

    let (rem, _) = try_parse!(input, opt!(multispace));
    let (rem, mut fm) = try_parse!(rem, opt!(front_matter));
    let (rem, _) = try_parse!(rem, opt!(multispace));
    let (rem, mut res): (&str, Stream) = try_parse!(rem, map!(
        separated_list!(whitespace, apply!(statement, &mut ctx)),
        |stmts: Vec<Stream<'a>>| stmts.into_iter().flatten().collect())
    );
    for unclosed in ctx.stack.into_iter().rev() {
        res.push_back(Event::End(unclosed));
    }
    res.push_front(Event::Start(Tag::Document));
    res.push_back(Event::Attributes(None, vec![("class", Cow::Borrowed("document-end"))]));
    res.push_back(Event::Start(Tag::Custom("div")));
    res.push_back(Event::End(Tag::Custom("div")));
    res.push_back(Event::End(Tag::Document));
    if let Some(fm) = fm {
        for e in fm.into_iter().rev() {
            res.push_front(e);
        }
    }

    IResult::Done(rem, Event::Span(res))
}

pub fn document<'a, 'b>(input: &'a str, cfg: &Config<'b>) -> Result<Event<'a>, ()> {
    match document_help(input, cfg) {
        IResult::Done(_rem, res) => Ok(res),
        _ => Err(()),
    }
}
