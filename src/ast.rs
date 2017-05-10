
use std;
use std::fmt::{self, Display, Write, Error, Formatter};
use itertools::Itertools;
use std::collections::HashMap;
use std::borrow::Cow;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mod {
    Bold,
    Italic,
    Underline,
    Border,
    Strikethrough,
    Code(bool), // multiline?
    Quote,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Attributes {
    ty: Option<String>,
    attrs: Vec<(String, String)>,
}
impl Attributes {
    pub fn new(ty: Option<String>, attrs: Vec<(String, String)>) -> Self {
        Self {
            ty: ty,
            attrs: attrs,
        }
    }
    
    pub fn to_html(&self, vars: &HashMap<String, String>) -> String {
        let ty_s = self.ty.as_ref().map(|t| t.as_str());
        if ty_s == Some("css") || ty_s == Some("style") {
            "style=\"".to_string()
                + &self.attrs.iter()
                   .map(|&(ref a, ref b)|
                       Node::replace_vars((a.clone() + ":" + b), vars))
                   .join(";")
                + "\""
        } else {
            self.attrs.iter()
                .map(|&(ref k, ref v)| {
                    let s = k.clone() + "=\"" + v + "\"";
                    Node::replace_vars(s, vars)
                })
                .join(" ")
        }
    }
    
    pub fn append_attrs(&self, other: &Vec<(String, String)>) -> Self {
        let mut res = self.clone();
        res.attrs.extend_from_slice(other);
        res
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Node {
    Paragraph(Vec<Node>),
    Span(Vec<Node>),
    Line(Box<Node>),
    Link(Box<Node>, String),
    Image(Box<Node>, String),
    List(Vec<Node>, bool),
    // elements, ordered?
    Blockquote(Box<Node>),
    Header(Box<Node>, usize),
    // contents, header number
    
    Modded(Mod, Box<Node>),
    WithAttributes(Box<Node>, Vec<Attributes>, bool),
    // inner, type, attributes, is inner-most span?
    
    Text(String),
    SimpleTag(String, Box<Node>),
    // open, inner, close
    VarDecl(String, String),
    // name, value literal
    Article(Vec<Node>),
    Placeholder,
    Indented(Box<Node>),
}

#[derive(Clone, Debug)]
struct Context {
    vars: HashMap<String, String>,
    attrs: Option<Vec<Attributes>>,
}
impl Context {
    fn drop_attrs(self) -> Self {
        Self {
            attrs: None,
            ..self
        }
    }
}


impl Node {
    
    pub fn map_inner(self, f: fn(Node) -> Node) -> Node {
        use self::Node::*;
        match self {
            Indented(n) => Node::Indented(Box::new((f)(*n))),
            Modded(_, n) => Node::Indented(Box::new((f)(*n))),
            SimpleTag(_, n) => Node::Indented(Box::new((f)(*n))),
            n => (f)(n),
        }
    }
    
    fn replace_vars<'a, T>(input: T, vars: &HashMap<String, String>) -> Cow<'a, str>
            where Cow<'a, str>: From<T> {
        let mut res = Cow::from(input);
        for (key, v) in vars {
            if res.contains(key) {
                res = Cow::Owned(res.replace(key, v));
            }
        }
        res
    }
    
    fn fmt_with_vars(&self, out: &mut Write, mut ctx: Context) -> fmt::Result {
        use self::Node::*;
        let curr_style = ctx.attrs.as_ref()
            .map(|attrs| {
                let mut res = String::new();
                for attr in attrs {
                    println!("printing attribute list");
                    res += " ";
                    res += &attr.to_html(&ctx.vars);
                }
                res
            }).unwrap_or_default();
        
        match *self {
            Paragraph(ref nodes) => {
                let val = nodes.iter().map(|n| {
                    let mut r = String::new();
                    n.fmt_with_vars(&mut r, ctx.clone().drop_attrs());
                    r
                }).join("");
                write!(out, "<p>{}</p>", val)
            },
            Blockquote(ref inner) => {
                write!(out, "<blockquote {}>", curr_style)?;
                inner.fmt_with_vars(out, ctx.drop_attrs())?;
                write!(out, "</blockquote>")
            },
            Span(ref nodes) => {
                let styled = ctx.attrs.is_some();
                if styled {
                    write!(out, "<span {}>", curr_style)?;
                }
                
                write!(out, "{}", nodes.iter().map(|n| {
                    let mut r = String::new();
                    n.fmt_with_vars(&mut r, ctx.clone().drop_attrs());
                    r
                }).join(""))?;
                
                if styled {
                    write!(out, "</span>")?;
                }
                Ok(())
            },
            Header(ref inner, idx) => {
                write!(out, "<h{} {}>", idx, curr_style)?;
                inner.fmt_with_vars(out, ctx.drop_attrs())?;
                write!(out, "</h{}>", idx)
            }
            Link(ref contents, ref url) => {
                write!(out, "<a href=\"{}\" {}>", Node::replace_vars(url.as_ref(), &ctx.vars), curr_style)?;
                contents.fmt_with_vars(out, ctx.drop_attrs())?;
                write!(out, "</a>")
            },
            Image(ref contents, ref url) => {
                write!(out, "<img src=\"{}\" {}>", Node::replace_vars(url.as_ref(), &ctx.vars), curr_style)?;
                contents.fmt_with_vars(out, ctx.drop_attrs())?;
                write!(out, "</img>")
            }
            Modded(m, ref contents) => match m {
                Mod::Underline => {
                    write!(out, "<u {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</u>")
                },
                Mod::Bold => {
                    write!(out, "<strong {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</strong>")
                },
                Mod::Italic => {
                    write!(out, "<em {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</em>")
                },
                Mod::Quote => {
                    write!(out, "<q {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</q>")
                },
                Mod::Border => {
                    write!(out, "<mark {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</mark>")
                },
                Mod::Code(multiline) => {
                    if multiline {
                        write!(out, "<pre>")?;
                    }
                    write!(out, "<code {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</code>")?;
                    if multiline {
                        write!(out, "</pre>")?;
                    }
                    Ok(())
                },
                Mod::Strikethrough => {
                    write!(out, "<del {}>", curr_style)?;
                    contents.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</del>")
                }
            },
            WithAttributes(ref inner, ref obj, inner_most) => {
                let mut left = ctx.attrs.take().unwrap_or_default();
                left.append(&mut obj.clone());
                ctx.attrs = Some(left);
                
                if inner_most {
                    write!(out, "<span")?;
                    if let Some(attrs) = ctx.attrs.as_ref() {
                        for attr in attrs {
                            write!(out, " {}", attr.to_html(&ctx.vars))?;
                        }
                    }
                    write!(out, ">")?;
                    inner.fmt_with_vars(out, ctx.drop_attrs())?;
                    write!(out, "</span>")
                } else {
                    inner.fmt_with_vars(out, ctx)
                }
            },
            Text(ref s) => {
                write!(out, "{}", Node::replace_vars(s.as_ref(), &ctx.vars))
            },
            SimpleTag(ref tag, ref inner) => {
                write!(out, "<{} {}>", tag, curr_style)?;
                inner.fmt_with_vars(out, ctx)?;
                write!(out, "</{}>", tag)
            },
            VarDecl(ref name, ref value) => {
                ctx.vars.insert(name.trim().to_string(), value.clone());
                Ok(())
            },
            Line(ref inner) => {
                inner.fmt_with_vars(out, ctx)?;
                write!(out, "\n")
            },
            List(ref elems, ordered) => {
                write!(out, "<ul {}>", curr_style)?;
                write!(out, "{}", elems.iter().map(|n| {
                    let mut r = String::new();
                    n.fmt_with_vars(&mut r, ctx.clone().drop_attrs());
                    r
                }).join(""))?;
                write!(out, "</ul>")
            },
            Article(ref elems) => {
                write!(out, "<article {}>", curr_style)?;
                write!(out, "{}", elems.iter().map(|n| {
                    let mut r = String::new();
                    n.fmt_with_vars(&mut r, Context {
                        attrs: None,
                        ..ctx.clone()
                    });
                    r
                }).join(""))?;
                write!(out, "</article>")
            },
            Indented(ref inner) => {
                write!(out, " ")?;
                inner.fmt_with_vars(out, ctx)
            },
            Placeholder => Ok(()),
        }
    }
    
    pub fn to_html(&self) -> Result<String, fmt::Error> {
        let mut out = String::new();
        self.fmt_with_vars(&mut out, Context {
            vars: HashMap::new(),
            attrs: None,
        })?;
        Ok(out)
    }
}