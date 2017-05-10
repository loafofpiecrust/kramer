
use nom;
use ast::Attributes;
use std::fmt::{self, Display, Write, Error, Formatter};
use std::collections::{HashMap};
use itertools::Itertools;

pub trait Node {
    fn html_with_context(&self, out: &mut Write, ctx: &mut Context) -> fmt::Result;
    
    fn to_html(&self) -> Result<String, fmt::Error> {
        let mut out = String::new();
        self.html_with_context(&mut out, &mut Context {
            vars: HashMap::new(),
            attrs: None,
        })?;
        Ok(out)
    }
}

pub trait Parse<'a>: Sized + Node {
    fn parse(input: &'a str) -> nom::IResult<&'a str, Self>;
}


#[derive(Clone, Debug)]
pub struct Context {
    vars: HashMap<String, String>,
    attrs: Option<Vec<Attributes>>,
}
impl Context {
    pub fn drop_attrs(self) -> Self {
        Self {
            attrs: None,
            ..self
        }
    }
    
    pub fn attrs_html(&self) -> String {
        self.attrs.as_ref()
            .map(|a_s| a_s.iter().map(|a| a.to_html(&self.vars)).join(" "))
            .unwrap_or_default()
    }
}
