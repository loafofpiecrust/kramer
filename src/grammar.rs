
pub use self::definition::*;

peg! definition(
r#"
use ast::{Mod, Node, Attributes};
use ast::Node::*;
use itertools::Itertools;

newline = "\n" / "\r\n"

doc_tag = "article"

stmt_list -> Node
    = s:statement ** (whitespace+) { Span(s) }
pub document -> Node
    = whitespace* s:stmt_list whitespace* {
        CustomWrap("<article>".to_owned(), Box::new(s), "</article>".to_owned())
    }

special_statement -> Node
    = var_decl
    / ul
    / header
    / horizontal_rule
    / block_code
    / blockquote
pub statement -> Node
    = special_statement
    / spaces* p:paragraph spaces* { p }

short_statement -> Node
    = special_statement
    / spaces* p:simple_span spaces* { p }

var_decl_op = "@"
var_decl -> Node
    = name:$(var_decl_op word) spaces* "=" spaces* value:$((!newline .)*) {
        VarDecl(name.to_string(), value.to_string())
    }

header -> Node
    = hashes:$("\#"*<1,8>) spaces* p:simple_span { Header(Box::new(p), hashes.len()) }
    / text:simple_span spaces* newline spaces* "="+ { Header(Box::new(text), 1) }
    / text:simple_span spaces* newline spaces* "-"+ { Header(Box::new(text), 2) }

horizontal_rule -> Node
    = [*-] ++ (spaces*) { Text("<hr/>".to_string()) }

ul_marker = "*" / "-"
ul_item -> Node
    = spaces* ul_marker spaces* p:simple_span spaces* {
        CustomWrap("<li>".to_owned(), Box::new(p), "</li>".to_owned())
    }
ul -> Node
    = items:ul_item ++ newline {
        CustomWrap("<ul>".to_owned(), Box::new(Span(items)), "</ul>".to_owned())
    }

spaces = [\t] / " "
whitespace = spaces / newline
special_char = [\[\]] / quote / "**"
comma_sep = spaces* "," spaces*
word_char = !special_char !whitespace .
pub word = word_char+
word_w_space = word spaces*
line_nonstarter = ul_marker / bq_delim

quote = "\"" / "\'"
quote_phrase -> Node
    = unstyled_phrase_no_words
    / w:$((!quote word_char)+ spaces*) { Text(w.to_string()) }
quotation -> Node
    = quote spaces* p:(quote_phrase+) spaces* quote { Modded(Mod::Quote, Box::new(Span(p))) }

italic_op = "/"
italic_phrase -> Node
    = unstyled_phrase_no_words
    / w:$((!italic_op word_char)+ spaces*) { Text(w.to_string()) }
italic -> Node
    = italic_op spaces* p:italic_phrase+ spaces* italic_op { Modded(Mod::Italic, Box::new(Span(p))) }

italibold -> Node
    = bold_op p:bolded bold_op { Modded(Mod::Italic, Box::new(p)) }


bold_op = "*"
bolded_phrase -> Node
    = unstyled_phrase_no_words
    / w:$((!bold_op word_char)+ spaces*) { Text(w.to_string()) }
pub bolded -> Node
    = bold_op spaces* p:bolded_phrase+ spaces* bold_op { Modded(Mod::Bold, Box::new(Span(p))) }

underline_op = "_"
underlined_phrase -> Node
    = unstyled_phrase_no_words
    / w:$((!underline_op word_char)+ spaces*) { Text(w.to_string()) }
pub underlined -> Node
    = underline_op spaces* p:(underlined_phrase+) spaces* underline_op {
        Modded(Mod::Underline, Box::new(Span(p)))
    }
    
    
border_start = "[="
border_end = "=]"
bordered_phrase -> Node
    = styled_phrase_no_words
    / w:$((!border_start !border_end word_char)+ spaces*) { Text(w.to_string()) }
pub bordered -> Node
    = border_start spaces* p:(bordered_phrase+) spaces* border_end {
        Modded(Mod::Border, Box::new(Span(p)))
    }


code_op = "\`"
code_phrase -> Node
    = styled_phrase_no_words
    / w:$((!code_op word_char)+ spaces*) { Text(w.to_string()) }
inline_code -> Node
    = code_op spaces* p:(code_phrase+) spaces* code_op {
        Modded(Mod::Code(false), Box::new(Span(p)))
    }

url = [^\(\)\[\]\<\> \t\n\r\\]+
link -> Node
    = "[" spaces* title:span spaces* "]" spaces* "(" spaces* url:$(url) spaces* ")" { Link(Box::new(title), url.to_string()) }


end_punctuation = [.?!]
punctuation = end_punctuation / [,;:/\\\(\)_*]
unstyled_phrase_no_words -> Node
    = quotation
    / bordered
    / inline_code
    / underlined
    / italibold
    / bolded
    / italic
    / link
    
styled_phrase_no_words -> Node
    = styled
    / unstyled_phrase_no_words

unstyled_phrase -> Node
    = unstyled_phrase_no_words
    / w:$(spaces* word spaces*) { Text(w.to_string()) }

style_list -> Vec<(String, String)> = s:style_attr ++ comma_sep { s }
style_open = "["
style_close = "]"
style_front -> (Node, bool)
    = p:unstyled_phrase_no_words { (p, false) }
    / style_open spaces* p:span spaces* style_close { (p, true) }
styled -> Node
    = p:style_front spaces*
            "{" spaces* ty:$((!":" word_char)*) spaces* ":" spaces* s:style_list spaces* "}" {
        let ty_opt = if ty == "" { None } else { Some(ty.to_string()) };
        WithAttributes(Box::new(p.0), Attributes::new(ty_opt, s), p.1)
    }

phrase -> Node // has styling
    = styled
    / p:unstyled_phrase { p }
    / #expected("phrase")

value_word = (![\{\},] .)+
style_value
    = quote (!quote .)+ quote
    / value_word

var_name = (!"=" word_char)+
style_attr -> (String, String)
    = name:$(var_name) spaces* "=" spaces* val:$(style_value) {
        (name.to_string(), val.to_string())
    }
    
    
phrase_sep
    = spaces* newline*<1> spaces*
    / spaces*

simple_span -> Node
    = p:phrase ++ (spaces*) {
        Span(p)
    }

span -> Node
    = header
    / blockquote
    / simple_span

phrase_w_sep -> Vec<Node>
    = p:phrase sep:$(phrase_sep) {
        let mut res = Vec::new();
        res.push(p);
        res.push(Text(sep.to_string()));
        res
    }

pub paragraph -> Node
    = p:phrase_w_sep+ { Paragraph(p.into_iter().flatten().collect()) }
    / #expected("paragraph")

bq_delim = ">"
bq_line -> Node
    = spaces* bq_delim spaces* p:span spaces* { p }
blockquote -> Node
    = p:bq_line ++ newline { Blockquote(Box::new(Span(p))) }
    / bq_delim spaces* p:paragraph { Blockquote(Box::new(p)) }
    / #expected("blockquote")

code_line = ([^`\`\n\r])*
code_contents = code_line ** newline
bc_delim = "```" / "~~~"
block_code -> Node
    = bc_delim spaces* newline? contents:$(code_contents) newline? spaces* bc_delim {
        Modded(Mod::Code(true), Box::new(Text(contents.to_owned())))
    }
"#);