

#[macro_use]
extern crate clap;


/// *Todo List*
/// - Built-in chapter indexing (integral, linked to Sections)
/// - Arbitrary html attributes added to a span of text eh?
/// - Images simply with URL, that build a stylable html structure.
/// - Videos with a simple URL for youtube or similar.
/// - Audio that will either pull from an mp3 url or youtube url. Polymer player ?
///     - Detect if it's from certain sites,
///       like for soundcloud use the same command but embed the soundcloud widget.
/// - Custom-defined widget, with the same syntax as audio and video.
/// - Image-comparison slider (?)
/// - Text overlay above image (or any html element?)
/// - parallax image
/// - gifs
/// - Easily embedded maps
///     - So, inline html (or pug) retained literally to have, say, a map.
/// - Pullquotes (almost like blockquotes, but off to the side.)
/// - Sidebar. (plug-in?)
/// - Table (integral)
/// - Button?
/// - Sections! (integral) *******
/// - pre-content grey matter data, ignored in html output. (preprocess step?)
/// - Unlocking chapters with passwords. Build into grey matter, maybe to be processed by a plug-in or something.
///     - Text becomes XOR encrypted with the password (not very secure, but it's not for security)
///       Then, as your password attempt changes, the gibberish changes until the password is right.
/// - Unordered lists: allow more span types. allow paragraphs.
/// - Checklists
///


/// Todo for a page that hosts this parser.
/// - Wysiwyg editor (eh, real hard.)
/// - linking chapters?
/// - Pages. work for here or for html organization?

extern crate kramer;

use kramer::*;

use std::path::Path;
use std::fs::{File};
use std::io::prelude::*;

use clap::{App, Arg};

fn main() {

    let cfg = ast_pull::Config::default();

    let matches = App::new("kramer")
        .version("1.0")
        .author("loafofpiecrust")
        .about("Similar to Markdown")
        .arg(Arg::with_name("input")
            .index(1)
            .help("the input file/folder to build a book from")
            .default_value("."))
        .arg(Arg::with_name("config")
            .short("c")
            .long("config")
            .takes_value(true))
        .get_matches();

    // Required parameter, so can unwrap.
    let inp = matches.value_of("input").unwrap_or(".");

    let mut file = File::open(inp).unwrap();
    let mut raw = String::new();
    file.read_to_string(&mut raw);

    println!("{:?}", ast_pull::document(&raw, &ast_pull::Config::default()).map(|d| d.to_html(&ast_pull::Config::default())));

    //book.unwrap().to_html(Path::new("test/book-out"), &cfg).unwrap();

}
//
// use kramer::*;
//
// fn main() {
//     println!("{:?}", adoc::lexer::nonempty_line("Shallots"));
//     println!("{:?}", adoc::lexer::paragraphs(
//     r#"
//     Hello my name is
//     Yolo
//
//     Shallots
//
//     [cmd]
//     --
//     Some block
//     of shit
//     --
//
//     "#));
//     println!("{:?}", adoc::lexer::elements(r#"
// I'm a paragraph.
//
// [quote]
// --
// I'm a block yo catch it.
// Multiple lines yo
//
// More
// --
//     "#));
// }
