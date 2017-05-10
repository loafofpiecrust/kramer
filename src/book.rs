
use {ast_pull, serde_json, serde_yaml};
use std::{io, fs};
use std::fs::{File};
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::collections::{HashMap};

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(tag = "type")]
pub enum Book {
    Section { name: String, chapters: Vec<Book> },
    Chapter {
        name: String,
        #[serde(skip_serializing_if="Option::is_none")]
        data: Option<serde_yaml::Mapping>,
        contents: String
    },
}

impl Book {
    fn is_chapter(&self) -> bool {
        match *self {
            Book::Chapter { .. } => true,
            _ => false,
        }
    }
    
    pub fn name(&self) -> &String {
        use self::Book::*;
        match *self {
            Section { ref name, .. } => name,
            Chapter { ref name, .. } => name,
        }
    }
}


pub fn build<P: AsRef<Path>>(dir: P, cfg: &ast_pull::Config) -> io::Result<Book> {
    let dir = dir.as_ref();
    let name = dir.components().last().unwrap().as_os_str().to_str().unwrap();
    if dir.is_dir() {
        let mut sec = Vec::default();
        let mut entries: Vec<_> = dir.read_dir()?.map(|e| e.unwrap().path()).collect();
        entries.sort();
        for path in entries {
            //let mut s = path.components().last().unwrap().as_os_str().to_str().unwrap();
            sec.push(build(&path, cfg)?);
        }
        sec.sort_by_key(|book| match book {
            &Book::Section { .. } => 0, // TODO: Add section index/priority
            &Book::Chapter { ref data, .. } => data.as_ref().map(|data|
                data.get(&serde_yaml::Value::String(format!("index")))
                    .map(|v| v.as_i64().unwrap_or(1))
                    .unwrap_or(1)
            ).unwrap_or(1)
        });
        Ok(Book::Section { name: name.to_string(), chapters: sec })
    } else if dir.is_file() {
        let mut file = File::open(dir)?;
        let mut contents = String::new();
        let name = name.rsplitn(2, '.').last().unwrap();
        file.read_to_string(&mut contents)?;
        let doc = ast_pull::document(&contents, cfg).unwrap();
        let data = if let ast_pull::Event::Span(ref stream) = doc {
            stream.front().map(|e| match e {
                &ast_pull::Event::FrontMatter(ref data) => Some(data.clone()),
                _ => None,
            }).unwrap_or(None)
        } else { None };
        let contents = format!("{}", doc.to_html(cfg).unwrap());
        
        Ok(Book::Chapter { name: name.to_string(), contents, data })
    } else {
        Err(io::Error::new(io::ErrorKind::NotFound, "Given non-existant file or folder"))
    }
}

//    pub fn to_html(&self, dir: &Path, cfg: &ast_pull::Config) -> io::Result<()> {
//        match *self {
//            Book::Section(ref chapters) => {
//                fs::create_dir_all(dir)?;
//                let mut nav_html = format!("<nav><ol>");
//                for &(ref name, ref c) in chapters {
//                    // TODO: impl numered priorities.
//                    let no_ext = name.rsplitn(2, '.').last().unwrap();
//                    nav_html += &format!("<li><a href=\"../{n}\">{n}</a></li>", n=no_ext);
//                    let next = dir.join(name);
//                    c.to_html(&next, cfg)?;
//                }
//                nav_html += "</ol></nav>";
//                let mut nav_file = File::create(dir.join("index.html"))?;
//                write!(nav_file, "{}", nav_html)?;
//            },
//            Book::Chapter(ref contents) => {
//                let mut file = File::create(dir.with_extension("html"))?;
//                write!(file, "{}", contents)?;
//            }
//        }
//
//        Ok(())
//    }
