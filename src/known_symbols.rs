use std::borrow::Cow;

use std::collections::HashMap;

use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KnownSymbols {
    macros: HashMap<Cow<'static, str>, SmallVec<[ArgKind; 8]>>,
    envs: HashMap<Cow<'static, str>, SmallVec<[ArgKind; 8]>>,
    envs_alt: HashMap<Cow<'static, str>, SmallVec<[ArgKind; 8]>>,
}

impl KnownSymbols {
    pub fn get_macro_args(&self, name: &str) -> Option<&[ArgKind]> {
        self.macros.get(name).map(|a| a.as_slice())
    }

    pub fn get_env_args(&self, name: &str, is_alt: bool) -> Option<&[ArgKind]> {
        if is_alt {
            self.envs_alt
                .get(name)
                .map(|a| a.as_slice())
                .or_else(|| self.envs.get(name).map(|a| a.as_slice()))
        } else {
            self.envs.get(name).map(|a| a.as_slice())
        }
    }
}

impl KnownSymbols {
    fn new() -> Self {
        Self {
            macros: HashMap::with_capacity(1000),
            envs: HashMap::with_capacity(50),
            envs_alt: HashMap::with_capacity(10),
        }
    }
}

/// Argument kind of environment or cmd or macro.
///
/// Note that while parsing we expect to find a valid LaTeX
/// and all of the arguments are treated technically a optional.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArgKind {
    /// Optional argument like `[opt]`
    #[serde(rename = "o")]
    Optional,

    /// Mandatory argument like `{arg}` or `\cmd`.
    ///
    /// Note that the macro variant must have no arguments on its own
    #[serde(rename = "m")]
    Mandatory,

    /// Parenthesized block like `(x,y)`
    #[serde(rename = "pb")]
    ParenBlock,

    /// Star after macro.
    #[serde(rename = "s")]
    Star,

    /// A single command like `\cmd` or inside the block `{\cmd}`.
    Cmd,

    /// Accepts anything until a the next specified argument.
    ///
    /// For example used by `\def<cmd><arg_spec>{replacement}`
    AnyUntil,

    /// Accepts any `n` items. Item is either a block `{..}`
    /// or command `\cmd` or single character
    Any(u8),

    /// Equals sign.
    Eq,

    /// Length with unit like `5pt`.
    #[serde(rename = "len")]
    Length,

    /// Single number.
    #[serde(rename = "num")]
    Number,

    /// Single boolean.
    Bool,

    /// `width` keyword
    Width,
    /// `height` keyword
    Height,
    /// `at` keyword
    At,
    /// `by` keyword
    By,
    /// `depth` keyword
    Depth,
    /// `plus` keyword
    Plus,
    /// `minus` keyword
    Minus,
    /// `to` keyword
    To,
    /// `spread` keyword
    Spread,
    /// `semicolon` token
    Semicolon,
}

#[allow(non_upper_case_globals)]
pub static KNOWN_SYMBOLS: Lazy<KnownSymbols> = Lazy::new(|| {
    let txt = std::fs::read_to_string("./symbols/base_latex.symbols.yml").unwrap();
    serde_yaml::from_str(&txt).unwrap()
});
