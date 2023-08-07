use core::{fmt, mem};
use std::borrow::Cow;

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};

use crate::known_symbols::{ArgKind, KNOWN_SYMBOLS};
use crate::lexer::{Lexer, MultipeekLexer, Token};

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr<'a> {
    Macro(MacroName<'a>),
    KnownMacro(KnownMacro<'a>),
    Block(Vec<Expr<'a>>),
    SquareBlock(Vec<Expr<'a>>),
    ParenBlock(Vec<Expr<'a>>),
    Env(Env<'a>),
    KnownEnv(KnownEnv<'a>),
    Text(Cow<'a, str>),
    Number(&'a str),
    Comment(&'a str),
    LineBreak,
    ParBreak,
    Token(Token<'a>),
    DoubleDash,
    TripleDash,
    SuperScript(Box<Expr<'a>>),
    SubScript(Box<Expr<'a>>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum EnvKind {
    Regular,
    InlineMath,
    BlockMath,
    Special,
}

impl std::fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Macro(arg0) => arg0.fmt(f),
            Self::KnownMacro(arg0) => f.debug_tuple("Builtin").field(arg0).finish(),
            Self::Block(arg0) => f.debug_tuple("Block").field(arg0).finish(),
            Self::SquareBlock(arg0) => f.debug_tuple("SquareBlock").field(arg0).finish(),
            Self::ParenBlock(arg0) => f.debug_tuple("ParenBlock").field(arg0).finish(),
            Self::Env(arg0) => arg0.fmt(f),
            Self::KnownEnv(arg0) => arg0.fmt(f),
            //Self::SpecialEnv(arg0) => f.debug_tuple("SpecialEnv").field(arg0).finish(),
            Self::Text(arg0) => write!(f, "Text({arg0:?})"),
            Self::Number(arg0) => write!(f, "Number({arg0:?})"),
            Self::Comment(arg0) => f.debug_tuple("Comment").field(arg0).finish(),
            Self::LineBreak => write!(f, "LineBreak"),
            Self::ParBreak => write!(f, "ParBreak"),
            Self::Token(arg0) => write!(f, "Token({arg0:?})"),
            Self::DoubleDash => write!(f, "DoubleDash"),
            Self::TripleDash => write!(f, "TripleDash"),
            Self::SubScript(e) => f.debug_tuple("SubScript").field(e).finish(),
            Self::SuperScript(e) => f.debug_tuple("SuperScript").field(e).finish(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MacroName<'a> {
    name: &'a str,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct KnownMacro<'a> {
    name: &'a str,
    args: Vec<Expr<'a>>,
    is_alt: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Env<'a> {
    name: &'a str,
    children: Vec<Expr<'a>>,
    is_alt: bool,
    kind: EnvKind,
    start_end: Option<Box<(Expr<'a>, Expr<'a>)>>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct KnownEnv<'a> {
    name: &'a str,
    args: Vec<Expr<'a>>,
    children: Vec<Expr<'a>>,
    is_alt: bool,
    kind: EnvKind,
    start_end: Option<Box<(Expr<'a>, Expr<'a>)>>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Ast<'a> {
    exprs: Vec<Expr<'a>>,
}

impl<'a> Ast<'a> {
    #[must_use]
    const fn new() -> Self {
        Self { exprs: Vec::new() }
    }
}

pub struct Parser<'a> {
    lexer: MultipeekLexer<'a>,
    current_token: Token<'a>,
    errors: Vec<ParseError>,
    /// Token buffer. self.advance() will pop front this first and only if it's empty
    /// will advance the lexer.
    ///
    /// This is useful if some inner parser only needs to consume a part of the token
    /// (probably Token::Text).
    /// After consuming, it should `self.buf.push_back` the remainder of the token.
    /// Otherwise the outer loop will advance and skip that token.
    ///
    /// For example see `self.parse_macro_env_args` Any(n) section.
    token_buf: VecDeque<Token<'a>>,
}

impl<'a> Parser<'a> {
    #[must_use]
    pub fn new(mut lexer: Lexer<'a>) -> Self {
        let t1 = lexer.next_token();

        Self {
            lexer: MultipeekLexer::new(lexer),
            current_token: t1,
            errors: Vec::new(),
            token_buf: VecDeque::new(),
        }
    }

    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn from_str(s: &'a str) -> Self {
        let lexer = Lexer::new(s);
        Self::new(lexer)
    }

    #[must_use]
    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }

    fn parse_possible_arguments(&mut self, exprs: &mut Vec<Expr<'a>>) -> Result<(), ParseError> {
        let should_return = |s: &mut Parser<'_>| match s.next_token() {
            Token::LSquare
            | Token::LBrace
            | Token::LParen
            | Token::Space
            | Token::NewLine
            | Token::Assign
            | Token::Length(..)
            | Token::Number(..)
            | Token::Asterisk => {
                s.advance();
                false
            }
            _ => {
                // Only remove flags that were not set originally
                true
            }
        };

        if should_return(self) {
            return Ok(());
        }

        while !self.current_token.is_eof() {
            match self.current_token {
                Token::LSquare => {
                    let expr = self.parse_optional_args()?;
                    exprs.push(expr)
                }
                Token::LParen => {
                    let expr = self.parse_paren_block()?;
                    exprs.push(expr)
                }
                Token::LBrace => {
                    let expr = self.parse_block()?;
                    exprs.push(expr)
                }
                ref t @ (Token::Space
                | Token::NewLine
                | Token::Assign
                | Token::Length(..)
                | Token::Number(..)
                | Token::Asterisk) => {
                    exprs.push(Expr::Token(t.clone()));
                }
                _ => unreachable!(),
            }

            if should_return(self) {
                return Ok(());
            }
        }
        Ok(())
    }

    fn back_track_square_block(&mut self, rsquare: Expr<'a>, exprs: &mut Vec<Expr<'a>>) {
        debug_assert!(matches!(rsquare, Expr::Token(Token::RSquare)));

        match exprs
            .iter()
            .rposition(|e| matches!(e, Expr::Token(Token::LSquare)))
        {
            Some(pos) => {
                let block_children = exprs.split_off(pos + 1);
                exprs.pop();
                exprs.push(Expr::SquareBlock(block_children));
            }
            None => exprs.push(rsquare),
        }
    }

    fn back_track_paren_block(&mut self, rparen: Expr<'a>, exprs: &mut Vec<Expr<'a>>) {
        debug_assert!(matches!(rparen, Expr::Token(Token::RParen)));

        match exprs
            .iter()
            .rposition(|e| matches!(e, Expr::Token(Token::LParen)))
        {
            Some(pos) => {
                let block_children = exprs.split_off(pos + 1);
                exprs.pop();
                exprs.push(Expr::ParenBlock(block_children));
            }
            None => exprs.push(rparen),
        }
    }

    fn skip_space(&mut self) {
        while self.current_token.is_space() {
            self.advance();
        }
    }

    fn skip_newline_and_spaces(&mut self) {
        while matches!(self.current_token, Token::Space | Token::NewLine) {
            self.advance();
        }
    }

    fn peek_after_newline_and_spaces(&mut self) -> (usize, Token<'a>) {
        let mut i = 0;
        loop {
            let peeked = self.lexer.peek_nth(i);
            match peeked {
                Token::Space | Token::NewLine => {
                    i += 1;
                }
                _ => return (i, peeked.clone()),
            }
        }
    }

    fn parse_macro_env_args(
        &mut self,
        expected_args: &[ArgKind],
    ) -> Result<(Vec<Expr<'a>>, bool), ParseError> {
        let mut args = Vec::with_capacity(expected_args.len());
        let mut is_alt = false;

        for (i, expected_arg) in expected_args.iter().enumerate() {
            let (_, tok) = self.peek_after_newline_and_spaces();
            let tok = if tok.is_comment() {
                self.advance();
                self.skip_newline_and_spaces();
                args.push(Expr::Token(self.current_token.clone()));
                let (_, tok) = self.peek_after_newline_and_spaces();
                tok
            } else {
                tok
            };

            match expected_arg {
                ArgKind::Optional => {
                    if tok.is_lsquare() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_lsquare, "[")?;
                        let block = self.parse_optional_args()?;
                        args.push(block);
                    }
                }
                ArgKind::Mandatory => {
                    let arg = match tok {
                        Token::LBrace => {
                            self.advance();
                            self.skip_newline_and_spaces();
                            self.parse_block()?
                        }
                        Token::MacroName(name) => {
                            self.advance();
                            self.skip_newline_and_spaces();
                            Expr::Macro(MacroName { name })
                        }
                        _ => {
                            return Err(ParseError(format!(
                                "Expected block or cmd. Found {:?}",
                                &self.current_token
                            )))
                        }
                    };
                    args.push(arg);
                }
                ArgKind::Star => {
                    if tok.is_asterisk() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_asterisk, "*")?;
                        is_alt = true;
                    }
                }
                ArgKind::Cmd => {
                    let arg = if tok.is_lbrace() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current_and_advance(Token::is_lbrace, "{")?; // eat start lbrace
                        let name =
                            self.expect_current_and_advance(Token::is_macro_name, "macro")?;
                        let name = name.as_macro_name().unwrap();

                        Expr::Block(vec![Expr::Macro(MacroName { name })])
                    } else if tok.is_macro_name() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        let name = self.current_token.as_macro_name().unwrap();
                        Expr::Macro(MacroName { name })
                    } else {
                        return Err(ParseError("".into()));
                    };

                    args.push(arg);
                }
                ArgKind::AnyUntil => {
                    let until = &expected_args[i + 1];
                    // TODO: support other tokens

                    let is_end =
                        |s: &mut Parser<'a>| matches!(s.next_token(), Token::LBrace | Token::Eof);

                    while !is_end(self) {
                        self.advance();
                        match self.parse_expression(Precedence::Lowest) {
                            Ok(e) => {
                                if !matches!(e, Expr::Comment(..)) {
                                    self.push_expr(e, &mut args)?
                                }
                            }
                            Err(err) => self.errors.push(err),
                        }
                    }
                }
                ArgKind::Eq => {
                    if tok.is_assign() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_assign, "*")?;
                        args.push(Expr::Token(tok));
                    }
                }
                ArgKind::Length => {
                    let tok = if tok.is_minus() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(tok));
                        let (_, tok) = self.peek_after_newline_and_spaces();
                        println!("{tok:?}");
                        tok
                    } else {
                        tok
                    };

                    let tok = if tok.is_number() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_number, "number")?;
                        args.push(Expr::Number(self.current_token.as_number().unwrap()));

                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_macro_name, "macroname")?;
                        args.push(Expr::Macro(MacroName {
                            name: self.current_token.as_macro_name().unwrap(),
                        }));
                        continue;
                    } else if tok.is_macro_name() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_macro_name, "macroname")?;
                        args.push(Expr::Macro(MacroName {
                            name: self.current_token.as_macro_name().unwrap(),
                        }));
                        continue;
                    } else {
                        tok
                    };

                    if tok.is_length() {
                        println!("o");
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_length, "*")?;
                        args.push(Expr::Token(tok));
                    }
                }
                ArgKind::Number => {
                    let tok = if tok.is_minus() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(tok));
                        let (_, tok) = self.peek_after_newline_and_spaces();
                        tok
                    } else if tok.is_macro_name() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_macro_name, "macroname")?;
                        args.push(Expr::Macro(MacroName {
                            name: self.current_token.as_macro_name().unwrap(),
                        }));
                        continue;
                    } else {
                        tok
                    };

                    if tok.is_number() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_number, "*")?;
                        args.push(Expr::Token(tok));
                    }
                }
                ArgKind::Any(count) => {
                    self.advance();
                    let mut j = 0;
                    while j < *count {
                        self.skip_newline_and_spaces();
                        match &mut self.current_token {
                            Token::Text(t) => {
                                // TODO: Any(n) takes the n characters from text.
                                // But it discards the rest at the moment but it shouldn't
                                // This happens because we modify current_token but outside
                                // of this function we advance and skip the remainder of the text
                                if let Some(c) = t.chars().next() {
                                    if c == '\\' {
                                        match t.chars().next() {
                                            Some(..) => {
                                                args.push(Expr::Text(Cow::Borrowed(&t[..2])));
                                                *t = &t[2..];
                                                j += 1;
                                                continue;
                                            }
                                            _ => {
                                                args.push(Expr::Text(Cow::Borrowed(t)));
                                            }
                                        }
                                    } else {
                                        args.push(Expr::Text(Cow::Borrowed(&t[..1])));
                                        *t = &t[1..];
                                        j += 1;
                                        continue;
                                    }
                                } else {
                                    self.advance();
                                    continue;
                                }
                            }
                            Token::LBrace => {
                                let block = self.parse_block()?;
                                args.push(block);
                            }
                            tok => args.push(Expr::Token(tok.clone())),
                        }

                        j += 1;
                        if j != *count {
                            self.advance();
                        }
                    }

                    match &self.current_token {
                        Token::Text(t) if !t.is_empty() => {
                            self.token_buf.push_back(self.current_token.clone());
                        }
                        _ => {}
                    }
                }
                ArgKind::ParenBlock => {
                    if tok.is_lparen() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        self.expect_current(Token::is_lparen, "(")?;
                        let block = self.parse_paren_block()?;
                        args.push(block);
                    }
                }
                ArgKind::Bool => match tok {
                    Token::Kw(t) if t == "true" || t == "false" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Width => match tok {
                    Token::Kw(t) if t == "width" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Height => match tok {
                    Token::Kw(t) if t == "height" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::At => match tok {
                    Token::Kw(t) if t == "at" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::By => match tok {
                    Token::Kw(t) if t == "by" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Depth => match tok {
                    Token::Kw(t) if t == "depth" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Plus => match tok {
                    Token::Kw(t) if t == "plus" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Minus => match tok {
                    Token::Kw(t) if t == "minus" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::To => match tok {
                    Token::Kw(t) if t == "to" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Spread => match tok {
                    Token::Kw(t) if t == "spread" => {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(self.current_token.clone()));
                    }
                    _ => {}
                },
                ArgKind::Semicolon => {
                    if tok.is_semicolon() {
                        self.advance();
                        self.skip_newline_and_spaces();
                        args.push(Expr::Token(Token::Semicolon));
                    }
                }
            }
        }

        Ok((args, is_alt))
    }

    fn push_expr(&mut self, e: Expr<'a>, exprs: &mut Vec<Expr<'a>>) -> Result<(), ParseError> {
        match e {
            Expr::Macro(MacroName { name }) => {
                eprintln!("Found an unknown macro `{name}`");
                exprs.push(e);
                // We don't know what arguments could the macro take.
                // Parse anything that follows as and could be an argument as such.
                self.parse_possible_arguments(exprs)?;
            }
            // Parse [..] and (..) in reverse because it completely OK to have unbalanced
            // () or [] in text or math expressions.
            e @ Expr::Token(Token::RSquare) => self.back_track_square_block(e, exprs),
            e @ Expr::Token(Token::RParen) => self.back_track_paren_block(e, exprs),

            // Expr::Text(new_text) => match exprs.last_mut() {
            //     Some(Expr::Token(tok @ (Token::RParen | Token::RSquare))) => {
            //         // If the last expression was an ] or ), then it cannot be
            //         // part of a delimited block. Hence it behaves exactly like
            //         // a text. Combine them into one.
            //         let s = match tok {
            //             Token::RParen => ")",
            //             Token::RSquare => "]",
            //             _ => unreachable!(),
            //         };

            //         let txt = Cow::Borrowed(s) + new_text;
            //         exprs.pop();
            //         exprs.push(Expr::Text(txt));
            //     }

            //     Some(Expr::Text(old_text)) => {
            //         // Combine two conseutive text tokens into one
            //         *old_text += new_text;
            //     }

            //     _ => exprs.push(Expr::Text(new_text)),
            // },
            s => exprs.push(s),
        };
        Ok(())
    }

    pub fn parse(&mut self) -> Ast<'a> {
        let mut ast = Ast::new();

        while !self.current_token.is_eof() {
            let result = self
                .parse_expression(Precedence::Lowest)
                .and_then(|e| self.push_expr(e, &mut ast.exprs));
            if let Err(e) = result {
                self.errors.push(e);
            }

            self.advance();
        }

        let ast = self.post_process(ast);

        ast
    }

    fn post_process(&mut self, ast: Ast<'a>) -> Ast<'a> {
        ast
    }

    fn next_token(&mut self) -> &Token<'a> {
        self.lexer.peek()
    }

    fn next_token_mut(&mut self) -> &mut Token<'a> {
        self.lexer.peek_mut()
    }

    /// Advances the parser to the next token and returns the current one.
    fn advance(&mut self) -> Token<'a> {
        // mem::swap(&mut self.current_token, &mut self.next_token());
        let tok = mem::replace(
            &mut self.current_token,
            self.token_buf
                .pop_front()
                .unwrap_or_else(|| self.lexer.next()),
        );
        //println!("{:?}", &tok);
        tok
    }

    fn parse_expression(&mut self, _precedence: Precedence) -> Result<Expr<'a>, ParseError> {
        let left = self.parse_prefix_expr()?;

        // while precedence < Self::precedence(&self.next_token()).unwrap_or(Precedence::Lowest) {
        //     if !Self::has_infix_parser(&self.next_token()) {
        //         return Ok(left);
        //     }
        //     self.advance();
        //     left = self.parse_infix_expr(left)?;
        // }

        Ok(left)
    }

    fn parse_prefix_expr(&mut self) -> Result<Expr<'a>, ParseError> {
        match &self.current_token {
            Token::Text(text) => self.parse_text(text),
            Token::Minus => {
                if self.next_token().is_minus() {
                    self.advance();
                    if self.next_token().is_minus() {
                        Ok(Expr::TripleDash)
                    } else {
                        Ok(Expr::DoubleDash)
                    }
                } else {
                    Ok(Expr::Token(Token::Minus))
                }
            }
            Token::Comment(text) => Ok(Expr::Comment(text)),
            Token::LineBreak => Ok(Expr::LineBreak),
            Token::ParBreak => Ok(Expr::ParBreak),
            Token::UpArrow => {
                self.advance();
                let right = self.parse_sub_super_script_right_expr()?;
                Ok(Expr::SuperScript(Box::new(right)))
            }
            Token::Underscore => {
                self.advance();
                let right = self.parse_sub_super_script_right_expr()?;
                Ok(Expr::SubScript(Box::new(right)))
            }
            Token::InlineMathLimiter | Token::InlineMathStartAlt => self.parse_inline_math(),
            Token::BlockMathLimiter | Token::BlockMathStartAlt => self.parse_simple_block_math(),
            Token::LBrace => self.parse_block(),
            Token::MacroName(name) if *name == "begin" => self.parse_env(),
            Token::MacroName(name) => Ok(match KNOWN_SYMBOLS.get_macro_args(name) {
                Some(args) => {
                    let name = *name;
                    let (args, is_alt) = self.parse_macro_env_args(args)?;
                    Expr::KnownMacro(KnownMacro { name, args, is_alt })
                }
                None => Expr::Macro(MacroName { name }),
            }),
            token => Ok(Expr::Token(token.clone())),
        }
    }

    fn parse_text(&mut self, text: &'a str) -> Result<Expr<'a>, ParseError> {
        // if self.lexer.context().is_empty() {
        //     let mut txt = text.to_string();
        //     //Combine Text() Space Text() into one
        //     loop {
        //         if self.current_token.is_text()
        //             && matches!(
        //                 self.next_token(),
        //                 Token::Space
        //                     | Token::NewLine
        //                     | Token::Dash
        //                     | Token::Plus
        //                     | Token::Asterisk
        //                     | Token::Lt
        //                     | Token::Gt
        //                     | Token::Slash
        //                     | Token::LParen
        //                     | Token::RParen //| Token::LSquare //| Token::RSquare
        //             )
        //             && matches!(self.lexer.peek_nth(1), Token::Text(..))
        //         {
        //             let separator = match self.next_token() {
        //                 Token::Space => ' ',
        //                 Token::NewLine => '\n',
        //                 Token::Minus => '-',
        //                 Token::Plus => '+',
        //                 Token::Asterisk => '*',
        //                 Token::Lt => '<',
        //                 Token::Gt => '>',
        //                 Token::Slash => '/',
        //                 Token::LParen => '(',
        //                 Token::RParen => ')',
        //                 Token::LSquare => '[',
        //                 Token::RSquare => ']',
        //                 _ => unreachable!(),
        //             };
        //             self.advance(); // eat current string
        //             self.advance(); // eat space
        //             txt.push(separator);
        //         } else if self.current_token.is_text() && self.next_token().is_text() {
        //             self.advance();
        //         } else {
        //             break;
        //         }

        //         txt.push_str(self.current_token.as_text().unwrap());
        //     }

        //     Ok(Expr::Text(Cow::Owned(txt)))
        // } else {
        Ok(Expr::Text(Cow::Borrowed(text)))
        // }
    }

    fn parse_sub_super_script_right_expr(&mut self) -> Result<Expr<'a>, ParseError> {
        Ok(match &mut self.current_token {
            Token::Text(t) => {
                // Only first character is parsed as a sub/super script
                // `a^saf` is equivalent to `a^{s}sf`
                let out_text = if t.len() == 1 {
                    t
                } else {
                    let out = &t[0..1];
                    *t = &t[1..];
                    self.token_buf.push_back(Token::Text(t));
                    out
                };
                Expr::Text(Cow::Borrowed(out_text))
            }
            Token::LSquare | Token::LParen => Expr::Token(self.current_token.clone()),
            _ => self.parse_expression(Precedence::Lowest)?,
        })
    }

    fn env_kind(name: &str) -> EnvKind {
        match name {
            "equation" | "aligned" | "align" | "gather" | "math" | "displaymath" | "cases"
            | "dcases" | "split" | "multiline" => EnvKind::BlockMath,
            "tikzpicture" => EnvKind::Special,
            _ => EnvKind::Regular,
        }
    }

    fn parse_env(&mut self) -> Result<Expr<'a>, ParseError> {
        // \begin{center}
        // 	\vspace*{0.2mm}
        // 	\textbf{\LARGE	Koduülesanded 5}
        // \end{center}

        self.expect_next_and_advance(Token::is_lbrace, "{")?;
        self.expect_next_and_advance(Token::is_text, "text")?;
        let name = self.advance();

        let is_alt = if self.current_token.is_asterisk() {
            self.advance();
            true
        } else {
            false
        };

        self.expect_current(Token::is_rbrace, "}")?;
        let name = name.as_text().unwrap();

        let kind = Self::env_kind(name);

        let mut children = Vec::new();

        let args = match KNOWN_SYMBOLS.get_env_args(name, is_alt) {
            Some(args) => Some(self.parse_macro_env_args(args)?),
            None => {
                self.parse_possible_arguments(&mut children)?;
                None
            }
        };

        self.advance();

        // Parse expressions until we reach the \end{name}.
        // It will be Macro(end), Block{Text(name)}
        while !self.current_token.is_eof() {
            match self.parse_expression(Precedence::Lowest) {
                Ok(stmt) => match stmt {
                    Expr::Macro(m) if m.name == "end" && self.next_token().is_lbrace() => {
                        self.check_env_end(name, is_alt)?;
                        break;
                    }
                    e => self.push_expr(e, &mut children)?,
                },
                Err(err) => self.errors.push(err),
            }

            self.advance();
        }

        if let Some((args, _)) = args {
            Ok(Expr::KnownEnv(KnownEnv {
                name,
                children,
                is_alt,
                kind,
                args,
                start_end: None,
            }))
        } else {
            Ok(Expr::Env(Env {
                name,
                children,
                is_alt,
                kind,
                start_end: None,
            }))
        }
    }

    fn parse_block(&mut self) -> Result<Expr<'a>, ParseError> {
        debug_assert!(self.current_token.is_lbrace());
        let mut exprs = Vec::new();

        self.advance(); // eat start lbrace

        while !self.current_token.is_rbrace() && !self.current_token.is_eof() {
            match self.parse_expression(Precedence::Lowest) {
                Ok(e) => self.push_expr(e, &mut exprs)?,
                Err(err) => self.errors.push(err),
            }
            self.advance();
        }

        debug_assert!(self.current_token.is_rbrace() || self.current_token.is_eof());

        Ok(Expr::Block(exprs))
    }

    fn parse_optional_args(&mut self) -> Result<Expr<'a>, ParseError> {
        debug_assert!(self.current_token.is_lsquare());
        let mut exprs = Vec::new();

        self.advance(); // eat start lbrace

        while !self.current_token.is_rsquare() && !self.current_token.is_eof() {
            if self.current_token.is_lsquare() {
                //
                self.parse_nested_square_block(&mut exprs)?;
                continue;
            }

            match self.parse_expression(Precedence::Lowest) {
                Ok(e) => self.push_expr(e, &mut exprs)?,
                Err(err) => self.errors.push(err),
            }
            self.advance();
        }

        Ok(Expr::SquareBlock(exprs))
    }

    fn parse_nested_square_block(&mut self, exprs: &mut Vec<Expr<'a>>) -> Result<(), ParseError> {
        let expr = self.parse_optional_args()?;
        println!("sq: {:?}", expr);

        match expr {
            Expr::SquareBlock(mut children) => {
                match children.len() {
                    0 => self.push_expr(Expr::Text("[]".into()), exprs)?,
                    1 => {
                        let item = children.pop().unwrap();

                        match (item, exprs.last_mut()) {
                            (Expr::Text(t), Some(Expr::Text(t2))) => {
                                *t2 += "[";
                                *t2 += t;
                                *t2 += "]";
                            }
                            (Expr::Text(t), _) => {
                                exprs.push(Expr::Text(Cow::Borrowed("[") + t + "]"))
                            }
                            (item, _) => exprs.push(item),
                        }
                    }
                    _ => {
                        let first = children.remove(0);
                        match (first, exprs.last_mut()) {
                            (Expr::Text(t), Some(Expr::Text(t2))) => {
                                *t2 += "[";
                                *t2 += t;
                            }
                            (Expr::Text(t), _) => exprs.push(Expr::Text(Cow::Borrowed("[") + t)),
                            (first, _) => exprs.push(first),
                        };

                        for e in children {
                            self.push_expr(e, exprs)?
                        }

                        self.push_expr(Expr::Text("]".into()), exprs)?;
                    }
                }

                self.advance();
            }
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_paren_block(&mut self) -> Result<Expr<'a>, ParseError> {
        debug_assert!(self.current_token.is_lparen());
        let mut exprs = Vec::new();

        self.advance(); // eat start lparen

        while !self.current_token.is_rparen() && !self.current_token.is_eof() {
            match self.parse_expression(Precedence::Lowest) {
                Ok(e) => self.push_expr(e, &mut exprs)?,
                Err(err) => self.errors.push(err),
            }
            self.advance();
        }

        Ok(Expr::ParenBlock(exprs))
    }

    /// Parses a inline math block delimited by `$`, `\(` or `\)`.
    ///
    /// It's OK to mix the delimiters as `$ \)` or `\( $` but `\(` cannot be the
    /// end delimiter and `\)` cannot be the start.
    fn parse_inline_math(&mut self) -> Result<Expr<'a>, ParseError> {
        debug_assert!(matches!(
            self.current_token,
            Token::InlineMathLimiter | Token::InlineMathStartAlt
        ));
        let start_token = self.advance();
        let mut children = Vec::new();

        while !matches!(
            self.current_token,
            Token::InlineMathLimiter | Token::InlineMathEndAlt | Token::Eof
        ) {
            if matches!(
                self.current_token,
                Token::InlineMathStartAlt
                    | Token::BlockMathStartAlt
                    | Token::BlockMathEndAlt
                    | Token::BlockMathLimiter
            ) {
                // TODO: return the text up to the bad limiter
                return Err(ParseError(String::from(
                    "Found invalid math environment delimiter inside the math environment.",
                )));
            }

            match self.parse_expression(Precedence::Lowest) {
                Ok(e) => self.push_expr(e, &mut children)?,
                Err(err) => self.errors.push(err),
            }
            self.advance();
        }

        debug_assert!(
            self.current_token.is_inline_math_limiter()
                || self.current_token.is_inline_math_end_alt()
                || self.current_token.is_eof()
        );

        Ok(Expr::Env(Env {
            name: "unnamed",
            kind: EnvKind::InlineMath,
            children,
            is_alt: false,
            start_end: Some(Box::new((
                Expr::Token(start_token),
                Expr::Token(self.current_token.clone()),
            ))),
        }))
    }

    /// Parses a math block delimited by `$$`, `\[` or `\]`.
    ///
    /// It's OK to mix the delimiters as `$$ \]` or `\[ $$` but `\[` cannot be the
    /// end delimiter and `\]` cannot be the start.
    fn parse_simple_block_math(&mut self) -> Result<Expr<'a>, ParseError> {
        debug_assert!(matches!(
            self.current_token,
            Token::BlockMathLimiter | Token::BlockMathStartAlt
        ));

        let start_token = self.advance();
        let mut children = Vec::new();

        while !matches!(
            self.current_token,
            Token::BlockMathLimiter | Token::BlockMathEndAlt | Token::Eof
        ) {
            if matches!(
                self.current_token,
                Token::BlockMathStartAlt
                    | Token::InlineMathStartAlt
                    | Token::InlineMathEndAlt
                    | Token::InlineMathLimiter
            ) {
                // TODO: return the text up to the bad limiter
                return Err(ParseError(format!(
                    "Found invalid math environment delimiter `{:?}` inside the math environment.",
                    self.current_token,
                )));
            }

            match self.parse_expression(Precedence::Lowest) {
                Ok(e) => self.push_expr(e, &mut children)?,
                Err(err) => self.errors.push(err),
            }
            self.advance();
        }

        Ok(Expr::Env(Env {
            name: "unnamed",
            kind: EnvKind::BlockMath,
            children,
            is_alt: false,
            start_end: Some(Box::new((
                Expr::Token(start_token),
                Expr::Token(self.current_token.clone()),
            ))),
        }))
    }

    /// Check if we have reached the end of environment.
    ///
    /// Expects that current_token is `\end` and checks that it is followed by
    /// `{name}` (or `{name*}` if is_alt==true).
    ///
    /// Returns `Ok(true)` if that was true and `Err(..)` if not.
    fn check_env_end(&mut self, name: &str, is_alt: bool) -> Result<bool, ParseError> {
        debug_assert!(matches!(self.current_token, Token::MacroName("end")));

        self.expect_next_and_advance(Token::is_lbrace, "{")?;
        self.expect_next(Token::is_text, "text")?;
        let block = self.parse_block()?;
        let b = match &block {
            Expr::Block(b) => b,
            _ => unreachable!(),
        };

        let correct_len = if is_alt { 2 } else { 1 };
        if b.len() == correct_len
            && (!is_alt || matches!(&b[1], Expr::Token(Token::Asterisk)))
            && matches!(&b[0], Expr::Text(t) if t == name)
        {
            Ok(true)
        } else {
            Err(ParseError(format!("Expected `MacroName(end), Block([Text(\"{}\")])` macro to end environment, found `\\MacroName(end), {:?}`", name, block)))
        }
    }

    /// Expect self.next_token() to match pred. If it does advance self and return the
    /// current token. If not return Err.
    fn expect_next_and_advance<'b, 'c>(
        &'b mut self,
        pred: fn(&Token<'c>) -> bool,
        expected: &'static str,
    ) -> Result<Token<'a>, ParseError>
    where
        'b: 'c,
    {
        if pred(self.next_token()) {
            Ok(self.advance())
        } else {
            Err(ParseError::expected_token(expected, self.next_token()))
        }
    }

    /// Expect self.current_token to match pred. If it does advance self and return the
    /// current token. If not return Err.
    #[allow(dead_code)]
    fn expect_current_and_advance<'b, 'c>(
        &'b mut self,
        pred: fn(&Token<'c>) -> bool,
        expected: &'static str,
    ) -> Result<Token<'a>, ParseError>
    where
        'b: 'c,
    {
        if pred(&self.current_token) {
            Ok(self.advance())
        } else {
            Err(ParseError::expected_token(expected, self.next_token()))
        }
    }

    /// Expect self.next_token() to match pred. If not return Err.
    #[allow(dead_code)]
    fn expect_next<'b, 'c>(
        &'b mut self,
        pred: fn(&Token<'c>) -> bool,
        expected: &'static str,
    ) -> Result<(), ParseError>
    where
        'b: 'c,
    {
        if pred(self.next_token()) {
            Ok(())
        } else {
            Err(ParseError::expected_token(expected, self.next_token()))
        }
    }

    /// Expect self.current_token to match pred. If not return Err.
    fn expect_current<'b, 'c>(
        &'b mut self,
        pred: fn(&Token<'c>) -> bool,
        expected: &'static str,
    ) -> Result<(), ParseError>
    where
        'b: 'c,
    {
        if pred(&self.current_token) {
            Ok(())
        } else {
            Err(ParseError::expected_token(expected, &self.current_token))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Precedence {
    Lowest = 0,
}

#[derive(Debug, Clone, Serialize)]
pub struct ParseError(String);

impl ParseError {
    fn expected_token<E: fmt::Debug + ?Sized>(expected: &E, found: &Token<'_>) -> Self {
        Self(format!(
            "expected token `{expected:?}` but found `{found:?}`",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    #[test]
    fn a() {
        let path = "/run/media/kalla/HDD_928GB/Kool/TÜMSc/3/Renormeerimismeetodid kvantväljateoorias/Kodutöö5/a.tex";
        let text = std::fs::read_to_string(path).unwrap();
        let mut lexer = Lexer::new(&text);
        let mut p = Parser::new(lexer);
        let doc = p.parse();
        println!("{doc:#?}");
        println!("{:#?}", p.errors())
    }

    macro_rules! insta_setup {
        ($($expr:expr),*; $input:expr) => {
            let mut settings = insta::Settings::clone_current();
            settings.set_snapshot_suffix(format!($($expr,)*));
            settings.set_info(&format!("input = `{}`", $input));
           // let f = file!();
            //let path = format!("{}/snapshots", &f[4..f.len()-3]);
            //settings.set_snapshot_path(path);
            //settings.set_prepend_module_to_snapshot(false);
            let _guard = settings.bind_to_scope();
        }
    }

    #[derive(Debug, Serialize)]
    struct AstWErrors<'a> {
        stmts: &'a [Expr<'a>],
        errors: &'a [ParseError],
    }

    #[rstest]
    #[case("m", r"\asdfr{pkg}")]
    #[case("om", r"\asdfr[opt]{pkg}")]
    #[case("som", r"\asdfr*[opt]{pkg}")]
    #[case("som_spaced", r"\asdfr  *  [opt]  {pkg}  ")]
    #[case("sm", r"\asdfr*{pkg}")]
    #[case("no_arg", r"\asdfr")]
    #[case("no_arg_star", r"\asdfr*")]
    #[case("eq_num", r"\asdfr=5")]
    #[case("num", r"\asdfr5")]
    #[case("len", r"\asdfr5pt")]
    #[case("eq_len", r"\asdfr=5pt")]
    fn unknown_macros(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("m", r"\usepackage{pkg}[not part]")]
    #[case("om", r"\documentclass[opt]{pkg}[not part]")]
    #[case("som", r"\chapter*[opt]{pkg}[not part]")]
    #[case("som_spaced", r"\chapter  *  [opt]  {pkg}  [not part]")]
    #[case("sm", r"\vspace*{pkg}[not part]")]
    #[case("no_arg", r"\lambda[not part]")]
    //
    #[case("eq_num", r"\adjdemerits=5[not part]")]
    #[case("num", r"\adjdemerits5[not part]")]
    #[case("num_spaced", r"\adjdemerits 5[not part]")]
    #[case("len", r"\arraycolsep5pt[not part]")]
    #[case("eq_len", r"\arraycolsep=5pt[not part]")]
    #[case("eq_len_macro", r"\arraycolsep=\mac[not part]")]
    #[case("eq_len_macro2", r"\arraycolsep=2.5\mac[not part]")]
    #[case("len_macro", r"\arraycolsep\mac[not part]")]
    #[case("len_macro2", r"\arraycolsep2.5\mac[not part]")]
    #[case("true_len1", r"\arraycolsep5truept[not part]")]
    #[case("true_len2", r"\arraycolsep=5 true pt[not part]")]
    #[case("true_len3", r"\arraycolsep 5 true pt[not part]")]
    //
    #[case("eq_neg_num", r"\adjdemerits=-5[not part]")]
    #[case("neg_num", r"\adjdemerits-5[not part]")]
    #[case("neg_num_spaced", r"\adjdemerits -5[not part]")]
    #[case("neg_len", r"\arraycolsep-5pt[not part]")]
    #[case("eq_neg_len", r"\arraycolsep=-5pt[not part]")]
    #[case("eq_neg_len_macro", r"\arraycolsep=-2.5\mac[not part]")]
    #[case("neg_len_macro", r"\arraycolsep-2.5\mac[not part]")]
    //
    #[case("only_opt_missing", r"\linebreak text")]
    #[case("only_opt_present", r"\linebreak[5][not part]")]
    #[case("bare_cmd", r"\newcommand\cmd[1]{#1}[not part]")]
    #[case("block_cmd", r"\newcommand{\cmd}[1]{#1}[not part]")]
    #[case("mixed1", r"\newtheorem*{m1}[o1]{m2}[o2][not part]")]
    #[case("mixed2", r"\newtheorem*{m1}{m2}{not part}")]
    #[case("Any(n)_with_text", r"\'abg ds")]
    #[case("=_macro", r"\parskip=\medskipamount")]
    //
    #[case(
        "optionals",
        r"\documentclass[opt, opt2, opt3=5pt, opt4={a, b}]{pkg}[not part]"
    )]
    // sym("def", [Cmd, AnyUntil, m]),
    #[case("def1", r"\def\a{part}{not part}")]
    #[case("def2", r"\def\a[#1]#2{part}{not part}")]
    #[case("def2_spaces", r"\def\a [#1]#2 {part}{not part}")]
    //  sym("atopwithdelims", [Any(2)]),
    #[case("any2_1", r"\atopwithdelims[]notpart")]
    #[case("any2_2", r"\atopwithdelims[)notpart")]
    #[case("any1", r"$\left(notpart\right)notpart$")]
    #[case("any2_macros", r"\atopwithdelims\a\b notpart")]
    #[case("accent1", r"asf\H ofs af")]
    #[case("accent2", r"asf\H {o}fs af")]
    #[case("accent3", r"asf\`ofs af")]
    // newcommand
    #[case("newcommand", r"\newcommand{\hc}[1]{#1^{\dagger}}")]
    #[case("renewcommand", r"\renewcommand{\headrulewidth}{1pt}")]
    #[case("cite", r"\cite{a,b,c}")]
    #[case("m_macro", r"\cite\asf")]
    #[case("parens", r"\put(1.2,3.4){content}{not part}")]
    #[case("kws", r"\hskip 3cm plus 5mm minus 6pt not part")]
    #[case("kws_no_spaces", r"\hskip3cmplus5mmminus6ptnot part")]
    #[case("kws_no_spaces_neg", r"\hskip-3cmplus-5mmminus-6ptnot part")]
    // hbox
    #[case("hbox1", r"\hbox spread 5pt{‘‘Oh, oh!’’ ... laughed.}")]
    #[case("hbox2", r"\hbox spread0.5\hsize{‘‘Oh, oh!’’ ... laughed.}")]
    fn known_macros(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("1", r"\usepackage[a]{pkg}")]
    #[case("1,2", r"\usepackage[a, 5pt]{pkg}")]
    #[case("1=", r"\usepackage[a=b]{pkg}")]
    #[case("1=macro", r"\usepackage[a=0.5\textwidth]{pkg}")]
    #[case("1=,2=", r"\usepackage[a=5, b=5pt]{pkg}")]
    fn options(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("simple_empty", r"\begin{asfs} \end{asfs}")]
    #[case("simple_txt", r"\begin{asfs} as \end{asfs}")]
    #[case("simple_txt_alt", r"\begin{asfs*} as \end{asfs*}")]
    #[case("with_args", r"\begin{asfs}[opt]{arg} as \end{asfs}")]
    fn unknown_envs(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("simple_empty", r"\begin{center} \end{center}")]
    #[case("simple_txt", r"\begin{center} as \end{center}")]
    #[case("simple_txt_alt", r"\begin{center*} as \end{center*}")]
    #[case("with_args", r"\begin{tabular}[opt]{arg} as \end{tabular}")]
    #[case("picture", r"\begin{picture}(1,5) as \end{picture}")]
    #[case("picture2", r"\begin{picture}(1,5)(2.4,5.6) as \end{picture}")]
    fn known_envs(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;
        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("simple_empty", r"\begin{equation} \end{equation}")]
    #[case("simple_txt", r"\begin{equation} as \end{equation}")]
    #[case("simple_txt_alt", r"\begin{equation*} as \end{equation*}")]
    #[case("inline", r"$ as $ \( as2 \) \( as3 $")]
    #[case("block", r"$$ as $$ \[ as2 \] $$ as3 \]")]
    fn math_envs(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("+", r"$ 1 + 2 $ ")]
    #[case("^", r"$ 1^2 $ ")]
    #[case("_", r"$ 1_2 $ ")]
    #[case("aligned", r"\begin{equation} a &= b \\ &= c \end{equation}")]
    fn math(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("_", r"$ 1_2 $ ")]
    #[case("block", r"$ 1_{a 2 + 3} $ ")]
    #[case("paren", r"$ 1_(a 2 + 3) $ ")]
    #[case("macro", r"$ \lambda_\mu $ ")]
    #[case("text", r"$ \lambda_asfs $ ")]
    fn subscript(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("^", r"$ 1^2 $ ")]
    #[case("block", r"$ 1^{a 2 + 3} $ ")]
    #[case("paren", r"$ 1^(a 2 + 3) $ ")]
    #[case("macro", r"$ \lambda^\mu $ ")]
    #[case("text", r"$ \lambda^asfs $ ")]
    fn superscript(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("space", r"a b")]
    #[case("newline", "a \n b")]
    #[case("parbreak", "a \n\n b")]
    #[case("linebreak", r"a \\ b")]
    #[case("dashes", r"a - b -- c --- d")]
    #[case("parens", r"a(fsa [sf )]b{f}sa")]
    #[case("ops", r"a+-*/b")]
    #[case("escapes", r"\% \$ \#")]
    fn text(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("{}", r"{{{}}}")]
    #[case("mixed", "{[{()}]}")]
    #[case("math", "${{{}}}$")]
    #[case("math_mixed", "${[{()}]}$")]
    #[case("math_mixed2", "${({[)}]}$")]
    #[case("math_unbalanced", "${({)}]}$")]
    #[case("math_unbalanced2", "$[(])$")]
    fn nested_blocks(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;
        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case(
        "1",
        r"\begin{center} \begin{center} \begin{center} \end{center} \end{center} \end{center}"
    )]
    fn nested_envs(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    #[case("1", "%asfs")]
    #[case("2", r"%\newcommand{\hc}[1]{#1^{\dagger}}")]
    #[case(
        "3",
        r"\newenvironment{exercise} %
        {%
          \textbf{Exercise}%
        }%
        {}%"
    )]
    fn comments(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;

        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }

    #[rstest]
    // we parse \begin{a} as environment, this fails in newenvironment (or similar)
    // macros where it's common to split \begin and \end between arguments
    #[case("unbalanced_begin", r"\newenvironment{c}{\begin{b}}{\end{b}}")]
    // Any(n) takes the n characters from text.
    // But it discards the rest at the moment but it shouldn't

    fn not_working(#[case] name: &str, #[case] input: &str) {
        insta_setup!("{}", name; input);
        let mut p = Parser::from_str(input);
        let stmts = &p.parse().exprs;
        insta::assert_yaml_snapshot!(AstWErrors {
            stmts,
            errors: p.errors()
        });
    }
}
