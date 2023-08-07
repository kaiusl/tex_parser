#![allow(dead_code)]

use core::iter::Peekable;
use core::str::Chars;

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Token<'a> {
    Backslash,
    Text(&'a str),
    MacroName(&'a str),
    Comment(&'a str),
    Number(&'a str),
    Length(&'a str, &'a str),

    ParBreak,  // empty line
    LineBreak, // \\

    // Operators
    Assign,
    Plus,
    Minus,
    Dash,
    DoubleDash,
    TripleDash,
    Ampersand,
    Asterisk,
    Percent,
    Slash,
    Lt,
    Gt,
    Underscore,
    UpArrow,
    Pound,
    InlineMathLimiter,
    InlineMathStartAlt,
    InlineMathEndAlt,
    BlockMathLimiter,
    BlockMathStartAlt,
    BlockMathEndAlt,
    Dot,
    Colon,
    Semicolon,
    Space,
    NewLine,
    NonBreakingSpace,

    // Punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LSquare,
    RSquare,
    Comma,

    // Kws
    Kw(&'a str),

    // Misc
    Illegal,
    Eof,
}

impl<'a> Token<'a> {
    /// Returns `true` if the token is [`Assign`].
    ///
    /// [`Assign`]: Token::Assign
    #[must_use]
    #[inline]
    pub const fn is_assign(&self) -> bool {
        matches!(self, Self::Assign)
    }

    /// Returns `true` if the token is [`Plus`].
    ///
    /// [`Plus`]: Token::Plus
    #[must_use]
    #[inline]
    pub const fn is_plus(&self) -> bool {
        matches!(self, Self::Plus)
    }

    /// Returns `true` if the token is [`Minus`].
    ///
    /// [`Minus`]: Token::Minus
    #[must_use]
    #[inline]
    pub const fn is_minus(&self) -> bool {
        matches!(self, Self::Minus)
    }

    /// Returns `true` if the token is [`Asterisk`].
    ///
    /// [`Asterisk`]: Token::Asterisk
    #[must_use]
    #[inline]
    pub const fn is_asterisk(&self) -> bool {
        matches!(self, Self::Asterisk)
    }

    /// Returns `true` if the token is [`Slash`].
    ///
    /// [`Slash`]: Token::Slash
    #[must_use]
    #[inline]
    pub const fn is_slash(&self) -> bool {
        matches!(self, Self::Slash)
    }

    /// Returns `true` if the token is [`Lt`].
    ///
    /// [`Lt`]: Token::Lt
    #[must_use]
    #[inline]
    pub const fn is_lt(&self) -> bool {
        matches!(self, Self::Lt)
    }

    /// Returns `true` if the token is [`Gt`].
    ///
    /// [`Gt`]: Token::Gt
    #[must_use]
    #[inline]
    pub const fn is_gt(&self) -> bool {
        matches!(self, Self::Gt)
    }

    /// Returns `true` if the token is [`Comma`].
    ///
    /// [`Comma`]: Token::Comma
    #[must_use]
    #[inline]
    pub const fn is_comma(&self) -> bool {
        matches!(self, Self::Comma)
    }

    /// Returns `true` if the token is [`LParen`].
    ///
    /// [`LParen`]: Token::LParen
    #[must_use]
    #[inline]
    pub const fn is_lparen(&self) -> bool {
        matches!(self, Self::LParen)
    }

    /// Returns `true` if the token is [`RParen`].
    ///
    /// [`RParen`]: Token::RParen
    #[must_use]
    #[inline]
    pub const fn is_rparen(&self) -> bool {
        matches!(self, Self::RParen)
    }

    /// Returns `true` if the token is [`LBrace`].
    ///
    /// [`LBrace`]: Token::LBrace
    #[must_use]
    #[inline]
    pub const fn is_lbrace(&self) -> bool {
        matches!(self, Self::LBrace)
    }

    /// Returns `true` if the token is [`RBrace`].
    ///
    /// [`RBrace`]: Token::RBrace
    #[must_use]
    #[inline]
    pub const fn is_rbrace(&self) -> bool {
        matches!(self, Self::RBrace)
    }

    /// Returns `true` if the token is [`Illegal`].
    ///
    /// [`Illegal`]: Token::Illegal
    #[must_use]
    #[inline]
    pub const fn is_illegal(&self) -> bool {
        matches!(self, Self::Illegal)
    }

    /// Returns `true` if the token is [`Eof`].
    ///
    /// [`Eof`]: Token::Eof
    #[must_use]
    #[inline]
    pub const fn is_eof(&self) -> bool {
        matches!(self, Self::Eof)
    }

    /// Returns `true` if the token is [`LSquare`].
    ///
    /// [`LSquare`]: Token::LSquare
    #[must_use]
    #[inline]
    pub const fn is_lsquare(&self) -> bool {
        matches!(self, Self::LSquare)
    }

    /// Returns `true` if the token is [`RSquare`].
    ///
    /// [`RSquare`]: Token::RSquare
    #[must_use]
    #[inline]
    pub const fn is_rsquare(&self) -> bool {
        matches!(self, Self::RSquare)
    }

    /// Returns `true` if the token is [`Backslash`].
    ///
    /// [`Backslash`]: Token::Backslash
    #[must_use]
    pub fn is_backslash(&self) -> bool {
        matches!(self, Self::Backslash)
    }

    /// Returns `true` if the token is [`Text`].
    ///
    /// [`Text`]: Token::Text
    #[must_use]
    pub fn is_text(&self) -> bool {
        matches!(self, Self::Text(..))
    }

    /// Returns `true` if the token is [`ParBreak`].
    ///
    /// [`ParBreak`]: Token::ParBreak
    #[must_use]
    pub fn is_par_break(&self) -> bool {
        matches!(self, Self::ParBreak)
    }

    /// Returns `true` if the token is [`LineBreak`].
    ///
    /// [`LineBreak`]: Token::LineBreak
    #[must_use]
    pub fn is_line_break(&self) -> bool {
        matches!(self, Self::LineBreak)
    }

    /// Returns `true` if the token is [`Ampersand`].
    ///
    /// [`Ampersand`]: Token::Ampersand
    #[must_use]
    pub fn is_ampersand(&self) -> bool {
        matches!(self, Self::Ampersand)
    }

    /// Returns `true` if the token is [`Percent`].
    ///
    /// [`Percent`]: Token::Percent
    #[must_use]
    pub fn is_percent(&self) -> bool {
        matches!(self, Self::Percent)
    }

    /// Returns `true` if the token is [`Underscore`].
    ///
    /// [`Underscore`]: Token::Underscore
    #[must_use]
    pub fn is_underscore(&self) -> bool {
        matches!(self, Self::Underscore)
    }

    /// Returns `true` if the token is [`UpArrow`].
    ///
    /// [`UpArrow`]: Token::UpArrow
    #[must_use]
    pub fn is_up_arrow(&self) -> bool {
        matches!(self, Self::UpArrow)
    }

    /// Returns `true` if the token is [`Pound`].
    ///
    /// [`Pound`]: Token::Pound
    #[must_use]
    pub fn is_pound(&self) -> bool {
        matches!(self, Self::Pound)
    }

    /// Returns `true` if the token is [`Space`].
    ///
    /// [`Space`]: Token::Space
    #[must_use]
    pub fn is_space(&self) -> bool {
        matches!(self, Self::Space)
    }

    /// Returns `true` if the token is [`NewLine`].
    ///
    /// [`NewLine`]: Token::NewLine
    #[must_use]
    pub fn is_new_line(&self) -> bool {
        matches!(self, Self::NewLine)
    }

    pub fn as_text(&self) -> Option<&&'a str> {
        if let Self::Text(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the token is [`DoubleDollar`].
    ///
    /// [`DoubleDollar`]: Token::DoubleDollar
    #[must_use]
    pub fn is_double_dollar(&self) -> bool {
        matches!(self, Self::BlockMathLimiter)
    }

    /// Returns `true` if the token is [`Dollar`].
    ///
    /// [`Dollar`]: Token::Dollar
    #[must_use]
    pub fn is_dollar(&self) -> bool {
        matches!(self, Self::InlineMathLimiter)
    }

    /// Returns `true` if the token is [`InlineMathStartAlt`].
    ///
    /// [`InlineMathStartAlt`]: Token::InlineMathStartAlt
    #[must_use]
    pub fn is_inline_math_start_alt(&self) -> bool {
        matches!(self, Self::InlineMathStartAlt)
    }

    /// Returns `true` if the token is [`InlineMathEndAlt`].
    ///
    /// [`InlineMathEndAlt`]: Token::InlineMathEndAlt
    #[must_use]
    pub fn is_inline_math_end_alt(&self) -> bool {
        matches!(self, Self::InlineMathEndAlt)
    }

    /// Returns `true` if the token is [`BlockMathStartAlt`].
    ///
    /// [`BlockMathStartAlt`]: Token::BlockMathStartAlt
    #[must_use]
    pub fn is_block_math_start_alt(&self) -> bool {
        matches!(self, Self::BlockMathStartAlt)
    }

    /// Returns `true` if the token is [`BlockMathEndAlt`].
    ///
    /// [`BlockMathEndAlt`]: Token::BlockMathEndAlt
    #[must_use]
    pub fn is_block_math_end_alt(&self) -> bool {
        matches!(self, Self::BlockMathEndAlt)
    }

    /// Returns `true` if the token is [`BlockMathLimiter`].
    ///
    /// [`BlockMathLimiter`]: Token::BlockMathLimiter
    #[must_use]
    pub fn is_block_math_limiter(&self) -> bool {
        matches!(self, Self::BlockMathLimiter)
    }

    /// Returns `true` if the token is [`InlineMathLimiter`].
    ///
    /// [`InlineMathLimiter`]: Token::InlineMathLimiter
    #[must_use]
    pub fn is_inline_math_limiter(&self) -> bool {
        matches!(self, Self::InlineMathLimiter)
    }

    /// Returns `true` if the token is [`MacroName`].
    ///
    /// [`MacroName`]: Token::MacroName
    #[must_use]
    pub fn is_macro_name(&self) -> bool {
        matches!(self, Self::MacroName(..))
    }

    pub fn as_macro_name(&self) -> Option<&&'a str> {
        if let Self::MacroName(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the token is [`Length`].
    ///
    /// [`Length`]: Token::Length
    #[must_use]
    pub fn is_length(&self) -> bool {
        matches!(self, Self::Length(..))
    }

    /// Returns `true` if the token is [`Number`].
    ///
    /// [`Number`]: Token::Number
    #[must_use]
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(..))
    }

    /// Returns `true` if the token is [`Comment`].
    ///
    /// [`Comment`]: Token::Comment
    #[must_use]
    pub fn is_comment(&self) -> bool {
        matches!(self, Self::Comment(..))
    }

    pub fn as_comment(&self) -> Option<&&'a str> {
        if let Self::Comment(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_number(&self) -> Option<&&'a str> {
        if let Self::Number(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the token is [`NonBreakingSpace`].
    ///
    /// [`NonBreakingSpace`]: Token::NonBreakingSpace
    #[must_use]
    pub fn is_non_breaking_space(&self) -> bool {
        matches!(self, Self::NonBreakingSpace)
    }

    /// Returns `true` if the token is [`Semicolon`].
    ///
    /// [`Semicolon`]: Token::Semicolon
    #[must_use]
    pub fn is_semicolon(&self) -> bool {
        matches!(self, Self::Semicolon)
    }

    /// Returns `true` if the token is [`Colon`].
    ///
    /// [`Colon`]: Token::Colon
    #[must_use]
    pub fn is_colon(&self) -> bool {
        matches!(self, Self::Colon)
    }

    /// Returns `true` if the token is [`Dot`].
    ///
    /// [`Dot`]: Token::Dot
    #[must_use]
    pub fn is_dot(&self) -> bool {
        matches!(self, Self::Dot)
    }

    /// Returns `true` if the token is [`Kw`].
    ///
    /// [`Kw`]: Token::Kw
    #[must_use]
    pub fn is_kw(&self) -> bool {
        matches!(self, Self::Kw(..))
    }

    pub fn try_into_kw(self) -> Result<&'a str, Self> {
        if let Self::Kw(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn as_kw(&self) -> Option<&&'a str> {
        if let Self::Kw(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    input: &'a str,
    chars: Peekable<Chars<'a>>,
    /// current position in input (poInts to current char)
    pos: usize,
    /// current char under examination
    char: char,
}

const NULL_CHAR: char = '\0';

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        let mut chars = input.chars().peekable();
        let first = chars.next().unwrap_or(NULL_CHAR);
        Self {
            input,
            chars,
            pos: 0,
            char: first,
        }
    }

    fn maybe_two_char_token(
        &mut self,
        expected_char: char,
        two_char_token: Token<'static>,
        fallback: Token<'static>,
    ) -> Token<'static> {
        match self.peek_next_char() {
            Some(&char) if char == expected_char => {
                self.read_next_char();
                two_char_token
            }
            _ => fallback,
        }
    }

    fn create_two_token(&mut self, tok: Token<'a>) -> Token<'a> {
        self.read_next_char();
        tok
    }

    fn peek_token(&mut self) -> Token<'a> {
        let mut c = self.clone();
        c.next_token()
    }

    pub fn next_token(&mut self) -> Token<'a> {
        self.skip_linefeed();

        let token = match self.char {
            '=' => Token::Assign,
            '+' => Token::Plus,
            ',' => Token::Comma,
            '(' => Token::LParen,
            ')' => Token::RParen,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            '[' => Token::LSquare,
            ']' => Token::RSquare,
            '-' => Token::Minus,
            ';' => Token::Semicolon,
            '.' => Token::Dot,
            ':' => Token::Colon,
            '*' => Token::Asterisk,
            '/' => Token::Slash,
            '<' => Token::Lt,
            '>' => Token::Gt,
            '^' => Token::UpArrow,
            '~' => Token::NonBreakingSpace,
            '_' => Token::Underscore,
            '#' => Token::Pound,
            '\\' => match self.peek_next_char() {
                Some(&char) => match char {
                    '(' => self.create_two_token(Token::InlineMathStartAlt),
                    ')' => self.create_two_token(Token::InlineMathEndAlt),
                    '[' => self.create_two_token(Token::BlockMathStartAlt),
                    ']' => self.create_two_token(Token::BlockMathEndAlt),
                    '`' | '\'' | '^' | '"' | '~' | '=' | '.' | '!' | ';' | ':' | ',' | ' '
                    | '\\' | '%' | '$' | '#' | '&' | '{' | '}' | '*' | '-' | '_' | '/' => self
                        .create_two_token(Token::MacroName(
                            &self.input
                                [(self.pos + '\\'.len_utf8())..=(self.pos + char.len_utf8())],
                        )),

                    ch if ch.is_ascii_alphabetic() || ch == '@' => {
                        self.read_next_char();
                        let ident = self.read_ident();
                        return Token::MacroName(ident);
                    }
                    _ => Token::Backslash,
                },
                _ => Token::Backslash,
            },
            '$' => {
                self.maybe_two_char_token('$', Token::BlockMathLimiter, Token::InlineMathLimiter)
            }
            '\n' => {
                self.read_next_char();
                self.skip_whitespace();
                self.skip_linefeed();
                if self.char == '\n' {
                    while self.char == '\n' {
                        self.read_next_char();
                        self.skip_whitespace();
                        self.skip_linefeed();
                    }
                    return Token::ParBreak;
                } else {
                    return Token::NewLine;
                }
            }

            '%' => {
                let comment = self.read_comment();
                return Token::Comment(comment);
            }
            ' ' | '\t' => {
                self.skip_whitespace(); // Remove double spaces
                if self.char == '\n' {
                    return self.next_token(); // remove spaces at line end
                }
                return Token::Space;
            }
            '&' => Token::Ampersand,
            ch if ch.is_ascii_digit() => return self.number_to_token(),
            ch if !self.is_special(ch) => {
                return self.read_text();
            }

            NULL_CHAR => Token::Eof,
            t => {
                println!("ILLEGAL TOKEN: {}", t);
                Token::Illegal
            }
        };

        self.read_next_char();
        token
    }

    fn number_to_token(&mut self) -> Token<'a> {
        let number = self.read_number();
        let mut chars = self.chars.clone();
        let mut start_pos = self.pos;
        let mut pos = start_pos;
        let mut char = self.char;
        while char == ' ' || char == '\t' || char == '\n' {
            pos += char.len_utf8();
            start_pos = pos;
            char = chars.next().unwrap_or(NULL_CHAR);
        }
        let mut is_true_len = false;
        let mut true_end = 0;
        while char.is_alphabetic() {
            pos += char.len_utf8();
            char = chars.next().unwrap_or(NULL_CHAR);
            let maybe_unit = if is_true_len {
                &self.input[true_end..pos]
            } else {
                &self.input[start_pos..pos]
            };
            if maybe_unit == "true" {
                true_end = pos;
                while matches!(char, ' ' | '\t' | '\n') {
                    pos += char.len_utf8();
                    true_end = pos;
                    char = chars.next().unwrap_or(NULL_CHAR);
                }
                is_true_len = true;
                continue;
            }

            if let "pt" | "pc" | "bp" | "in" | "cm" | "mm" | "dd" | "cc" | "sp" | "ex" | "em"
            | "mu" | "fil" | "fill" | "filll" = maybe_unit
            {
                while self.char == ' ' || self.char == '\t' || self.char == '\n' {
                    self.read_next_char();
                }
                for _ in 0..pos - start_pos {
                    self.read_next_char();
                }

                return Token::Length(number, &self.input[start_pos..pos]);
            }
        }
        Token::Number(number)
    }

    fn peek_after_newline_and_spaces(&mut self) -> Option<char> {
        self.chars
            .clone()
            .find(|&c| !(c == ' ' || c == '\n' || c == '\t'))
    }

    fn is_special(&self, c: char) -> bool {
        matches!(
            c,
            '{' | '}'
                | '*'
                | '\\'
                | '_'
                | '^'
                | '\n'
                | '#'
                | '%'
                | '\t'
                | '&'
                | '$'
                | ' '
                | '~'
                | NULL_CHAR
                | '+'
                | '/'
                | '<'
                | '>'
                | ':'
                | '.'
                | ';'
                | '('
                | ')'
                | '['
                | ']'
                | ','
                | '='
                | '-'
        )
    }

    fn skip_linefeed(&mut self) {
        while self.char == '\r' {
            self.read_next_char();
        }
    }

    fn skip_whitespace(&mut self) {
        while self.char == ' ' || self.char == '\t' {
            self.read_next_char();
        }
    }

    fn skip_whitespace_and_newline(&mut self) {
        while self.char == ' ' || self.char == '\t' || self.char == '\n' || self.char == '\r' {
            self.read_next_char();
        }
    }

    fn read_ident(&mut self) -> &'a str {
        let start_pos = self.pos;

        while self.char.is_ascii_alphabetic() || self.char == '@' {
            self.read_next_char();
        }

        &self.input[start_pos..self.pos]
    }

    fn read_text(&mut self) -> Token<'a> {
        let start_pos = self.pos;
        while !self.is_special(self.char) {
            self.read_next_char();

            let txt = &self.input[start_pos..self.pos];
            match txt {
                "width" | "height" | "at" | "by" | "depth" | "plus" | "minus" | "to" | "spread"
                | "true" | "false" => return Token::Kw(txt),
                _ => {}
            }
        }

        Token::Text(&self.input[start_pos..self.pos])
    }

    fn read_comment(&mut self) -> &'a str {
        // Comment is: rest of the line + newline + spaces/tabs at the beginning of next line

        let start_pos = self.pos;
        while self.char != '\n' && self.char != NULL_CHAR {
            self.read_next_char();
        }

        if self.char == '\n' {
            self.read_next_char();
            // skin spaces at the beginning of next line
            while (self.char == ' ' || self.char == '\t') && self.char != NULL_CHAR {
                self.read_next_char();
            }
        }

        &self.input[start_pos..self.pos]
    }

    fn is_ident_char(ch: char) -> bool {
        ch.is_alphabetic() || ch == '_'
    }

    fn read_next_char(&mut self) {
        self.pos += self.char.len_utf8();
        self.char = self.chars.next().unwrap_or(NULL_CHAR);
    }

    fn read_number(&mut self) -> &'a str {
        let start_pos = self.pos;
        // if self.char == '-' {
        //     self.read_next_char();
        // }
        while self.char.is_ascii_digit() {
            self.read_next_char();
        }

        let mut is_float = false;
        loop {
            if self.char.is_ascii_digit() {
                self.read_next_char();
            } else if !is_float // If is_float, there already was an ., there cannot be two . in a number
                && self.char == '.'
                && self
                    .peek_next_char()
                    .map(|ch| ch.is_ascii_digit())
                    .unwrap_or(false)
            // After . we expect more digits
            {
                // We have a float, keep parsing
                is_float = true;
                self.read_next_char();
            } else {
                break;
            }
        }

        &self.input[start_pos..self.pos]
    }

    fn peek_next_char(&mut self) -> Option<&char> {
        self.chars.peek()
    }
}

#[derive(Debug, Clone)]
pub struct MultipeekLexer<'a> {
    lexer: Lexer<'a>,
    buf: VecDeque<Token<'a>>,
}

impl<'a> MultipeekLexer<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer,
            buf: VecDeque::new(),
        }
    }

    pub fn next(&mut self) -> Token<'a> {
        self.buf
            .pop_front()
            .unwrap_or_else(|| self.lexer.next_token())
    }

    pub fn peek(&mut self) -> &Token<'a> {
        self.peek_nth(0)
    }

    pub fn peek_mut(&mut self) -> &mut Token<'a> {
        self.peek_nth_mut(0)
    }

    pub fn peek_nth(&mut self, n: usize) -> &Token<'a> {
        while n >= self.buf.len() {
            let item = self.lexer.next_token();
            self.buf.push_back(item);
        }
        &self.buf[n]
    }

    pub fn peek_nth_mut(&mut self, n: usize) -> &mut Token<'a> {
        while n >= self.buf.len() {
            let item = self.lexer.next_token();
            self.buf.push_back(item);
        }
        &mut self.buf[n]
    }

    pub fn peek_after_newline_and_spaces(&mut self) -> (usize, Token<'a>) {
        let mut i = 0;
        loop {
            let peeked = self.peek_nth(i);
            if !matches!(peeked, Token::Space | Token::NewLine) {
                return (i, peeked.clone());
            }
            i += 1;
        }
    }
}
