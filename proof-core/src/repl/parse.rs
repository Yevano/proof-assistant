use std::{
    fmt::{Display, Formatter},
    iter,
    rc::Rc,
};

use super::eval::BinderType;

use crate::result::Result;

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumn {
    line: usize,
    column: usize,
}

impl LineColumn {
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }

    pub fn column(&self) -> usize {
        self.column
    }

    pub fn line(&self) -> usize {
        self.line
    }
}

impl Display for LineColumn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourcePos {
    line_column: LineColumn,
    source_index: usize,
}

impl SourcePos {
    pub fn new(line_column: LineColumn, source_index: usize) -> Self {
        Self {
            line_column,
            source_index,
        }
    }

    pub fn line_column(&self) -> LineColumn {
        self.line_column
    }

    pub fn source_index(&self) -> usize {
        self.source_index
    }

    pub fn add_columns(&self, columns: usize) -> Self {
        Self {
            line_column: LineColumn::new(self.line_column.line, self.line_column.column + columns),
            source_index: self.source_index + columns,
        }
    }

    pub fn add_columns_mut(&mut self, columns: usize) {
        self.line_column.column += columns;
        self.source_index += columns;
    }

    pub fn add_lines(&self, lines: usize) -> Self {
        Self {
            line_column: LineColumn::new(self.line_column.line + lines, 0),
            source_index: self.source_index + lines,
        }
    }

    pub fn add_lines_mut(&mut self, lines: usize) {
        self.line_column.line += lines;
        self.line_column.column = 0;
        self.source_index += lines;
    }

    // Find the SourcePos of the end of the input slice
    pub fn find_end_of_str(source: &[char], start_pos: SourcePos) -> Self {
        let SourcePos {
            line_column:
                LineColumn {
                    mut line,
                    mut column,
                },
            ..
        } = start_pos;
        for c in source[start_pos.source_index..].iter() {
            if *c == '\n' {
                line += 1;
                column = 0;
            } else {
                column += 1;
            }
        }
        Self::new(LineColumn::new(line, column), source.len())
    }
}

impl Display for SourcePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.line_column)
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub struct SourceRange {
    begin: SourcePos,
    end: SourcePos,
}

impl SourceRange {
    pub fn new(begin: SourcePos, end: SourcePos) -> SourceRange {
        Self { begin, end }
    }

    pub fn begin(&self) -> SourcePos {
        self.begin
    }

    pub fn end(&self) -> SourcePos {
        self.end
    }

    pub fn new_from_begin_and_columns(begin: SourcePos, columns: usize) -> SourceRange {
        Self {
            begin,
            end: begin.add_columns(columns),
        }
    }

    pub fn len(&self) -> usize {
        self.end.source_index - self.begin.source_index
    }

    pub fn lines_spanned(&self) -> usize {
        self.end.line_column.line - self.begin.line_column.line
    }
}

impl Display for SourceRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-{}", self.begin, self.end)
    }
}

trait HasSourcePos {
    fn source_pos(&self) -> SourcePos;
}

trait HasSourceRange {
    fn source_range(&self) -> SourceRange;
    fn len(&self) -> usize {
        self.source_range().end.source_index - self.source_range().begin.source_index
    }
}

impl<T: HasSourceRange> HasSourcePos for T {
    fn source_pos(&self) -> SourcePos {
        self.source_range().begin
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenData {
    Ident(String),
    Period,
    RightArrow,
    Colon,
    LeftParen,
    RightParen,
    ColonEq,
    QuestionMark,
    Asterisk,
}

impl Display for TokenData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TokenData::Ident(s) => s.as_str(),
            TokenData::Period => ".",
            TokenData::RightArrow => "=>",
            TokenData::Colon => ":",
            TokenData::LeftParen => "(",
            TokenData::RightParen => ")",
            TokenData::ColonEq => ":=",
            TokenData::QuestionMark => "?",
            TokenData::Asterisk => "*",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    data: TokenData,
    begin: SourcePos,
}

impl Token {
    fn new(data: TokenData, begin: SourcePos) -> Self {
        Self { data, begin }
    }

    fn data(&self) -> &TokenData {
        &self.data
    }

    pub fn begin(&self) -> &SourcePos {
        &self.begin
    }
}

impl HasSourceRange for Token {
    fn source_range(&self) -> SourceRange {
        let columns = match &self.data {
            TokenData::Ident(ident_string) => ident_string.len(),
            TokenData::Period => 1,
            TokenData::RightArrow => 2,
            TokenData::Colon => 1,
            TokenData::LeftParen => 1,
            TokenData::RightParen => 1,
            TokenData::ColonEq => 2,
            TokenData::QuestionMark => 1,
            TokenData::Asterisk => 1,
        };
        SourceRange::new_from_begin_and_columns(self.begin, columns)
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display_string = match &self.data {
            TokenData::Ident(ident_string) => ident_string.as_str(),
            TokenData::Period => ".",
            TokenData::RightArrow => "=>",
            TokenData::Colon => ":",
            TokenData::LeftParen => "(",
            TokenData::RightParen => ")",
            TokenData::ColonEq => ":=",
            TokenData::QuestionMark => "?",
            TokenData::Asterisk => "*",
        };
        write!(f, "{}", display_string)
    }
}

pub trait Parse
where
    Self: Sized,
{
    fn parse(tokens: &mut ParseStream) -> Result<Self>;
}

#[derive(Default, Debug)]
struct TokenBuffer {
    buffered_tokens: Vec<Token>,
}

impl TokenBuffer {
    fn new() -> Self {
        Self {
            ..Default::default()
        }
    }

    fn len(&self) -> usize {
        self.buffered_tokens.len()
    }

    fn back_position(&self) -> TokenBufferPosition {
        TokenBufferPosition(self.len())
    }

    fn source_pos_at_back(&self) -> SourcePos {
        match &self.buffered_tokens[..] {
            [.., back] => back.source_range().end(),
            [] => Default::default(),
        }
    }

    fn skip_whitespace(last_source_pos: &mut SourcePos, remaining_input_slice: &mut &[char]) {
        while let [next_input_char, rest @ ..] = remaining_input_slice && next_input_char.is_whitespace() {
            match next_input_char {
                '\n' => { last_source_pos.add_lines_mut(1); }
                _ => { last_source_pos.add_columns_mut(1); }
            };
            *remaining_input_slice = rest;
        }
    }

    fn read_ident<'a>(
        last_source_pos: &mut SourcePos,
        remaining_input_slice: &'a mut &[char],
    ) -> &'a [char] {
        let initial_input_slice = &remaining_input_slice[..];
        let mut amount_of_chars_read = 0usize;
        loop {
            match remaining_input_slice {
                ['.' | '>' | ':' | '=' | '(' | ')', ..] => break,
                [front, ..] if front.is_whitespace() => break,
                [_, rest @ ..] => {
                    last_source_pos.add_columns_mut(1);
                    *remaining_input_slice = rest
                }
                [] => break,
            }
            amount_of_chars_read += 1
        }
        &initial_input_slice[..amount_of_chars_read]
    }

    fn push_token_from_input<'a>(
        &'a mut self,
        remaining_input_slice: &'a mut &[char],
    ) -> Option<&Token> {
        let mut last_source_pos = self.source_pos_at_back();
        Self::skip_whitespace(&mut last_source_pos, remaining_input_slice);

        match remaining_input_slice {
            ['.', ..] => Some(Token::new(TokenData::Period, last_source_pos)),
            ['=', '>', ..] => Some(Token::new(TokenData::RightArrow, last_source_pos)),
            [':', '=', ..] => Some(Token::new(TokenData::ColonEq, last_source_pos)),
            [':', ..] => Some(Token::new(TokenData::Colon, last_source_pos)),
            ['(', ..] => Some(Token::new(TokenData::LeftParen, last_source_pos)),
            [')', ..] => Some(Token::new(TokenData::RightParen, last_source_pos)),
            ['?', ..] => Some(Token::new(TokenData::QuestionMark, last_source_pos)),
            ['*', ..] => Some(Token::new(TokenData::Asterisk, last_source_pos)),
            [] => None,
            [_, ..] => {
                let front_line_column = last_source_pos;
                let ident_slice = Self::read_ident(&mut last_source_pos, remaining_input_slice);
                if ident_slice.is_empty() {
                    None
                } else {
                    Some(Token::new(
                        TokenData::Ident(ident_slice.iter().collect()),
                        front_line_column,
                    ))
                }
            }
        }
        .map(|token| {
            self.buffered_tokens.push(token);
            self.buffered_tokens.last().unwrap()
        })
        .inspect(|token| {
            if !matches!(token.data(), TokenData::Ident(_)) {
                *remaining_input_slice = &remaining_input_slice[token.len()..]
            }
        })
    }
}

#[derive(Default, Debug, Clone, Copy)]
struct TokenBufferPosition(usize);

/// A struct which holds all the information required to generate tokens from
/// a slice of characters, as well as caching previously generated tokens to
/// make parsing easier.
///
/// The mechanism for selecting a (cached) token is as follows:
/// The `ParseStream` holds a growable array of `Token`s. It also holds a "lookback"
/// index. The token which is accessed when calling `ParseStream#peek` is such that
/// for a token buffer of length `n`, it is located in the buffer at index `n - lookback_index`.
/// This can be represented visually like so:
///
/// ```plain
///              unparsed region (lookback_index = 0 will attempt to peek here and trigger the parsing of a new token)
///                  |
///                  v
/// [a, b, c, d, e, ...]
///        ^
///        |
///    this token (at index 2) is peeked if lookback_index = 3
/// ```
#[derive(Default, Debug)]
pub struct ParseStream<'a> {
    input_slice: &'a [char],
    token_buffer: TokenBuffer,
    lookback_index: usize,
}

impl<'a> ParseStream<'a> {
    pub fn new(input_slice: &'a [char]) -> Self {
        Self {
            input_slice,
            token_buffer: TokenBuffer::new(),
            lookback_index: 0,
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if self.lookback_index == 0 {
            let pushed_token = self
                .token_buffer
                .push_token_from_input(&mut self.input_slice);
            if pushed_token.is_some() {
                self.lookback_index = 1;
            }
            pushed_token
        } else {
            let buffered_tokens = self.token_buffer.buffered_tokens.as_slice();
            buffered_tokens
                .len()
                .checked_sub(self.lookback_index)
                .map(|peek_index| &buffered_tokens[peek_index])
        }
    }

    pub fn next(&mut self) -> Option<&Token> {
        if self.lookback_index == 0 {
            self.token_buffer
                .push_token_from_input(&mut self.input_slice)
        } else {
            let buffered_tokens = self.token_buffer.buffered_tokens.as_slice();
            let token = buffered_tokens
                .len()
                .checked_sub(self.lookback_index)
                .map(|peek_index| &buffered_tokens[peek_index]);
            if token.is_some() {
                self.lookback_index -= 1;
            }
            token
        }
    }

    pub fn next_if(&mut self, token_data: TokenData) -> Option<&Token> {
        if let Some(token) = self.peek() && *token.data() == token_data {
            self.next()
        } else {
            None
        }
    }

    pub fn prev(&mut self) {
        if self.token_buffer.buffered_tokens.len() > self.lookback_index {
            self.lookback_index += 1;
        }
    }

    pub fn expect_next(&mut self, token_data: TokenData) -> Result<&Token> {
        let line_column = self.source_pos_at_back();
        let token = self.next();
        if let Some(token) = token {
            if *token.data() == token_data {
                Ok(token)
            } else {
                error!(
                    "expected token `{}` at {}, got `{}`",
                    token_data,
                    token.source_pos(),
                    token.data()
                )
                .into()
            }
        } else {
            error!(
                "expected token `{}` at {}, got end of input",
                token_data, line_column
            )
            .into()
        }
    }

    fn source_pos_at_back(&self) -> SourcePos {
        self.token_buffer.source_pos_at_back()
    }

    fn token_buffer_position(&self) -> TokenBufferPosition {
        TokenBufferPosition(self.token_buffer.back_position().0 - self.lookback_index)
    }

    /// Get the lookback index required to peek at the token at the given position.
    /// E.g., if the given position is equal to `self.token_buffer.back_position()`, then
    fn lookback_index_of_position(&self, position: TokenBufferPosition) -> usize {
        self.token_buffer.len() - position.0
    }

    fn seek_to_known_position(&mut self, position: TokenBufferPosition) {
        self.lookback_index = self.lookback_index_of_position(position)
    }

    /// Tries to parse tokens. Resets the stream position if parsing fails.
    pub fn try_parse<P: Parse>(&mut self) -> Result<P> {
        let begin_token_buffer_position = self.token_buffer_position();
        let parse_result = P::parse(self);
        match parse_result {
            Ok(_) => {}
            Err(_) => self.seek_to_known_position(begin_token_buffer_position),
        }
        parse_result
    }
}

pub struct Diagnostic {
    message: String,
    source_range: SourceRange,
}

impl Diagnostic {
    pub fn new(message: String, source_range: SourceRange) -> Self {
        Self {
            message,
            source_range,
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn source_range(&self) -> &SourceRange {
        &self.source_range
    }

    pub fn display(&self, source: &[char]) -> String {
        let begin_line_index = self.source_range.begin().source_index()
            - self.source_range.begin().line_column().column();
        let line = source[begin_line_index..]
            .iter()
            .take_while(|c| **c != '\n')
            .collect::<String>();
        let mut display = String::new();
        display.push_str(&self.message);
        display.push('\n');
        display.push_str(&line);
        display.push_str("\n");
        let source_len_single_line: usize;
        if self.source_range.end.line_column.line != self.source_range.begin.line_column.line {
            source_len_single_line = line.len() - self.source_range.begin.line_column.column;
        } else {
            source_len_single_line = self.source_range.len();
        }
        display.push_str(&" ".repeat(self.source_range.begin.line_column.column));
        display.push_str(&"^".repeat(source_len_single_line));
        display
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_stream() {
        let mut input_vec = "abcd := ?a".chars().collect::<Vec<char>>();
        let input_slice = input_vec.as_mut_slice();
        let mut ps = ParseStream::new(input_slice);
        ps.prev();
        assert_eq!(*ps.peek().unwrap().data(), TokenData::Ident("abcd".into()));
        assert_eq!(*ps.peek().unwrap().data(), TokenData::Ident("abcd".into()));
        assert_eq!(*ps.next().unwrap().data(), TokenData::Ident("abcd".into()));
        assert_eq!(*ps.next().unwrap().data(), TokenData::ColonEq);
        assert_eq!(*ps.next().unwrap().data(), TokenData::QuestionMark);
        ps.prev();
        assert_eq!(*ps.next().unwrap().data(), TokenData::QuestionMark);
        assert_eq!(*ps.next().unwrap().data(), TokenData::Ident("a".into()));
        assert!(ps.next().is_none());
        assert!(ps.peek().is_none());
        ps.prev();
        assert_eq!(*ps.peek().unwrap().data(), TokenData::Ident("a".into()));
        assert_eq!(*ps.next().unwrap().data(), TokenData::Ident("a".into()));
        assert!(ps.peek().is_none());
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HoleTree {
    ident: IdentTree,
    source_pos: SourcePos,
}

impl HoleTree {
    pub fn ident(&self) -> &IdentTree {
        &self.ident
    }

    pub fn source_pos(&self) -> &SourcePos {
        &self.source_pos
    }
}

impl Display for HoleTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.ident)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentTree {
    ident: String,
    source_pos: SourcePos,
}

impl IdentTree {
    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn source_pos(&self) -> &SourcePos {
        &self.source_pos
    }
}

impl Display for IdentTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ident)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct SortTree {
    universe: u32,
}

impl SortTree {
    pub fn universe(&self) -> u32 {
        self.universe
    }
}

impl Display for SortTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Type{}", self.universe)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApplicationTree {
    applicant: Rc<ExpressionTree>,
    applicand: Rc<ExpressionTree>,
}

impl ApplicationTree {
    pub fn applicant(&self) -> &Rc<ExpressionTree> {
        &self.applicant
    }

    pub fn applicand(&self) -> &Rc<ExpressionTree> {
        &self.applicand
    }
}

impl Display for ApplicationTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}) ({})", self.applicant, self.applicand)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinderTree {
    binder_type: BinderType,
    variable_name: IdentTree,
    variable_type: Rc<ExpressionTree>,
    body: Rc<ExpressionTree>,
}

impl BinderTree {
    pub fn binder_type(&self) -> BinderType {
        self.binder_type
    }

    pub fn variable_name(&self) -> &IdentTree {
        &self.variable_name
    }

    pub fn variable_type(&self) -> &Rc<ExpressionTree> {
        &self.variable_type
    }

    pub fn body(&self) -> &Rc<ExpressionTree> {
        &self.body
    }
}

impl Display for BinderTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} : [{}] . {}",
            self.binder_type, self.variable_name, self.variable_type, self.body
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrowTree {
    parameter_type: Rc<ExpressionTree>,
    return_type: Rc<ExpressionTree>,
}

impl ArrowTree {
    pub fn parameter_type(&self) -> &Rc<ExpressionTree> {
        &self.parameter_type
    }

    pub fn return_type(&self) -> &Rc<ExpressionTree> {
        &self.return_type
    }
}

impl Display for ArrowTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", self.parameter_type, self.return_type)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionTree {
    Hole(HoleTree),
    Variable(IdentTree),
    Sort(SortTree),
    Application(ApplicationTree),
    Binder(BinderTree),
    Arrow(ArrowTree),
}

impl Display for ExpressionTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpressionTree::Hole(hole_tree) => write!(f, "{}", hole_tree),
            ExpressionTree::Variable(ident_tree) => write!(f, "{}", ident_tree),
            ExpressionTree::Sort(sort_tree) => write!(f, "{}", sort_tree),
            ExpressionTree::Application(application_tree) => write!(f, "{}", application_tree),
            ExpressionTree::Binder(binder_tree) => write!(f, "{}", binder_tree),
            ExpressionTree::Arrow(arrow_tree) => write!(f, "{}", arrow_tree),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentTree {
    name: IdentTree,
    value: ExpressionTree,
}

impl AssignmentTree {
    pub fn name(&self) -> &IdentTree {
        &self.name
    }

    pub fn value(&self) -> &ExpressionTree {
        &self.value
    }
}

impl Display for AssignmentTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := {}", self.name, self.value)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseTree {
    Expression(ExpressionTree),
    Assignment(AssignmentTree),
}

impl Display for ParseTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseTree::Expression(expression_tree) => write!(f, "{}", expression_tree),
            ParseTree::Assignment(assignment_tree) => write!(f, "{}", assignment_tree),
        }
    }
}

impl Parse for ParseTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        if let Ok(assignment_tree) = tokens.try_parse::<AssignmentTree>() {
            Ok(ParseTree::Assignment(assignment_tree))
        } else {
            let expression_tree = tokens.try_parse::<ExpressionTree>()?;
            Ok(ParseTree::Expression(expression_tree))
        }
    }
}

impl Parse for ExpressionTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        let mut expressions = iter::repeat_with(|| {
            if let Ok(binder_tree) = tokens.try_parse::<BinderTree>() {
                Ok(ExpressionTree::Binder(binder_tree))
            } else if let Ok(sort_tree) = tokens.try_parse::<SortTree>() {
                Ok(ExpressionTree::Sort(sort_tree))
            } else if let Ok(ident_tree) = tokens.try_parse::<IdentTree>() {
                Ok(ExpressionTree::Variable(ident_tree))
            } else if let Ok(hole_tree) = tokens.try_parse::<HoleTree>() {
                Ok(ExpressionTree::Hole(hole_tree))
            } else if let Some(token) = tokens.peek() && *token.data() == TokenData::LeftParen {
                tokens.expect_next(TokenData::LeftParen)?;
                let expression_tree = tokens.try_parse::<ExpressionTree>()?;
                tokens.expect_next(TokenData::RightParen)?;
                Ok(expression_tree)
            } else {
                error!("todo error when no match for expression tree").into()
            }
        });

        let first_result = expressions.next().unwrap()?;

        let expressions = iter::once(Ok(first_result)).chain(expressions);

        let e = expressions
            .take_while(Result::is_ok)
            .map(Result::unwrap)
            .reduce(|lhs, rhs| {
                let application_tree = ApplicationTree {
                    applicant: lhs.into(),
                    applicand: rhs.into(),
                };
                ExpressionTree::Application(application_tree)
            })
            .unwrap();

        if let Some(_) = tokens.next_if(TokenData::RightArrow) {
            let return_type = tokens.try_parse::<ExpressionTree>()?;
            let arrow_tree = ArrowTree {
                parameter_type: e.into(),
                return_type: return_type.into(),
            };
            Ok(ExpressionTree::Arrow(arrow_tree))
        } else {
            Ok(e)
        }
    }
}

impl Parse for HoleTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        let prefix_token = tokens.expect_next(TokenData::QuestionMark)?;
        let hole_begin = prefix_token.source_pos();
        let ident_tree = IdentTree::parse(tokens)?;
        Ok(HoleTree {
            ident: ident_tree,
            source_pos: hole_begin,
        })
    }
}

impl Parse for IdentTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        let begin_line_column = tokens.source_pos_at_back();
        let token = tokens.next();
        if let Some(token) = token {
            if let TokenData::Ident(ident) = token.data() {
                Ok(Self {
                    source_pos: begin_line_column,
                    ident: ident.clone(),
                })
            } else {
                error!("expected ident at {}, got {}", begin_line_column, token).into()
            }
        } else {
            error!("expected ident at {}, got end of input", begin_line_column).into()
        }
    }
}

impl Parse for SortTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        tokens.expect_next(TokenData::Asterisk)?;
        Ok(Self { universe: 0 })
    }
}

impl Parse for BinderTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        let IdentTree {
            source_pos: begin_line_column,
            ident,
        } = tokens.try_parse::<IdentTree>()?;
        let binder_type = match ident.as_str() {
            "fun" => Ok(BinderType::Abstraction),
            "for" => Ok(BinderType::Product),
            _ => error!("expected `fun` or `for` at {}", begin_line_column).into(),
        }?;

        let variable_name = tokens.try_parse::<IdentTree>()?;
        tokens.expect_next(TokenData::Colon)?;
        let variable_type = tokens.try_parse::<ExpressionTree>()?.into();
        tokens.expect_next(TokenData::Period)?;
        let body = tokens.try_parse::<ExpressionTree>()?.into();

        Ok(BinderTree {
            binder_type,
            variable_name,
            variable_type,
            body,
        })
    }
}

impl Parse for AssignmentTree {
    fn parse(tokens: &mut ParseStream) -> Result<Self> {
        let name = IdentTree::parse(tokens)?;
        tokens.expect_next(TokenData::ColonEq)?;
        let value = ExpressionTree::parse(tokens)?;
        Ok(Self { name, value })
    }
}

#[test]
fn test_parse() {
    let input = "x := fun y : *. fun z : y. y".chars().collect::<Vec<_>>();
    let mut parse_stream = ParseStream::new(&input);
    let parse_tree = ParseTree::parse(&mut parse_stream).unwrap();
    println!("{}", parse_tree)
}
