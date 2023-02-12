pub mod arena;
pub mod eval;
pub mod parse;

use std::{
    io::{self, Write},
    mem,
};

use console::{Key, Term};

use self::parse::{ParseStream, ParseTree, SourcePos, SourceRange, Diagnostic, Parse};

#[derive(Debug)]
pub struct Repl {
    term: Term,
    prompt_buffer: Vec<char>,
    prompt_history: Vec<Vec<char>>,
    utf8_read_buffer: [u8; 4],
    history_selection_index: HistorySelection,
}

#[derive(Debug)]
enum ReplCommand {
    ShowContext,
    Check,
    Ast(Vec<char>),
}

#[derive(Debug)]
enum HistorySelection {
    Inactive,
    Active(usize),
}

impl Repl {
    pub fn new(term: Term) -> Self {
        Self {
            term,
            prompt_buffer: vec![],
            prompt_history: vec![],
            utf8_read_buffer: Default::default(),
            history_selection_index: HistorySelection::Inactive,
        }
    }

    pub const fn prompt_prefix() -> &'static str {
        ">> "
    }

    fn prompt_input(&mut self) -> io::Result<()> {
        loop {
            let last_key_read = self.term.read_key()?;

            match last_key_read {
                Key::Backspace => {
                    self.apply_history_selection()?;
                    if self.prompt_buffer.pop().is_some() {
                        self.term.clear_chars(1)?
                    }
                }
                Key::Enter => {
                    self.apply_history_selection()?;
                    if let Some(command) = self.repl_command() {
                        match command {
                            ReplCommand::ShowContext => {
                                self.term.write_line("show context")?;
                            }
                            ReplCommand::Check => {
                                self.term.write_line("check")?;
                            }
                            ReplCommand::Ast(input) => {
                                let mut parse_stream = ParseStream::new(&input);
                                let parse_tree = ParseTree::parse(&mut parse_stream);
                                self.term.write_line("")?;
                                match parse_tree {
                                    Ok(tree) => self.term.write_line(tree.to_string().as_str())?,
                                    Err(e) => self.term.write_line(e.to_string().as_str())?,
                                }
                                if let Some(token) = parse_stream.peek() {
                                    let end_of_str =
                                        SourcePos::find_end_of_str(&input, *token.begin());
                                    self.term.write_line(end_of_str.to_string().as_str())?;
                                    let diagnostic = Diagnostic::new(
                                        "parsing stopped before end of input reached".to_owned(),
                                        SourceRange::new(*token.begin(), end_of_str),
                                    );
                                    self.term.write_line(&diagnostic.display(&input))?;
                                }
                            }
                        }
                        return Ok(());
                    } else {
                        let mut parse_stream = ParseStream::new(&self.prompt_buffer);
                        let parse_tree = ParseTree::parse(&mut parse_stream);
                        match parse_tree {
                            Ok(_) => self.term.write_line("\nOk!")?,
                            Err(e) => self.term.write_line(e.to_string().as_str())?,
                        }
                        if parse_stream.peek().is_some() {
                            self.term
                                .write_line("parsing stopped before end of input reached")?
                        }
                        return Ok(());
                    }
                }
                Key::Char(last_char_read) => {
                    self.apply_history_selection()?;
                    last_char_read.encode_utf8(&mut self.utf8_read_buffer);
                    self.term.write_all(&self.utf8_read_buffer)?;
                    self.prompt_buffer.push(last_char_read);
                }
                Key::ArrowUp => {
                    match self.history_selection_index {
                        HistorySelection::Inactive => {
                            if let Some(index) = self.prompt_history.len().checked_sub(1) {
                                self.history_selection_index = HistorySelection::Active(index);
                                self.set_prompt_line(self.prompt_history[index].iter().collect())?;
                            }
                        }
                        HistorySelection::Active(index) => {
                            if let Some(new_index) = index.checked_sub(1) {
                                self.history_selection_index = HistorySelection::Active(new_index);
                                self.set_prompt_line(self.prompt_history[new_index].iter().collect())?;
                            }
                        }
                    }
                }
                Key::ArrowDown => {
                    match self.history_selection_index {
                        HistorySelection::Inactive => {}
                        HistorySelection::Active(index) => {
                            if let Some(new_index) = index.checked_add(1) {
                                if new_index < self.prompt_history.len() {
                                    self.history_selection_index = HistorySelection::Active(new_index);
                                    self.set_prompt_line(self.prompt_history[new_index].iter().collect())?;
                                } else {
                                    self.history_selection_index = HistorySelection::Inactive;
                                    self.set_prompt_line(self.prompt_buffer.iter().collect())?;
                                }
                            } else {
                                self.history_selection_index = HistorySelection::Inactive;
                                self.set_prompt_line(self.prompt_buffer.iter().collect())?;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn clear_prompt(&mut self) -> io::Result<()> {
        self.term.clear_line()?;
        self.term.write_all(Repl::prompt_prefix().as_bytes())
    }

    pub fn set_prompt_line(&mut self, line: String) -> io::Result<()> {
        self.clear_prompt()?;
        self.term.write_all(line.as_bytes())
    }

    fn apply_history_selection(&mut self) -> io::Result<()> {
        match self.history_selection_index {
            HistorySelection::Inactive => Ok(()),
            HistorySelection::Active(index) => {
                self.history_selection_index = HistorySelection::Inactive;
                self.prompt_buffer = self.prompt_history[index].clone();
                Ok(())
            }
        }
    }

    pub fn run_repl(&mut self) -> io::Result<()> {
        loop {
            self.term.hide_cursor()?;
            self.term.write_all(Repl::prompt_prefix().as_bytes())?;
            self.term.show_cursor()?;
            self.prompt_input()?;
            self.prompt_history.push(mem::take(&mut self.prompt_buffer));
        }
    }

    fn repl_command(&self) -> Option<ReplCommand> {
        // Command is of form
        // :ctx | :check <expr> | :ast <expr>
        let prompt_slice = self.prompt_buffer.as_slice();
        if prompt_slice.starts_with(&[':']) {
            let mut command = prompt_slice[1..].iter().cloned();
            let command_name = command
                .by_ref()
                .take_while(|c| !c.is_whitespace())
                .collect::<Vec<_>>();
            let command_args = command.collect::<Vec<_>>();
            match command_name.as_slice() {
                ['c', 't', 'x'] => Some(ReplCommand::ShowContext),
                ['c', 'h', 'e', 'c', 'k'] => Some(ReplCommand::Check),
                ['a', 's', 't'] => Some(ReplCommand::Ast(command_args)),
                _ => None,
            }
        } else {
            None
        }
    }
}
