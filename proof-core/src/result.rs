use std::{
    borrow::{Borrow, BorrowMut},
    fmt::{Display, Formatter},
    rc::Rc,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ErrorInfo {
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct ErrorChain {
    error_info: ErrorInfo,
    causes: Rc<Vec<ErrorChain>>,
}

impl ErrorChain {
    pub fn new(error_info: ErrorInfo, causes: Vec<ErrorChain>) -> Self {
        Self {
            error_info,
            causes: Rc::new(causes),
        }
    }
}

fn display_chain(chain: &ErrorChain, f: &mut Formatter<'_>, indent: usize) -> std::fmt::Result {
    let indent_str = " ".repeat(indent);
    writeln!(f, "{}{}", indent_str, chain.error_info.message)?;
    write!(
        f,
        "{}┗ {}:{}:{}",
        indent_str, chain.error_info.file, chain.error_info.line, chain.error_info.column
    )?;
    let num_causes = chain.causes.len();
    if num_causes > 0 {
        writeln!(
            f,
            " (due to {} error{}):",
            num_causes,
            if num_causes > 1 { "s" } else { "" }
        )?;
    } else {
        writeln!(f)?;
    }
    for cause in chain.causes.iter() {
        display_chain(cause, f, indent + 2)?;
    }
    Ok(())
}

impl Display for ErrorChain {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        display_chain(self, f, 0)
    }
}

impl From<ErrorInfo> for ErrorChain {
    fn from(error_info: ErrorInfo) -> Self {
        Self {
            error_info,
            causes: Rc::new(Vec::new()),
        }
    }
}

pub trait ResultExt<T> {
    fn errors(error_info: ErrorInfo, causes: ErrorList) -> Self;
    fn chain_error<F: FnOnce() -> ErrorInfo>(self, error_chain: F) -> Self;
    fn unwrap_chain(self) -> T;
}

pub type Result<T> = std::result::Result<T, ErrorChain>;

impl<T> ResultExt<T> for Result<T> {
    fn errors(error_info: ErrorInfo, causes: ErrorList) -> Self {
        Self::Err(ErrorChain::new(error_info, causes.0))
    }

    fn chain_error<F: FnOnce() -> ErrorInfo>(self, error_chain: F) -> Self {
        match self {
            Self::Ok(x) => Self::Ok(x),
            Self::Err(error_list) => Self::Err(ErrorChain::new(error_chain(), vec![error_list])),
        }
    }

    fn unwrap_chain(self) -> T {
        match self {
            Self::Ok(x) => x,
            Self::Err(error_list) => {
                println!("{}", error_list);
                panic!("unwrap_chain panicked");
            }
        }
    }
}

impl<T> From<ErrorChain> for Result<T> {
    fn from(value: ErrorChain) -> Self {
        Self::Err(value)
    }
}

impl<T> From<ErrorInfo> for Result<T> {
    fn from(value: ErrorInfo) -> Self {
        Self::Err(ErrorChain::new(value, Vec::new()))
    }
}

#[macro_export]
macro_rules! error {
    ($($tokens:tt)+) => {
        $crate::result::ErrorInfo {
            file: file!(), line: line!(), column: column!(), message: format!($($tokens)+),
        }
    };
}

pub struct ErrorList(Vec<ErrorChain>);

impl ErrorList {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, error_chain: ErrorChain) {
        self.0.push(error_chain);
    }

    pub fn push_if_error<T, F: FnOnce() -> Result<T>>(&mut self, result: F) {
        match result() {
            Result::Ok(_) => {}
            Result::Err(error_chain) => self.push(error_chain),
        }
    }

    pub fn into_result<T, F: FnOnce() -> T, E: FnOnce() -> ErrorInfo>(
        &self,
        ok: F,
        err: E,
    ) -> Result<T> {
        if self.0.is_empty() {
            Result::Ok(ok())
        } else {
            Result::Err(ErrorChain::new(err(), self.0.clone()))
        }
    }
}

impl Default for ErrorList {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for ErrorList {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for error_chain in self.0.iter() {
            writeln!(f, "{}", error_chain)?;
        }
        Ok(())
    }
}

impl Borrow<[ErrorChain]> for ErrorList {
    fn borrow(&self) -> &[ErrorChain] {
        &self.0
    }
}

impl BorrowMut<[ErrorChain]> for ErrorList {
    fn borrow_mut(&mut self) -> &mut [ErrorChain] {
        &mut self.0
    }
}

impl From<Vec<ErrorChain>> for ErrorList {
    fn from(value: Vec<ErrorChain>) -> Self {
        Self(value)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn read_file(file_name: String) -> Result<String> {
        error!("file not found: {}", file_name).into()
    }

    fn resolve_domain(domain: String) -> Result<String> {
        error!("Failed to resolve domain {}", domain).into()
    }

    fn format_document(file_name: String) -> Result<String> {
        read_file(file_name).chain_error(|| error!("Failed to read file"))
    }

    fn ping_domain(domain: String) -> Result<String> {
        resolve_domain(domain).chain_error(|| error!("Failed to resolve domain"))
    }

    #[test]
    fn test() {
        let mut error_list = ErrorList::new();
        let doc_result = format_document("test.txt".to_string());
        error_list.push_if_error(|| doc_result);

        let ping_result = ping_domain("example.com".to_string());
        error_list.push_if_error(|| ping_result);

        let _result = Result::<String>::errors(error!("Failed to do all the stuff"), error_list);
    }
}
