use std::borrow::Cow;

use crate::{
    eval::{beta_reduce, substitute},
    expr::{Expression, Variable},
    goals::expressions_match,
    result::{Result, ResultExt},
    types::Context,
};

#[derive(Clone)]
struct Definition {
    variable: Variable,
    type_: Expression,
    value: Expression,
    value_substituted: Expression,
}

pub struct DefinitionScope<'a> {
    definitions: Vec<Definition>,
    context: Context<'a>,
}

impl<'a> DefinitionScope<'a> {
    pub fn new() -> DefinitionScope<'a> {
        DefinitionScope {
            definitions: Vec::new(),
            context: Context::Empty,
        }
    }

    pub fn add_definition(&mut self, variable: Variable, expression: Expression) -> Result<()> {
        let substituted_expression = self.substitute(&expression);
        let type_ = self.context.resolve_type(&substituted_expression).chain_error(|| {
            error!(
                "could not add definition {} = {} because type resolution failed",
                variable.clone(),
                expression.clone()
            )
        })?;
        self.definitions.push(Definition {
            variable: variable.clone(),
            type_: type_.clone(),
            value: expression,
            value_substituted: substituted_expression,
            // (variable.clone(), type_.clone(), expression)
        });
        self.context = self.context.clone().extend(variable, Cow::Owned(type_));
        Ok(())
    }

    pub fn substitute(&self, expression: &Expression) -> Expression {
        let mut expression = expression.clone();

        for Definition {
            variable,
            type_: _,
            value: _,
            value_substituted,
        } in self.definitions.iter()
        {
            expression = substitute(&expression, variable.clone(), value_substituted);
        }

        expression
    }

    pub fn show_all(&self) -> Result<()> {
        for Definition {
            variable,
            type_,
            value,
            value_substituted,
        } in self.definitions.iter()
        {
            println!("{}  : {}", variable, &type_);
            println!("{}  = {}", variable, &value);
            println!("{} β= {}", variable, &beta_reduce(&value_substituted));
            println!();
        }

        Ok(())
    }

    pub fn show_type(&self, expression: Expression) -> Result<()> {
        let substituted_expression = self.substitute(&expression);
        let type_ = self.context.resolve_type(&substituted_expression)
            .chain_error(|| error!("could not resolve type of value {}", expression))?;
        println!("{} : {}", &expression, &type_);
        Ok(())
    }

    pub fn show(&self, expression: Expression) -> Result<()> {
        let substituted_expression = self.substitute(&expression);
        let type_ = self.context.resolve_type(&expression)?;
        println!("{}  : {}", &expression, &type_);
        println!("{}  = {}", &expression, &substituted_expression);
        println!(
            "{} β= {}",
            &expression,
            &beta_reduce(&substituted_expression)
        );
        Ok(())
    }

    pub fn eval(&self, expression: &Expression) -> Expression {
        let substituted_expression = self.substitute(expression);
        let beta_reduced = beta_reduce(&substituted_expression);
        beta_reduced
    }

    pub fn show_type_check(&self, value: Expression, type_: Expression) -> Result<()> {
        let substituted_value = self.substitute(&value);
        let substituted_type = self.substitute(&type_);
        let value_type = self.context.resolve_type(&substituted_value)
            .chain_error(|| error!("could not resolve type of value {}", value.clone()))?;
        expressions_match(&value_type, &substituted_type)
            .chain_error(|| error!("type check {} : {} failed!", value.clone(), type_.clone()))?;
        println!("Sucess! {} : {}", &value, &type_);
        Ok(())
    }

    pub fn is_of_type(&self, value: &Expression, type_: &Expression) -> Result<bool> {
        let substituted_value = self.substitute(value);
        let substituted_type = self.substitute(type_);
        let value_type = self.context.resolve_type(&substituted_value)
            .chain_error(|| error!("could not resolve type of value {}", value.clone()))?;
        Ok(expressions_match(&value_type, &substituted_type).is_ok())
    }

    pub fn show_eq_check(&self, lhs: Expression, rhs: Expression) -> Result<()> {
        let substituted_lhs = self.substitute(&lhs);
        let substituted_rhs = self.substitute(&rhs);
        expressions_match(&substituted_lhs, &substituted_rhs)
            .chain_error(|| error!("error while checking for equality"))?;
        println!("Sucess! {} = {}", &lhs, &rhs);
        Ok(())
    }

    pub fn is_eq(&self, lhs: &Expression, rhs: &Expression) -> bool {
        let substituted_lhs = self.substitute(lhs);
        let substituted_rhs = self.substitute(rhs);
        expressions_match(&substituted_lhs, &substituted_rhs).is_ok()
    }

    pub fn context(&self) -> &Context<'a> {
        &self.context
    }
}

impl<'a> Default for DefinitionScope<'a> {
    fn default() -> Self {
        Self::new()
    }
}
