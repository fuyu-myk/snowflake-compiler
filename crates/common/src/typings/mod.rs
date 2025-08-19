use std::fmt::{Display, Formatter, Result};


#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Void,
    Usize,
    Array(Box<Type>, usize), // Fixed-size array: [type; size]
    Unresolved, // used as a default
    Error,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let type_name = match self {
            Type::Int => "int".to_string(),
            Type::Float => "float".to_string(),
            Type::Bool => "bool".to_string(),
            Type::String => "string".to_string(),
            Type::Void => "void".to_string(),
            Type::Usize => "usize".to_string(),
            Type::Array(element_type, size) => format!("[{}; {}]", element_type, size),
            Type::Unresolved => "unresolved".to_string(),
            Type::Error => "???".to_string(),
        };

        write!(f, "{}", type_name)
    }
}

impl Type {
    pub fn is_assignable_to(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Usize, Type::Usize) => true,
            (Type::Array(left_elem, left_size), Type::Array(right_elem, right_size)) => {
                left_size == right_size && left_elem.is_assignable_to(right_elem)
            },
            (Type::Error, _) => true,
            (_, Type::Error) => true,
            _ => false,
        }
    }

    pub fn from_str(s: &str) -> Option<Type> {
        match s {
            "int" => Some(Type::Int),
            "float" => Some(Type::Float),
            "bool" => Some(Type::Bool),
            "string" => Some(Type::String),
            "void" => Some(Type::Void),
            "usize" => Some(Type::Usize),
            _ => None,
        }
    }
}