use std::fmt::{Display, Formatter, Result};


#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Void,
    Usize,
    Array(Box<Type>, usize), // Fixed-size array: [type; size]
    Tuple(Vec<Box<Type>>), // Tuple type: (type1, type2, ...)
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
            Type::Tuple(element_types) => {
                let types_str: Vec<String> = element_types.iter().map(|t| format!("{}", t)).collect();
                format!("({})", types_str.join(", "))
            },
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
            (Type::Tuple(left_types), Type::Tuple(right_types)) => {
                left_types.len() == right_types.len() &&
                left_types.iter().zip(right_types.iter()).all(|(left, right)| left.is_assignable_to(right))
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