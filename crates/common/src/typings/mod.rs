use std::fmt::{Display, Formatter, Result};

use crate::token::Token;


#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Void,
    Usize,
    Array(Box<Type>, usize), // Fixed-size array: [type; size]
    Object(ObjectType), // Unified type for tuples and structs
    ObjectUnresolved(Token), // During parsing - referenced by name for structs
    Unresolved, // used as a default
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectType {
    pub fields: Vec<FieldType>,
    pub kind: ObjectKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldType {
    pub ty: Box<Type>,
    pub name: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ObjectKind {
    Tuple,
    Struct(String),
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
            Type::Object(object_type) => {
                match &object_type.kind {
                    ObjectKind::Tuple => {
                        let types_str: Vec<String> = object_type.fields.iter()
                            .map(|f| format!("{}", f.ty)).collect();
                        format!("({})", types_str.join(", "))
                    },
                    ObjectKind::Struct(identifier) => {
                        let fields_str: Vec<String> = object_type.fields.iter()
                            .map(|f| {
                                format!("{}", f.ty)
                            }).collect();
                        format!("{}::<{}>", identifier.split("::").last().unwrap_or(identifier), fields_str.join(", "))
                    }
                }
            },
            Type::ObjectUnresolved(name) => name.span.literal.clone(),
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
            (Type::Object(left_obj), Type::Object(right_obj)) => {
                left_obj.fields.len() == right_obj.fields.len() &&
                left_obj.fields.iter().zip(right_obj.fields.iter()).all(|(left, right)| {
                    left.ty.is_assignable_to(&right.ty) && left.name == right.name
                }) && 

                match (&left_obj.kind, &right_obj.kind) {
                    (ObjectKind::Tuple, ObjectKind::Tuple) => true,
                    (ObjectKind::Struct(left_idx), ObjectKind::Struct(right_idx)) => left_idx == right_idx,
                    _ => false,
                }
            },
            (Type::ObjectUnresolved(left_name), Type::ObjectUnresolved(right_name)) => left_name == right_name,
            (Type::Error, _) => true,
            (_, Type::Error) => true,
            _ => false,
        }
    }

    pub fn from_token(s: &Token) -> Type {
        match s.span.literal.as_str() {
            "int" => Type::Int,
            "float" => Type::Float,
            "bool" => Type::Bool,
            "string" => Type::String,
            "void" => Type::Void,
            "usize" => Type::Usize,
            _ => Type::ObjectUnresolved(s.clone()), // Assume unknown types are structs
        }
    }

    /// Create a tuple type from a list of types
    pub fn tuple(field_types: Vec<Type>) -> Type {
        let fields = field_types.into_iter().map(|ty| FieldType {
            ty: Box::new(ty),
            name: None,
        }).collect();
        
        Type::Object(ObjectType {
            fields,
            kind: ObjectKind::Tuple,
        })
    }

    /// Create a struct type with the given index and field information
    pub fn struct_resolved(struct_name: String, field_types: Vec<(String, Type)>) -> Type {
        let fields = field_types.into_iter().map(|(name, ty)| FieldType {
            ty: Box::new(ty),
            name: Some(name),
        }).collect();
        
        Type::Object(ObjectType {
            fields,
            kind: ObjectKind::Struct(struct_name),
        })
    }
}