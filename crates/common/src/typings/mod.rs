use std::fmt::{Display, Formatter, Result};

use crate::token::Token;


#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub token: Token,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Int,
    Float,
    Bool,
    String,
    Void,
    Usize,
    Array(Box<TypeKind>, usize), // Fixed-size array: [type; size]
    Object(ObjectType), // Unified type for tuples and structs
    ObjectUnresolved(Token), // During parsing - referenced by name for structs
    Unresolved, // used as a default
    Path(Option<String>, String), // Optional module path and type name
    Enum {
        enum_name: String,
        variant_name: Option<String>,  // None for the enum type itself
    },
    Unit, // used for `Foo = ..`
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectType {
    pub fields: Vec<FieldType>,
    pub kind: ObjectKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldType {
    pub ty: Box<TypeKind>,
    pub name: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ObjectKind {
    Tuple,
    Struct(String),
}

impl Display for TypeKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let type_name = match self {
            TypeKind::Int => "int".to_string(),
            TypeKind::Float => "float".to_string(),
            TypeKind::Bool => "bool".to_string(),
            TypeKind::String => "string".to_string(),
            TypeKind::Void => "void".to_string(),
            TypeKind::Usize => "usize".to_string(),
            TypeKind::Array(element_type, size) => format!("[{}; {}]", element_type, size),
            TypeKind::Object(object_type) => {
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
                        
                        if fields_str.is_empty() {
                            return write!(f, "{}", identifier.split("::").last().unwrap_or(identifier));
                        }

                        format!("{}::<{}>", identifier.split("::").last().unwrap_or(identifier), fields_str.join(", "))
                    }
                }
            },
            TypeKind::ObjectUnresolved(name) => name.span.literal.clone(),
            TypeKind::Unresolved => "unresolved".to_string(),
            TypeKind::Path(module_path, type_name) => {
                if let Some(module) = module_path {
                    format!("{}::{}", module, type_name)
                } else {
                    type_name.clone()
                }
            },
            TypeKind::Enum { enum_name, variant_name } => {
                if let Some(variant) = variant_name {
                    format!("{}::{}", enum_name, variant)
                } else {
                    enum_name.clone()
                }
            },
            TypeKind::Unit => "()".to_string(),
            TypeKind::Error => "???".to_string(),
        };

        write!(f, "{}", type_name)
    }
}

impl TypeKind {
    pub fn is_assignable_to(&self, other: &TypeKind) -> bool {
        match (self, other) {
            (TypeKind::Int, TypeKind::Int) => true,
            (TypeKind::Float, TypeKind::Float) => true,
            (TypeKind::Bool, TypeKind::Bool) => true,
            (TypeKind::String, TypeKind::String) => true,
            (TypeKind::Usize, TypeKind::Usize) => true,
            (TypeKind::Array(left_elem, left_size), TypeKind::Array(right_elem, right_size)) => {
                left_size == right_size && left_elem.is_assignable_to(right_elem)
            },
            (TypeKind::Object(left_obj), TypeKind::Object(right_obj)) => {
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
            (TypeKind::ObjectUnresolved(left_name), TypeKind::ObjectUnresolved(right_name)) => left_name == right_name,
            (TypeKind::Enum { enum_name: left_enum, .. }, TypeKind::Enum { enum_name: right_enum, .. }) => left_enum == right_enum,
            (TypeKind::Error, _) => true,
            (_, TypeKind::Error) => true,
            _ => false,
        }
    }

    pub fn from_token(s: &Token) -> TypeKind {
        match s.span.literal.as_str() {
            "int" => TypeKind::Int,
            "float" => TypeKind::Float,
            "bool" => TypeKind::Bool,
            "string" => TypeKind::String,
            "void" => TypeKind::Void,
            "usize" => TypeKind::Usize,
            _ => TypeKind::ObjectUnresolved(s.clone()), // Assume unknown types are structs
        }
    }

    /// Create a tuple type from a list of types
    pub fn tuple(field_types: Vec<TypeKind>) -> TypeKind {
        let fields = field_types.into_iter().map(|ty| FieldType {
            ty: Box::new(ty),
            name: None,
        }).collect();
        
        TypeKind::Object(ObjectType {
            fields,
            kind: ObjectKind::Tuple,
        })
    }

    /// Create a struct type with the given index and field information
    pub fn struct_resolved(struct_name: String, field_types: Vec<(String, TypeKind)>) -> TypeKind {
        let fields = field_types.into_iter().map(|(name, ty)| FieldType {
            ty: Box::new(ty),
            name: Some(name),
        }).collect();
        
        TypeKind::Object(ObjectType {
            fields,
            kind: ObjectKind::Struct(struct_name),
        })
    }
}