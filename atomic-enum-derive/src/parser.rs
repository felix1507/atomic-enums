use proc_macro2::Ident;
use syn::{DeriveInput, Expr};

#[derive(Debug)]
pub struct EnumValue {
    pub ident: Ident,
    pub discriminant: Expr,
}

pub struct ParsedInput {
    pub enum_ident: Ident,
    pub enum_values: Vec<EnumValue>,
}

impl ParsedInput {
    pub fn parse(input: DeriveInput) -> Self {
        let enum_input = match input.data {
            syn::Data::Enum(e) => e,
            _ => panic!("The trait is only for enums!"),
        };
        println!("{:#?}", &enum_input);

        let mut has_invalid_field = false;
        let enum_values = enum_input
            .variants
            .iter()
            .map(|v| {
                let v = v.to_owned();

                if &v.ident.to_string() == "UnknownField" {
                    has_invalid_field = true;
                }

                EnumValue {
                    ident: v.ident,
                    discriminant: match v.discriminant {
                        Some((_, d)) => d,
                        None => panic!("A number must be assigned to each field!"),
                    },
                }
            })
            .collect();

        if !has_invalid_field {
            panic!("The enumeration must contain a field with the name \"UnknownField\"!");
        }

        println!("{:#?}", &enum_values);

        Self {
            enum_ident: input.ident,
            enum_values,
        }
    }
}
