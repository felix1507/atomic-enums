use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Ident, Span};

use crate::parser::ParsedInput;

pub struct CodeGenerator {
    input: ParsedInput,
}

impl CodeGenerator {
    pub fn generate(input: ParsedInput) -> TokenStream {
        let generator = CodeGenerator { input };

        let trait_u16_from_self = generator.gen_trait_u16_from_self();
        let trait_self_from_u16 = generator.get_trati_self_from_u16();

        let ident = generator.ident();
        quote::quote!(
            #[automatically_derived]
            impl Atomize for #ident {}

            #[automatically_derived]
            #trait_u16_from_self

            #[automatically_derived]
            #trait_self_from_u16
        ).into()
    }

    fn ident(&self) -> Ident {
        self.input.enum_ident.clone()
    }

    fn gen_trait_u16_from_self(&self) -> TokenStream2 {
        let ident = self.ident();
        let mut match_stmt = quote::quote!();
        let mut is_first = true;

        for e_val in self.input.enum_values.iter() {
            let e_ident = e_val.ident.clone();
            let discriminant = e_val.discriminant.clone();

            if is_first {
                is_first = false;
                match_stmt = quote::quote!( #ident::#e_ident => #discriminant );
            } else {
                match_stmt = quote::quote!( #match_stmt, #ident::#e_ident => #discriminant );
            }
        }

        quote::quote!(
            impl From<#ident> for u16 {
                fn from(value: #ident) -> Self {
                    match value {
                        #match_stmt
                    }
                }
            }
        )
    }

    fn get_trati_self_from_u16(&self) -> TokenStream2 {
        let ident = self.ident();
        let mut match_stmt = quote::quote!();
        let mut is_first = true;
        let unknown_ident = Ident::new("UnknownField", Span::call_site());
        println!("Unknown ident generated: {:?}", unknown_ident);

        for e_val in self.input.enum_values.iter() {
            // Skip the UnknownField, it is used as default handler
            if &e_val.ident == &unknown_ident {
                println!("Skipped: {:?}", &e_val.ident);
                continue;
            }

            let ident = e_val.ident.clone();
            let discriminant = e_val.discriminant.clone();

            if is_first {
                is_first = false;
                match_stmt = quote::quote!( #discriminant => Self::#ident );
            } else {
                match_stmt = quote::quote!(#match_stmt, #discriminant => Self::#ident);
            }
        }

        match_stmt = quote::quote!(#match_stmt, _ => Self::#unknown_ident);

        quote::quote!(
            impl From<u16> for #ident {
                fn from(value: u16) -> Self {
                    match value {
                        #match_stmt
                    }
                }
            }
        )
    }
}
