mod code_gen;
mod parser;

use code_gen::CodeGenerator;
use parser::ParsedInput;
use proc_macro::{self, TokenStream};
use syn::parse_macro_input;

#[proc_macro_derive(Atomize)]
pub fn derive(input: TokenStream) -> TokenStream {
    CodeGenerator::generate(ParsedInput::parse(parse_macro_input!(input)))
}
