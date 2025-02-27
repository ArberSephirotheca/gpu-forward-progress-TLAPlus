//! constant.rs is used to store the constant value defined by OpConstant or OpConstantComposite in the codegen module.

#[derive(Debug)]
pub enum ConstantType {
    Bool(bool),
    String(String),
    Int(i32),
    Uint(u32),
}

#[derive(Debug)]
pub struct Constant {
    pub name: String,
    pub value: ConstantType,
}
