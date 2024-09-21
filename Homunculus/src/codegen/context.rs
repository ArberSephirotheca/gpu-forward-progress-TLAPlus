use crate::compiler::ast::ast::{BinaryExpr, Expr, ResultType, Root, Stmt};
/// `CodegenCx` is a struct that holds the compilation unit of the codegen.
use crate::compiler::parse::symbol_table::*;
use crate::compiler::parse::syntax::SyntaxNode;

use super::builder::InstructionArgumentsBuilder;
use super::common::{
    Instruction, InstructionArgument, InstructionArguments, InstructionBuiltInVariable,
    InstructionScope, InstructionValue, Program, Scheduler, VariableScope,
};
use crate::codegen::common::{IndexKind, InstructionName};

pub struct CodegenCx {
    type_table: SpirvTypeTable,
    variable_table: VariableSymbolTable,
    label_table: LabelTable,
    current_inst_position: u32,
    sub_group_size: u32,
    work_group_size: u32,
    num_work_group: u32,
    scheduler: Scheduler,
    // also include built in variable
}

impl CodegenCx {
    pub fn new(
        sub_group_size: u32,
        work_group_size: u32,
        num_work_group: u32,
        scheduler: Scheduler,
    ) -> Self {
        Self {
            type_table: SpirvTypeTable::new(),
            variable_table: VariableSymbolTable::new(),
            label_table: LabelTable::new(),
            current_inst_position: 0,
            sub_group_size,
            work_group_size,
            num_work_group,
            scheduler,
        }
    }
    pub(crate) fn increment_inst_position(&mut self) -> u32 {
        self.current_inst_position += 1;
        self.current_inst_position
    }
    pub(crate) fn reset_position(&mut self) {
        self.current_inst_position = 0;
    }
    pub fn insert_type(&mut self, id: String, ty: SpirvType) {
        self.type_table.insert(id, ty);
    }

    pub fn lookup_type(&self, id: &str) -> Option<&SpirvType> {
        self.type_table.lookup(id)
    }

    pub fn insert_variable(&mut self, name: String, var_info: VariableInfo) {
        self.variable_table.insert(name, var_info);
    }

    pub fn lookup_variable(&self, id: &str) -> Option<VariableInfo> {
        self.variable_table.lookup(id)
    }

    pub fn built_in_variable(&self, id: &str) -> Option<BuiltInVariable> {
        match self.lookup_variable(id) {
            Some(var_info) => var_info.get_builtin(),
            None => None,
        }
    }

    pub fn insert_label(&mut self, label: String, position: u32) {
        self.label_table.insert(label, position);
    }

    pub fn lookup_label(&self, label: &str) -> Option<&u32> {
        self.label_table.lookup(label)
    }

    /// get_from_spirv_type will return the InstructionValueType and index for the given SpirvType.
    pub fn get_from_spirv_type(&self, spirv_type: &SpirvType) -> (InstructionValue, IndexKind) {
        match spirv_type {
            SpirvType::Void => (InstructionValue::None, IndexKind::Literal(-1)),
            SpirvType::Function { .. } => (InstructionValue::None, IndexKind::Literal(-1)),
            SpirvType::Bool => (InstructionValue::Bool(true), IndexKind::Literal(-1)),
            SpirvType::Int {
                width: _,
                signed: _,
            } => (InstructionValue::Int(0), IndexKind::Literal(-1)),
            SpirvType::Vector { element, count } => {
                let real_type = self.lookup_type(element.as_str()).unwrap();
                (
                    self.get_from_spirv_type(real_type).0,
                    IndexKind::Literal(*count as i32),
                )
            }
            SpirvType::Array { element, count } => {
                let real_type = self.lookup_type(element.as_str()).unwrap();
                (
                    self.get_from_spirv_type(real_type).0,
                    IndexKind::Literal(*count as i32),
                )
            }
            // fixme: what to do with runtime array? the index is unknown
            SpirvType::RuntimeArray { element } => {
                let real_type = self.lookup_type(element.as_str()).unwrap();
                (
                    self.get_from_spirv_type(real_type).0,
                    IndexKind::Literal(-1),
                )
            }
            // fixme: we only accept one member for now
            // run the function recursively to get the actual type
            SpirvType::Struct { members } => {
                let real_type = self.lookup_type(members.as_str()).unwrap();
                self.get_from_spirv_type(real_type)
            }

            SpirvType::Pointer {
                ty,
                storage_class: _,
            } => {
                let real_type = self.lookup_type(ty.as_str()).unwrap();
                self.get_from_spirv_type(real_type)
            }
        }
    }

    fn symbol_table_construction_pass_expr(&mut self, var_name: String, expr: &Expr) {
        match expr {
            Expr::TypeExpr(type_expr) => {
                self.insert_type(var_name.clone(), type_expr.ty());
            }
            Expr::VariableExpr(var_expr) => {
                let ty_name = var_expr.ty_name().unwrap();
                let storage_class = var_expr.storage_class().unwrap();
                // get the actual type of the variable
                let built_in = self.built_in_variable(var_name.as_str());

                let spirv_type = match self.lookup_type(ty_name.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", ty_name),
                };

                // variable expression would be a variable declaration, so its SSA form is the same as the variable name
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    spirv_type.clone(),
                    vec![],
                    storage_class,
                    None,
                    built_in,
                );
                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            // example: OpAccessChain
            // fixme: need testing
            Expr::VariableRef(var_ref) => {
                // Start with the base variable
                let base_var_name = var_ref.base_var_name().unwrap();
                let base_var_info = self
                    .lookup_variable(base_var_name.text())
                    .expect("OpAccessChain: Base variable not found in symbol table");

                let ty = self
                    .lookup_type(var_ref.ty().unwrap().text())
                    .expect("OpAccessChain: Type not found in symbol table");
                // Initialize access chain tracking
                let mut access_chain = base_var_info.access_chain.clone();

                let index_name = var_ref.index_name().unwrap();
                let var_info = self.lookup_variable(index_name.text()).unwrap();

                // Record the access step
                // since it is a constant, we can directly use its value
                if var_info.is_constant() {
                    access_chain.push(AccessStep::ConstIndex(var_info.get_constant_int()))
                } else {
                    access_chain.push(AccessStep::VariableIndex(index_name.text().to_string()));
                }

                // Build the final variable information after applying the access chain
                let var_info = VariableInfo::new(
                    base_var_name.text().to_string(),
                    ty.clone(),
                    access_chain,
                    base_var_info.get_storage_class(),
                    None,
                    base_var_info.get_builtin(),
                );

                // Insert the new variable information into the symbol table
                self.insert_variable(var_name, var_info.clone());
            }
            Expr::ConstExpr(const_expr) => {
                let ty = self.lookup_type(const_expr.ty().unwrap().text()).unwrap();
                let value = const_expr.value().unwrap().text().parse::<i32>().unwrap();
                let signed = match ty {
                    SpirvType::Int { signed, .. } => signed,
                    _ => panic!("ConstExpr: Type {:#?} is not an integer type", ty),
                };

                let constant_info = VariableInfo::new_const_int(var_name.clone(), value, *signed);
                self.insert_variable(var_name, constant_info);
            }
            Expr::ConstTrueExpr(_) => {
                let constant_info = VariableInfo::new_const_bool(var_name.clone(), true);
                self.insert_variable(var_name, constant_info);
            }
            Expr::ConstFalseExpr(_) => {
                let constant_info = VariableInfo::new_const_bool(var_name.clone(), false);
                self.insert_variable(var_name, constant_info);
            }
            Expr::AddExpr(add_expr) => {
                let result_type = add_expr.result_type().unwrap();
                // let storage_class = add_expr.storage_class().unwrap();
                // get the actual type of the variable
                let spirv_type = match self.lookup_type(result_type.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", result_type),
                };

                // variable expression would be a variable declaration, so its SSA form is the same as the variable name
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    spirv_type.clone(),
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }

            Expr::SubExpr(sub_expr) => {
                let result_type = sub_expr.result_type().unwrap();
                // let storage_class = add_expr.storage_class().unwrap();
                // get the actual type of the variable
                let spirv_type = match self.lookup_type(result_type.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", result_type),
                };

                let var_info = VariableInfo::new(
                    var_name.clone(),
                    spirv_type.clone(),
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::MulExpr(mul_expr) => {
                let result_type = mul_expr.result_type().unwrap();
                // let storage_class = add_expr.storage_class().unwrap();
                // get the actual type of the variable
                let spirv_type = match self.lookup_type(result_type.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", result_type),
                };

                let var_info = VariableInfo::new(
                    var_name.clone(),
                    spirv_type.clone(),
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::EqualExpr(_) => {
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::NotEqualExpr(_) => {
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::LessThanExpr(_) => {
                let var_info: VariableInfo = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::LessThanEqualExpr(_) => {
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::GreaterThanExpr(_) => {
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::GreaterThanEqualExpr(_) => {
                let var_info = VariableInfo::new(
                    var_name.clone(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            Expr::LabelExpr(_) => {
                let position = self.increment_inst_position();
                self.insert_label(var_name.clone(), position);
            }
            // fixme: handle array type
            // LoadExpr will only load to a SSA result ID that has pointer type
            // it will never load to a real variable
            Expr::LoadExpr(load_expr) => {
                // fixme: better error handling
                let pointer_ssa_id = load_expr.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                self.insert_variable(var_name.clone(), pointer_info.clone());
                self.increment_inst_position();
            }
            Expr::AtomicLoadExpr(atomic_load_expr) => {
                // fixme: better error handling
                let pointer_ssa_id = atomic_load_expr.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                self.insert_variable(var_name.clone(), pointer_info.clone());
                self.increment_inst_position();
            }
            // fixme: consider memory scope in the future
            Expr::AtomicExchangeExpr(atomic_exch_expr) => {
                let result_type = atomic_exch_expr.result_type().unwrap();
                // get the actual type of the variable
                let spirv_type = match self.lookup_type(result_type.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", result_type),
                };

                let var_info = VariableInfo::new(
                    var_name.clone(),
                    spirv_type.clone(),
                    vec![],
                    StorageClass::Local,
                    None,
                    None,
                );

                self.insert_variable(var_name, var_info);
                self.increment_inst_position();
            }
            // Expr::AtomicCompareExchangeExpr(atomic_cmp_exch_expr) => {
            //     todo!()
            // }
            // todo: implement the rest of the expressions
            _ => unimplemented!(),
        }
    }

    fn symbol_table_construction_pass_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::ExecutionMode(_) => {}
            Stmt::ReturnStatement(_) => {
                self.increment_inst_position();
            }

            // Stmt::ExecutionMode(execution_mode) => {
            //     let local_size_x = execution_mode.local_size_x().unwrap().text().parse::<i32>().unwrap();
            //     self.insert_variable("local_size_x".to_string(), VariableInfo::new_const_int("local_size_x".to_string(), local_size_x, false));
            //     None
            // }
            Stmt::VariableDef(var_def) => {
                let var_name = var_def.name().unwrap().text().to_string();
                let expr = var_def
                    .value()
                    .expect("Variable definition must have a value");
                self.symbol_table_construction_pass_expr(var_name, &expr);
            }
            // decorate statement is used to attach built-in variables/metadata to a variable
            Stmt::DecorateStatement(_) => {}
            // fixme:: does not support OpAccesschain yet
            Stmt::StoreStatement(store_stmt) => {
                let pointer_ssa_id = store_stmt.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                self.insert_variable(pointer_ssa_id.text().to_string(), pointer_info.clone());

                self.increment_inst_position();
            }
            Stmt::AtomicStoreStatement(atomic_store_stmt) => {
                let pointer_ssa_id = atomic_store_stmt.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                self.insert_variable(pointer_ssa_id.text().to_string(), pointer_info.clone());

                self.increment_inst_position();
            }
            Stmt::BranchStatement(_) => {
                self.increment_inst_position();
            }
            Stmt::BranchConditionalStatement(_) => {
                self.increment_inst_position();
            }
            Stmt::LoopMergeStatement(_) => {
                self.increment_inst_position();
            }
            Stmt::SelectionMergeStatement(_) => {
                self.increment_inst_position();
            }

            _ => panic!("Unsupported statement: {:?}", stmt),
        }
    }

    fn symbol_table_construction_pass(&mut self, root: &Root) {
        for stmt in root.stmts() {
            self.symbol_table_construction_pass_stmt(&stmt);
        }
    }

    /// generate_code_for_expr will generate the SPIR-V code for the given expression,
    /// and the generated code will be added to the instruction builder.
    fn generate_code_for_expr(
        &mut self,
        var_name: String,
        expr: &Expr,
    ) -> Option<InstructionArgumentsBuilder> {
        match expr {
            Expr::TypeExpr(_) => None,
            Expr::VariableExpr(var_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg_builder = InstructionArgument::builder();
                // fixme: error handling
                let ty_name = var_expr.ty_name().unwrap();
                // get the actual type of the variable
                let built_in = self.built_in_variable(var_name.as_str());

                let spirv_type = match self.lookup_type(ty_name.text()) {
                    Some(ty) => ty,
                    None => panic!("Type {} not found", ty_name),
                };

                let (instr_value, idx) = match &built_in {
                    Some(b) => {
                        let instr_value =
                            InstructionValue::BuiltIn(InstructionBuiltInVariable::cast(b.clone()));
                        (instr_value, IndexKind::Literal(-1))
                    }
                    None => self.get_from_spirv_type(spirv_type),
                };
                // fixme: avoid using unwrap, use better error handling instead
                let arg = inst_arg_builder
                    .name(var_name)
                    .value(instr_value)
                    .index(idx)
                    .scope(VariableScope::cast(&var_expr.storage_class().unwrap()))
                    .build()
                    .unwrap();

                Some(
                    inst_args_builder
                        .name(InstructionName::Assignment)
                        .num_args(1)
                        .push_argument(arg),
                )
            }
            // example: OpAccessChain
            // fixme: need testing
            // Expr::VariableRef(var_ref) => {
            //     // Start with the base variable
            //     let base_var_name = var_ref.base_var_name().unwrap();
            //     let base_var_info = self
            //         .lookup_variable(base_var_name.text())
            //         .expect("OpAccessChain: Base variable not found in symbol table");

            //     println!("{:#?}", var_ref.ty().unwrap().text());
            //     let ty = self
            //         .lookup_type(var_ref.ty().unwrap().text())
            //         .expect("OpAccessChain: Type not found in symbol table");
            //     // Initialize access chain tracking
            //     let mut access_chain = base_var_info.access_chain.clone();

            //     let index_name = var_ref.index_name().unwrap();
            //     let var_info = self.lookup_variable(index_name.text()).unwrap();

            //     // Record the access step
            //     // since it is a constant, we can directly use its value
            //     if var_info.is_constant() {
            //         access_chain.push(AccessStep::ConstIndex(var_info.get_constant_int()))
            //     } else {
            //         access_chain.push(AccessStep::VariableIndex(index_name.text().to_string()));
            //     }
            //     // OpAccessChain instruction does not output instruction in TLA+ code
            //     None
            // }
            Expr::ConstExpr(_) => None,
            Expr::ConstTrueExpr(_) => None,
            Expr::ConstFalseExpr(_) => None,
            Expr::AddExpr(add_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                let first_operand = add_expr.first_operand().unwrap();
                let second_operand = add_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("AddExpr: First operand not found");

                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("AddExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_arg = if first_operand_info.is_constant() {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::Add)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }

            Expr::SubExpr(sub_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                let first_operand = sub_expr.first_operand().unwrap();
                let second_operand = sub_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("SubExpr: First operand not found");

                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("SubExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_arg = if first_operand_info.is_constant() {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::Sub)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::MulExpr(mul_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                let first_operand = mul_expr.first_operand().unwrap();
                let second_operand = mul_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("MulExpr: First operand not found");

                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("MulExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_arg = if first_operand_info.is_constant() {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::Mul)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }

            Expr::EqualExpr(equal_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                let first_operand = equal_expr.first_operand().unwrap();
                let second_operand = equal_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("EqualExpr: First operand not found");

                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("EqualExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();
                let first_operand_arg = if first_operand_info.is_constant() {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg1_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::Equal)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::NotEqualExpr(not_equal_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let first_operand_builder = InstructionArgument::builder();
                let second_operand_builder = InstructionArgument::builder();

                let first_operand = not_equal_expr.first_operand().unwrap();
                let second_operand = not_equal_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("NotEqualExpr: First operand not found");
                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("NotEqualExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_arg = if first_operand_info.is_constant() {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };
                let second_operand_arg = if second_operand_info.is_constant() {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::NotEqual)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::LessThanExpr(less_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let first_operand_builder = InstructionArgument::builder();
                let second_operand_builder = InstructionArgument::builder();

                let first_operand = less_expr.first_operand().unwrap();
                let second_operand = less_expr.second_operand().unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("LessThanExpr: First operand not found");
                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("LessThanExpr: Second operand not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_arg = if first_operand_info.is_constant() {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::LessThan)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::LessThanEqualExpr(less_equal_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let first_operand_builder = InstructionArgument::builder();
                let second_operand_builder = InstructionArgument::builder();

                let first_operand = less_equal_expr.first_operand().unwrap();
                let second_operand = less_equal_expr.second_operand().unwrap();

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("LessThanEqualExpr: First operand not found");
                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("LessThanEqualExpr: Second operand not found");

                let first_operand_arg = if first_operand_info.is_constant() {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::LessThanEqual)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::GreaterThanExpr(greater_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let first_operand_builder = InstructionArgument::builder();
                let second_operand_builder = InstructionArgument::builder();

                let first_operand = greater_expr.first_operand().unwrap();
                let second_operand = greater_expr.second_operand().unwrap();

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("GreaterThanExpr: First operand not found");
                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("GreaterThanExpr: Second operand not found");

                let first_operand_arg = if first_operand_info.is_constant() {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::GreaterThan)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::GreaterThanEqualExpr(greater_equal_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let first_operand_builder = InstructionArgument::builder();
                let second_operand_builder = InstructionArgument::builder();

                let first_operand = greater_equal_expr.first_operand().unwrap();
                let second_operand = greater_equal_expr.second_operand().unwrap();

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Local)
                    .build()
                    .unwrap();

                let first_operand_info = self
                    .lookup_variable(first_operand.text())
                    .expect("GreaterThanEqualExpr: First operand not found");
                let second_operand_info = self
                    .lookup_variable(second_operand.text())
                    .expect("GreaterThanEqualExpr: Second operand not found");

                let first_operand_arg = if first_operand_info.is_constant() {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::Int(first_operand_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    first_operand_builder
                        .name(first_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&first_operand_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let second_operand_arg = if second_operand_info.is_constant() {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::Int(
                            second_operand_info.get_constant_int(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    second_operand_builder
                        .name(second_operand.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(
                            &second_operand_info.get_storage_class(),
                        ))
                        .build()
                        .unwrap()
                };

                Some(
                    inst_args_builder
                        .name(InstructionName::GreaterThanEqual)
                        .num_args(3)
                        .push_argument(result_arg)
                        .push_argument(first_operand_arg)
                        .push_argument(second_operand_arg),
                )
            }
            Expr::LabelExpr(_) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg_builder = InstructionArgument::builder();

                let arg1 = inst_arg_builder
                    .index(IndexKind::Literal(-1))
                    .name(var_name)
                    .scope(VariableScope::Global)
                    .value(InstructionValue::None)
                    .build()
                    .unwrap();

                let args = inst_args_builder
                    .name(InstructionName::Label)
                    .num_args(1)
                    .push_argument(arg1);

                Some(args)
            }
            // fixme: handle array type
            // LoadExpr will only load to a SSA result ID that has pointer type
            // it will never load to a real variable
            Expr::LoadExpr(load_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                // fixme: better error handling
                let pointer_ssa_id = load_expr.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                // first arg is the pointer to load into
                let result = inst_arg1_builder
                    .name(var_name.clone())
                    // it is intializing a ssa, so the value is None
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Intermediate)
                    .build()
                    .unwrap();

                // second arg is the pointer to load from
                let pointer = inst_arg2_builder
                    .name(pointer_ssa_id.text().to_string() /* .get_var_name()*/)
                    .value(if pointer_info.is_builtin() {
                        InstructionValue::BuiltIn(InstructionBuiltInVariable::cast(
                            pointer_info.get_builtin().unwrap(),
                        ))
                    } else {
                        // as we are loading from a pointer, the value should be None
                        InstructionValue::None
                    })
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&pointer_info.get_storage_class()))
                    .build()
                    .unwrap();

                Some(
                    inst_args_builder
                        .name(InstructionName::Load)
                        .num_args(2)
                        .push_argument(result)
                        .push_argument(pointer),
                )
            }
            Expr::AtomicLoadExpr(atomic_load_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();

                // fixme: better error handling
                let pointer_ssa_id = atomic_load_expr.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                // first arg is the pointer to load into
                let result = inst_arg1_builder
                    .name(var_name.clone())
                    // it is intializing a ssa, so the value is None
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Intermediate)
                    .build()
                    .unwrap();

                // second arg is the pointer to load from
                let pointer = inst_arg2_builder
                    .name(pointer_ssa_id.text().to_string() /* .get_var_name()*/)
                    .value(if pointer_info.is_builtin() {
                        InstructionValue::BuiltIn(InstructionBuiltInVariable::cast(
                            pointer_info.get_builtin().unwrap(),
                        ))
                    } else {
                        // as we are loading from a pointer, the value should be None
                        InstructionValue::None
                    })
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&pointer_info.get_storage_class()))
                    .build()
                    .unwrap();

                Some(
                    inst_args_builder
                        .name(InstructionName::AtomicLoad)
                        .num_args(2)
                        .push_argument(result)
                        .push_argument(pointer),
                )
            }
            // fixme: consider memory scope in the future
            Expr::AtomicExchangeExpr(atomic_exch_expr) => {
                let inst_args_builder = InstructionArguments::builder();
                let result_arg_builder = InstructionArgument::builder();
                let pointer_arg_builder = InstructionArgument::builder();
                let value_arg_builder = InstructionArgument::builder();

                let pointer = atomic_exch_expr.pointer().unwrap();
                let value = atomic_exch_expr.value().unwrap();

                let result_info = self
                    .lookup_variable(&var_name)
                    .expect("AtomicExchangeExpr: Result not found");
                let pointer_info = self
                    .lookup_variable(pointer.text())
                    .expect("AtomicExchangeExpr: Pointer not found");
                let value_info = self
                    .lookup_variable(value.text())
                    .expect("AtomicExchangeExpr: Value not found");

                let result_arg = result_arg_builder
                    .name(var_name.clone())
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&result_info.get_storage_class()))
                    .build()
                    .unwrap();

                let pointer_arg = pointer_arg_builder
                    .name(pointer.text().to_string())
                    .value(InstructionValue::Pointer(
                        pointer.text().to_string(),
                        pointer_info.clone(),
                    ))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&pointer_info.get_storage_class()))
                    .build()
                    .unwrap();

                let value_arg = value_arg_builder
                    .name(value.text().to_string())
                    .value(InstructionValue::Pointer(
                        value.text().to_string(),
                        value_info.clone(),
                    ))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&value_info.get_storage_class()))
                    .build()
                    .unwrap();

                let inst_args = inst_args_builder
                    .name(InstructionName::AtomicExchange)
                    .num_args(3)
                    .push_argument(result_arg)
                    .push_argument(pointer_arg)
                    .push_argument(value_arg);

                Some(inst_args)
            }
            Expr::AtomicCompareExchangeExpr(atomic_cmp_exch_expr) => {
                todo!()
            }
            // todo: implement the rest of the expressions
            _ => unimplemented!(),
        }
    }

    fn generate_code_for_stmt(&mut self, stmt: &Stmt) -> Option<Instruction> {
        match stmt {
            // fixme: handle execution mode
            Stmt::ExecutionMode(_) => None,
            Stmt::ReturnStatement(_) => {
                let args = InstructionArguments::builder()
                    .name(InstructionName::Return)
                    .num_args(0)
                    .build()
                    .unwrap();
                Some(
                    Instruction::builder()
                        .arguments(args)
                        .name(InstructionName::Return)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }

            // Stmt::ExecutionMode(execution_mode) => {
            //     let local_size_x = execution_mode.local_size_x().unwrap().text().parse::<i32>().unwrap();
            //     self.insert_variable("local_size_x".to_string(), VariableInfo::new_const_int("local_size_x".to_string(), local_size_x, false));
            //     None
            // }
            Stmt::VariableDef(var_def) => {
                let inst_builder = Instruction::builder();
                let var_name = var_def.name().unwrap().text().to_string();
                let expr = var_def
                    .value()
                    .expect("Variable definition must have a value");
                let inst_args_builder = self.generate_code_for_expr(var_name, &expr);
                if inst_args_builder.is_none() {
                    None
                } else {
                    let arguments = inst_args_builder.unwrap().build().unwrap();
                    let inst_name = arguments.name.clone();
                    Some(
                        inst_builder
                            .arguments(arguments)
                            .name(inst_name)
                            .scope(InstructionScope::None)
                            .position(self.increment_inst_position())
                            .build()
                            .unwrap(),
                    )
                }
            }
            // decorate statement is used to attach built-in variables/metadata to a variable
            Stmt::DecorateStatement(decorate_stmt) => {
                let name = decorate_stmt.name().unwrap();
                let built_in = decorate_stmt.built_in_var().unwrap();
                // fixme: find a better way to represent built-in variables
                let var_info = VariableInfo::new(
                    // attached variable name is the same as its SSA name
                    name.text().to_string(),
                    SpirvType::Bool,
                    vec![],
                    StorageClass::Global,
                    None,
                    Some(BuiltInVariable::cast(built_in.kind())),
                );

                self.insert_variable(name.text().to_string(), var_info);
                None
            }
            // fixme:: does not support OpAccesschain yet
            Stmt::StoreStatement(store_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();
                // fixme: better error handling
                let pointer_ssa_id = store_stmt.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                let object_ssa_id = store_stmt.object().unwrap();

                self.insert_variable(pointer_ssa_id.text().to_string(), pointer_info.clone());

                // first arg is the pointer to load into
                let pointer_arg = inst_arg1_builder
                    .name(pointer_ssa_id.text().to_string())
                    // it is intializing a ssa, so the value is None
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&pointer_info.get_storage_class()))
                    .build()
                    .unwrap();

                let var_info = self.lookup_variable(object_ssa_id.text()).unwrap();
                let value_arg = if var_info.is_constant() {
                    inst_arg2_builder
                        .name(object_ssa_id.text().to_string())
                        .value(InstructionValue::Int(var_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(object_ssa_id.text().to_string())
                        .value(InstructionValue::Pointer(
                            var_info.get_var_name(),
                            var_info.clone(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&var_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let inst_args = inst_args_builder
                    .name(InstructionName::Store)
                    .num_args(2)
                    .push_argument(pointer_arg)
                    .push_argument(value_arg)
                    .build()
                    .unwrap();
                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::Store)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }
            // fixme:: does not support OpAccesschain yet
            Stmt::AtomicStoreStatement(atomic_store_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();
                // fixme: better error handling
                let pointer_ssa_id = atomic_store_stmt.pointer().unwrap();
                let pointer_info = self.lookup_variable(pointer_ssa_id.text()).unwrap();

                let value_ssa_id = atomic_store_stmt.value().unwrap();

                self.insert_variable(pointer_ssa_id.text().to_string(), pointer_info.clone());

                // first arg is the pointer to load into
                let pointer_arg = inst_arg1_builder
                    .name(pointer_ssa_id.text().to_string())
                    // it is intializing a ssa, so the value is None
                    .value(InstructionValue::None)
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::cast(&pointer_info.get_storage_class()))
                    .build()
                    .unwrap();

                let var_info = self.lookup_variable(value_ssa_id.text()).unwrap();
                let value_arg = if var_info.is_constant() {
                    inst_arg2_builder
                        .name(value_ssa_id.text().to_string())
                        .value(InstructionValue::Int(var_info.get_constant_int()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg2_builder
                        .name(value_ssa_id.text().to_string())
                        .value(InstructionValue::Pointer(
                            var_info.get_var_name(),
                            var_info.clone(),
                        ))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&var_info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let inst_args = inst_args_builder
                    .name(InstructionName::AtomicStore)
                    .num_args(2)
                    .push_argument(pointer_arg)
                    .push_argument(value_arg)
                    .build()
                    .unwrap();
                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::AtomicStore)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }
            Stmt::BranchStatement(branch_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg_builder = InstructionArgument::builder();
                let label = branch_stmt.label().unwrap();
                let label_position = self.lookup_label(label.text()).unwrap();
                let arg = inst_arg_builder
                    .name(label.text().to_string())
                    .value(InstructionValue::Int(label_position.clone() as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();
                let inst_args = inst_args_builder
                    .name(InstructionName::Branch)
                    .num_args(1)
                    .push_argument(arg)
                    .build()
                    .unwrap();
                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::Branch)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }
            Stmt::BranchConditionalStatement(branch_conditional_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let inst_arg2_builder = InstructionArgument::builder();
                let inst_arg3_builder = InstructionArgument::builder();
                let condition = branch_conditional_stmt.condition().unwrap();
                let true_label = branch_conditional_stmt.true_label().unwrap();
                let false_label = branch_conditional_stmt.false_label().unwrap();
                let true_label_position = self.lookup_label(true_label.text()).unwrap();
                let false_label_position = self.lookup_label(false_label.text()).unwrap();

                let info = self.lookup_variable(condition.text()).unwrap();
                let condition_arg = if info.is_constant() {
                    inst_arg1_builder
                        .name(condition.text().to_string())
                        .value(InstructionValue::Bool(info.get_constant_bool()))
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::Literal)
                        .build()
                        .unwrap()
                } else {
                    inst_arg1_builder
                        .name(condition.text().to_string())
                        .value(InstructionValue::None)
                        .index(IndexKind::Literal(-1))
                        .scope(VariableScope::cast(&info.get_storage_class()))
                        .build()
                        .unwrap()
                };

                let truel_label_arg = inst_arg2_builder
                    .name(true_label.text().to_string())
                    .value(InstructionValue::Int(*true_label_position as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();

                let false_label_arg = inst_arg3_builder
                    .name(false_label.text().to_string())
                    .value(InstructionValue::Int(*false_label_position as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();

                let inst_args = inst_args_builder
                    .name(InstructionName::BranchConditional)
                    .num_args(3)
                    .push_argument(condition_arg)
                    .push_argument(truel_label_arg)
                    .push_argument(false_label_arg)
                    .build()
                    .unwrap();

                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::BranchConditional)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }
            Stmt::LoopMergeStatement(loop_merge_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let merge_block_arg_builder = InstructionArgument::builder();
                let continue_block_arg_builder = InstructionArgument::builder();
                let merge_label = loop_merge_stmt.merge_label().unwrap();
                let merge_label_position = self.lookup_label(merge_label.text()).unwrap();
                let continue_label = loop_merge_stmt.continue_label().unwrap();
                let continue_label_position = self.lookup_label(continue_label.text()).unwrap();

                let merge_block_arg = merge_block_arg_builder
                    .name(merge_label.text().to_string())
                    .value(InstructionValue::Int(*merge_label_position as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();

                let continue_block_arg = continue_block_arg_builder
                    .name(continue_label.text().to_string())
                    .value(InstructionValue::Int(*continue_label_position as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();

                let inst_args = inst_args_builder
                    .name(InstructionName::LoopMerge)
                    .num_args(2)
                    .push_argument(merge_block_arg)
                    .push_argument(continue_block_arg)
                    .build()
                    .unwrap();

                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::LoopMerge)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }
            Stmt::SelectionMergeStatement(selection_merge_stmt) => {
                let inst_args_builder = InstructionArguments::builder();
                let inst_arg1_builder = InstructionArgument::builder();
                let merge_label = selection_merge_stmt.merge_label().unwrap();
                let merge_label_position = self.lookup_label(merge_label.text()).unwrap();

                let arg = inst_arg1_builder
                    .name(merge_label.text().to_string())
                    .value(InstructionValue::Int(*merge_label_position as i32))
                    .index(IndexKind::Literal(-1))
                    .scope(VariableScope::Literal)
                    .build()
                    .unwrap();

                let inst_args = inst_args_builder
                    .name(InstructionName::SelectionMerge)
                    .num_args(1)
                    .push_argument(arg)
                    .build()
                    .unwrap();

                Some(
                    Instruction::builder()
                        .arguments(inst_args)
                        .name(InstructionName::SelectionMerge)
                        .scope(InstructionScope::None)
                        .position(self.increment_inst_position())
                        .build()
                        .unwrap(),
                )
            }

            _ => panic!("Unsupported statement: {:?}", stmt),
        }
    }

    pub(crate) fn generate_code(&mut self, root: SyntaxNode) -> Program {
        let mut program_builder = Program::builder();
        let root = Root::cast(root).unwrap();
        // first pass: construct symbol table
        self.symbol_table_construction_pass(&root);
        self.reset_position();

        for stmt in root.stmts() {
            let inst = self.generate_code_for_stmt(&stmt);
            match inst {
                Some(i) => program_builder = program_builder.push_instruction(i),
                None => { /* do nothing */ }
            }
        }

        let global_variables = self.get_global_variables();
        // fixme: remove the hardcoded values
        program_builder
            .global_var(global_variables)
            .num_work_groups(self.num_work_group)
            .work_group_size(self.work_group_size)
            .subgroup_size(self.sub_group_size)
            .num_threads(self.num_work_group * self.work_group_size)
            .scheduler(Scheduler::OBE)
            .build()
            .unwrap()
    }

    pub(crate) fn get_global_variables(&self) -> Vec<VariableInfo> {
        self.variable_table.get_global_variables()
    }
}

#[cfg(test)]
mod test {
    use crate::codegen::common::IndexKind;
    use crate::codegen::common::InstructionName;
    use crate::codegen::common::InstructionScope;
    use crate::codegen::common::Scheduler;
    use crate::codegen::common::VariableScope;
    use crate::codegen::context::AccessStep;
    use crate::codegen::context::InstructionBuiltInVariable::SubgroupLocalInvocationId;
    use crate::codegen::context::InstructionValue;
    use crate::codegen::context::VariableInfo;
    use crate::compiler::parse::parser::parse;
    use crate::compiler::parse::symbol_table::SpirvType;
    use crate::compiler::parse::symbol_table::StorageClass;

    use super::CodegenCx;
    fn check(input: &str, expected_tree: expect_test::Expect) {
        let parse = parse(input);
        expected_tree.assert_eq(&parse.debug_tree());
    }

    #[test]
    fn check_basic_type_symbol_table() {
        CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let input = "%uint = OpTypeInt 32 0
         %uint_0 = OpVariable %uint Function
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::OBE);
        let program = codegen_ctx.generate_code(syntax);
        // let basic_type = program.instructions.get(0).unwrap();
        let variable_decl = program.instructions.get(0).unwrap();
        assert_eq!(variable_decl.name, InstructionName::Assignment);
        assert_eq!(variable_decl.arguments.num_args, 1);
        assert_eq!(variable_decl.arguments.arguments[0].name, "%uint_0");
        assert_eq!(
            variable_decl.arguments.arguments[0].value,
            InstructionValue::Int(0)
        );
        assert_eq!(
            variable_decl.arguments.arguments[0].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            variable_decl.arguments.arguments[0].scope,
            VariableScope::Local
        );
    }

    #[test]
    fn check_high_level_type_symbol_table() {
        CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let input = "%uint = OpTypeInt 32 0
         %v3uint = OpTypeVector %uint 30
         %_ptr_Input_v3uint = OpTypePointer Input %v3uint
         %v3uint_0 = OpVariable %_ptr_Input_v3uint Function
        ";

        let syntax = parse(input).syntax();
        // let root = Root::cast(syntax).unwrap();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        // let basic_type = program.instructions.get(0).unwrap();
        let variable_decl = program.instructions.get(0).unwrap();
        assert_eq!(variable_decl.name, InstructionName::Assignment);
        assert_eq!(variable_decl.arguments.num_args, 1);
        assert_eq!(variable_decl.arguments.arguments[0].name, "%v3uint_0");
        assert_eq!(
            variable_decl.arguments.arguments[0].value,
            InstructionValue::Int(0)
        );
        assert_eq!(
            variable_decl.arguments.arguments[0].index,
            IndexKind::Literal(30)
        );
        assert_eq!(
            variable_decl.arguments.arguments[0].scope,
            VariableScope::Local
        );
    }

    #[test]
    fn check_return() {
        let input = "%int = OpTypeInt 32 1
        OpReturn
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let return_stmt = program.instructions.get(0).unwrap();
        assert_eq!(return_stmt.name, InstructionName::Return);
    }
    #[test]
    fn check_constant() {
        let input = "%int = OpTypeInt 32 1
        %11 = OpConstant %int -5 
        ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        codegen_ctx.generate_code(syntax);
        assert_ne!(codegen_ctx.lookup_variable("%11"), None);
        let const_val = codegen_ctx.lookup_variable("%11").unwrap();
        assert_eq!(const_val.get_constant_int(), -5);
    }

    #[test]
    fn check_constant_true() {
        let input = "%bool = OpTypeBool
        %11 = OpConstantTrue %bool
        ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        codegen_ctx.generate_code(syntax);
        assert_ne!(codegen_ctx.lookup_variable("%11"), None);
        let const_val = codegen_ctx.lookup_variable("%11").unwrap();
        assert_eq!(const_val.get_constant_bool(), true);
    }

    #[test]
    fn check_constant_false() {
        let input = "%bool = OpTypeBool
        %11 = OpConstantFalse %bool
        ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        codegen_ctx.generate_code(syntax);
        assert_ne!(codegen_ctx.lookup_variable("%11"), None);
        let const_val = codegen_ctx.lookup_variable("%11").unwrap();
        assert_eq!(const_val.get_constant_bool(), false);
    }

    #[test]
    fn check_built_in_load() {
        CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let input = "OpDecorate %gl_SubgroupInvocationID BuiltIn SubgroupLocalInvocationId
         %uint = OpTypeInt 32 0
         %_ptr_Input_uint = OpTypePointer Input %uint
         %gl_SubgroupInvocationID = OpVariable %_ptr_Input_uint Input
         %11 = OpLoad %uint %gl_SubgroupInvocationID
        ";

        let syntax = parse(input).syntax();
        // let root = Root::cast(syntax).unwrap();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let builtin_variable_decl = program.instructions.get(0).unwrap();

        assert_eq!(builtin_variable_decl.name, InstructionName::Assignment);
        assert_eq!(builtin_variable_decl.arguments.num_args, 1);
        assert_eq!(
            builtin_variable_decl.arguments.arguments[0].name,
            "%gl_SubgroupInvocationID"
        );
        assert_eq!(
            builtin_variable_decl.arguments.arguments[0].value,
            InstructionValue::BuiltIn(SubgroupLocalInvocationId)
        );
        assert_eq!(
            builtin_variable_decl.arguments.arguments[0].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            builtin_variable_decl.arguments.arguments[0].scope,
            VariableScope::Global
        );

        let var_load = program.instructions.get(1).unwrap();
        assert_eq!(var_load.arguments.num_args, 2);
        assert_eq!(var_load.arguments.arguments[0].name, "%11");
        assert_eq!(
            var_load.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            var_load.arguments.arguments[0].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            var_load.arguments.arguments[0].scope,
            VariableScope::Intermediate
        );

        assert_eq!(
            var_load.arguments.arguments[1].name,
            "%gl_SubgroupInvocationID"
        );
        assert_eq!(
            var_load.arguments.arguments[1].value,
            InstructionValue::BuiltIn(SubgroupLocalInvocationId)
        );
        assert_eq!(
            var_load.arguments.arguments[1].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(var_load.arguments.arguments[1].scope, VariableScope::Global);
    }

    #[test]
    fn check_store_constant() {
        let input = "%int = OpTypeInt 32 1
        %11 = OpConstant %int -5
        %_ptr_Function_uint = OpTypePointer Function %int
        %idx = OpVariable %_ptr_Function_uint Function
        OpStore %idx %11
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let store = program.instructions.get(1).unwrap();
        assert_eq!(store.arguments.num_args, 2);
        assert_eq!(store.arguments.arguments[0].name, "%idx");
        assert_eq!(store.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(store.arguments.arguments[0].index, IndexKind::Literal(-1));
        assert_eq!(store.arguments.arguments[0].scope, VariableScope::Local);

        assert_eq!(store.arguments.arguments[1].name, "%11");
        assert_eq!(
            store.arguments.arguments[1].value,
            InstructionValue::Int(-5)
        );
        assert_eq!(store.arguments.arguments[1].index, IndexKind::Literal(-1));
        assert_eq!(store.arguments.arguments[1].scope, VariableScope::Literal);
    }

    #[test]
    fn check_store_variable() {
        let input = "%uint = OpTypeInt 32 0
        %uint_0 = OpVariable %uint Function
        %_ptr_Function_uint = OpTypePointer Function %uint
        %idx = OpVariable %_ptr_Function_uint Function
        OpStore %idx %uint_0
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let store = program.instructions.get(2).unwrap();
        assert_eq!(store.arguments.num_args, 2);
        assert_eq!(store.arguments.arguments[0].name, "%idx");
        assert_eq!(store.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(store.arguments.arguments[0].index, IndexKind::Literal(-1));
        assert_eq!(store.arguments.arguments[0].scope, VariableScope::Local);

        assert_eq!(store.arguments.arguments[1].name, "%uint_0");
        assert_eq!(
            store.arguments.arguments[1].value,
            InstructionValue::Pointer(
                "%uint_0".to_string(),
                VariableInfo::new(
                    "%uint_0".to_string(),
                    SpirvType::Int {
                        width: 32,
                        signed: false
                    },
                    vec![],
                    StorageClass::Local,
                    None,
                    None
                )
            )
        );
        assert_eq!(store.arguments.arguments[1].index, IndexKind::Literal(-1));
        assert_eq!(store.arguments.arguments[1].scope, VariableScope::Local);
    }

    #[test]
    fn check_access_chain() {
        let input = "%uint = OpTypeInt 32 0
         %v3uint = OpTypeVector %uint 30
         %_ptr_Input_v3uint = OpTypePointer Input %v3uint
         %_ptr_Input_uint = OpTypePointer Workgroup %uint
         %v3uint_0 = OpVariable %_ptr_Input_v3uint Function
         %10 = OpConstant %uint 2
         %11 = OpAccessChain %_ptr_Input_uint %v3uint_0 %10
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        codegen_ctx.generate_code(syntax);
        let var_info = codegen_ctx.lookup_variable("%11");
        assert_ne!(var_info, None);
        let var_info = var_info.unwrap();
        assert_eq!(var_info.id, "%v3uint_0");
        assert_eq!(
            var_info.ty,
            SpirvType::Pointer {
                ty: "%uint".to_string(),
                storage_class: StorageClass::Shared
            }
        );
        assert_eq!(var_info.access_chain.len(), 1);
        assert_eq!(var_info.access_chain[0], AccessStep::ConstIndex(2));
    }

    /*
    layout(std140, binding = 0) uniform UBO {
    float data[10];
    int indices[10];
    };

    void main() {
    int index = int(gl_FragCoord.x);

    // First load: load an index from the 'indices' array
    int tempIndex = indices[index];  // Load index

    // Second load: use the loaded index to load from 'data'
    float value = data[tempIndex];   // Load value using tempIndex
    }
     */
    // #[test]
    // fn check_load_with_access_chain() {
    //     let input = "%ptr1 = OpAccessChain %_ptr_Uniform_int %UBO %index
    //         %tempIndex = OpLoad %int %ptr1
    //         %ptr2 = OpAccessChain %_ptr_Uniform_float %UBO %tempIndex
    //         %value = OpLoad %float %ptr2
    //         ";
    //     todo!()
    // }

    #[test]
    fn check_label() {
        let input = "%uint = OpTypeInt 32 0
        %v3uint = OpTypeVector %uint 30
        %_ptr_Input_v3uint = OpTypePointer Input %v3uint
        %_ptr_Input_uint = OpTypePointer Workgroup %uint
        %v3uint_0 = OpVariable %_ptr_Input_v3uint Function
        %1 = OpLabel
        ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let label = program.instructions.get(1).unwrap();
        assert_eq!(label.arguments.num_args, 1);
        assert_eq!(label.arguments.arguments[0].name, "%1");
        assert_ne!(codegen_ctx.lookup_label("%1"), None);
        let label = codegen_ctx.lookup_label("%1").unwrap();
        assert_eq!(label, &2);
    }

    #[test]
    fn check_branch() {
        let input = "%1 = OpLabel
        %2 = OpLabel
        OpBranch %2
        ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let branch = program.instructions.get(2).unwrap();
        assert_eq!(branch.arguments.num_args, 1);
        assert_eq!(branch.arguments.arguments[0].name, "%2");
        assert_eq!(
            branch.arguments.arguments[0].value,
            InstructionValue::Int(2)
        );
        assert_eq!(branch.arguments.arguments[0].index, IndexKind::Literal(-1));
        assert_eq!(branch.arguments.arguments[0].scope, VariableScope::Literal);
    }

    #[test]
    fn check_branch_conditional() {
        let intput = "%1 = OpLabel
        %2 = OpLabel
        %bool = OpTypeBool
        %true = OpConstantTrue %bool
        %v3uint = OpTypeVector %uint 30
        OpBranchConditional %true %1 %2
        ";

        let syntax = parse(intput).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let branch_conditional = program.instructions.get(2).unwrap();
        assert_eq!(branch_conditional.arguments.num_args, 3);
        assert_eq!(branch_conditional.arguments.arguments[0].name, "%true");
        assert_eq!(
            branch_conditional.arguments.arguments[0].value,
            InstructionValue::Bool(true)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[0].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[0].scope,
            VariableScope::Literal
        );

        assert_eq!(branch_conditional.arguments.arguments[1].name, "%1");
        assert_eq!(
            branch_conditional.arguments.arguments[1].value,
            InstructionValue::Int(1)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[1].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[1].scope,
            VariableScope::Literal
        );

        assert_eq!(branch_conditional.arguments.arguments[2].name, "%2");
        assert_eq!(
            branch_conditional.arguments.arguments[2].value,
            InstructionValue::Int(2)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[2].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            branch_conditional.arguments.arguments[2].scope,
            VariableScope::Literal
        );
    }

    #[test]
    fn check_selection_merge() {
        let input = "%1 = OpLabel
        %2 = OpLabel
        OpSelectionMerge %2 None
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let selection_merge = program.instructions.get(2).unwrap();
        assert_eq!(selection_merge.arguments.num_args, 1);
        assert_eq!(selection_merge.arguments.arguments[0].name, "%2");
        assert_eq!(
            selection_merge.arguments.arguments[0].value,
            InstructionValue::Int(2)
        );
        assert_eq!(
            selection_merge.arguments.arguments[0].index,
            IndexKind::Literal(-1)
        );
        assert_eq!(
            selection_merge.arguments.arguments[0].scope,
            VariableScope::Literal
        );
    }

    #[test]
    fn check_add() {
        let input = "%int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %sum = OpIAdd %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let add = program.instructions.get(0).unwrap();
        assert_eq!(add.arguments.num_args, 3);
        assert_eq!(add.arguments.arguments[0].name, "%sum");
        assert_eq!(add.arguments.arguments[1].name, "%3");
        assert_eq!(add.arguments.arguments[2].name, "%5");
        assert_eq!(add.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(add.arguments.arguments[1].value, InstructionValue::Int(3));
        assert_eq!(add.arguments.arguments[2].value, InstructionValue::Int(5));
        assert_eq!(add.scope, InstructionScope::None);
        assert_eq!(add.name, InstructionName::Add);
    }

    #[test]
    fn check_sub() {
        let input = "%int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %sub = OpISub %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let sub = program.instructions.get(0).unwrap();
        assert_eq!(sub.arguments.num_args, 3);
        assert_eq!(sub.arguments.arguments[0].name, "%sub");
        assert_eq!(sub.arguments.arguments[1].name, "%3");
        assert_eq!(sub.arguments.arguments[2].name, "%5");
        assert_eq!(sub.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(sub.arguments.arguments[1].value, InstructionValue::Int(3));
        assert_eq!(sub.arguments.arguments[2].value, InstructionValue::Int(5));
        assert_eq!(sub.scope, InstructionScope::None);
        assert_eq!(sub.name, InstructionName::Sub);
    }

    #[test]
    fn check_mul() {
        let input = "%int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %mul = OpIMul %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let mul = program.instructions.get(0).unwrap();
        assert_eq!(mul.arguments.num_args, 3);
        assert_eq!(mul.arguments.arguments[0].name, "%mul");
        assert_eq!(mul.arguments.arguments[1].name, "%3");
        assert_eq!(mul.arguments.arguments[2].name, "%5");
        assert_eq!(mul.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(mul.arguments.arguments[1].value, InstructionValue::Int(3));
        assert_eq!(mul.arguments.arguments[2].value, InstructionValue::Int(5));
        assert_eq!(mul.scope, InstructionScope::None);
        assert_eq!(mul.name, InstructionName::Mul);
    }

    #[test]
    fn check_equal() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %equal = OpIEqual %bool %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let equal = program.instructions.get(0).unwrap();
        assert_eq!(equal.arguments.num_args, 3);
        assert_eq!(equal.arguments.arguments[0].name, "%equal");
        assert_eq!(equal.arguments.arguments[1].name, "%3");
        assert_eq!(equal.arguments.arguments[2].name, "%5");
        assert_eq!(equal.arguments.arguments[0].value, InstructionValue::None);
        assert_eq!(equal.arguments.arguments[1].value, InstructionValue::Int(3));
        assert_eq!(equal.arguments.arguments[2].value, InstructionValue::Int(5));
        assert_eq!(equal.scope, InstructionScope::None);
        assert_eq!(equal.name, InstructionName::Equal);
    }

    #[test]
    fn check_not_equal() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %not_equal = OpINotEqual %bool %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let not_equal = program.instructions.get(0).unwrap();
        assert_eq!(not_equal.arguments.num_args, 3);
        assert_eq!(not_equal.arguments.arguments[0].name, "%not_equal");
        assert_eq!(not_equal.arguments.arguments[1].name, "%3");
        assert_eq!(not_equal.arguments.arguments[2].name, "%5");
        assert_eq!(
            not_equal.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            not_equal.arguments.arguments[1].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            not_equal.arguments.arguments[2].value,
            InstructionValue::Int(5)
        );
        assert_eq!(not_equal.scope, InstructionScope::None);
        assert_eq!(not_equal.name, InstructionName::NotEqual);
    }

    #[test]
    fn check_less_than() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %less_than = OpSLessThan %bool %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let less_than = program.instructions.get(0).unwrap();
        assert_eq!(less_than.arguments.num_args, 3);
        assert_eq!(less_than.arguments.arguments[0].name, "%less_than");
        assert_eq!(less_than.arguments.arguments[1].name, "%3");
        assert_eq!(less_than.arguments.arguments[2].name, "%5");
        assert_eq!(
            less_than.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            less_than.arguments.arguments[1].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            less_than.arguments.arguments[2].value,
            InstructionValue::Int(5)
        );
        assert_eq!(less_than.scope, InstructionScope::None);
        assert_eq!(less_than.name, InstructionName::LessThan);
    }

    #[test]
    fn check_less_than_equal() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %less_than_equal = OpSLessThanEqual %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let less_than_equal = program.instructions.get(0).unwrap();
        assert_eq!(less_than_equal.arguments.num_args, 3);
        assert_eq!(
            less_than_equal.arguments.arguments[0].name,
            "%less_than_equal"
        );
        assert_eq!(less_than_equal.arguments.arguments[1].name, "%3");
        assert_eq!(less_than_equal.arguments.arguments[2].name, "%5");
        assert_eq!(
            less_than_equal.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            less_than_equal.arguments.arguments[1].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            less_than_equal.arguments.arguments[2].value,
            InstructionValue::Int(5)
        );
        assert_eq!(less_than_equal.scope, InstructionScope::None);
        assert_eq!(less_than_equal.name, InstructionName::LessThanEqual);
    }

    #[test]
    fn check_greater_than() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %greater_than = OpSGreaterThan %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let greater_than = program.instructions.get(0).unwrap();
        assert_eq!(greater_than.arguments.num_args, 3);
        assert_eq!(greater_than.arguments.arguments[0].name, "%greater_than");
        assert_eq!(greater_than.arguments.arguments[1].name, "%3");
        assert_eq!(greater_than.arguments.arguments[2].name, "%5");
        assert_eq!(
            greater_than.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            greater_than.arguments.arguments[1].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            greater_than.arguments.arguments[2].value,
            InstructionValue::Int(5)
        );
        assert_eq!(greater_than.scope, InstructionScope::None);
        assert_eq!(greater_than.name, InstructionName::GreaterThan);
    }

    #[test]
    fn check_greater_than_equal() {
        let input = "%bool = OpTypeBool
        %int = OpTypeInt 32 1
        %3 = OpConstant %int 3
        %5 = OpConstant %int 5
        %greater_than_equal = OpSGreaterThanEqual %int %3 %5
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let greater_than_equal = program.instructions.get(0).unwrap();
        assert_eq!(greater_than_equal.arguments.num_args, 3);
        assert_eq!(
            greater_than_equal.arguments.arguments[0].name,
            "%greater_than_equal"
        );
        assert_eq!(greater_than_equal.arguments.arguments[1].name, "%3");
        assert_eq!(greater_than_equal.arguments.arguments[2].name, "%5");
        assert_eq!(
            greater_than_equal.arguments.arguments[0].value,
            InstructionValue::None
        );
        assert_eq!(
            greater_than_equal.arguments.arguments[1].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            greater_than_equal.arguments.arguments[2].value,
            InstructionValue::Int(5)
        );
        assert_eq!(greater_than_equal.scope, InstructionScope::None);
        assert_eq!(greater_than_equal.name, InstructionName::GreaterThanEqual);
    }

    #[test]
    fn check_loop_merge() {
        let input = "OpLoopMerge %15 %16 None
  %16 = OpLabel
  %15 = OpLabel";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let loop_merge = program.instructions.get(0).unwrap();
        assert_eq!(loop_merge.arguments.num_args, 2);
        assert_eq!(loop_merge.arguments.arguments[0].name, "%15");
        assert_eq!(loop_merge.arguments.arguments[1].name, "%16");
        assert_eq!(
            loop_merge.arguments.arguments[0].value,
            InstructionValue::Int(3)
        );
        assert_eq!(
            loop_merge.arguments.arguments[1].value,
            InstructionValue::Int(2)
        );
        assert_eq!(loop_merge.scope, InstructionScope::None);
        assert_eq!(loop_merge.name, InstructionName::LoopMerge);
    }

    #[test]
    fn check_atomic_exchange() {
        let input = "%uint = OpTypeInt 32 0
%_ptr_Workgroup_uint = OpTypePointer Workgroup %uint
     %lock = OpVariable %_ptr_Workgroup_uint Workgroup
   %uint_0 = OpConstant %uint 0
   %uint_1 = OpConstant %uint 1
       %17 = OpAtomicExchange %uint %lock %uint_1 %uint_0 %uint_1
       ";

        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        let atomic_exchange = program.instructions.get(1).unwrap();
        assert_eq!(atomic_exchange.arguments.num_args, 3);
        assert_eq!(atomic_exchange.arguments.arguments[0].name, "%17");
        assert_eq!(atomic_exchange.arguments.arguments[1].name, "%lock");
        assert_eq!(atomic_exchange.arguments.arguments[2].name, "%uint_1");
        assert_eq!(atomic_exchange.scope, InstructionScope::None);
        assert_eq!(atomic_exchange.name, InstructionName::AtomicExchange);
    }

    #[test]
    fn check_producer_consumer() {
        let input = "; SPIR-V
; Version: 1.0
; Generator: Khronos Glslang Reference Front End; 11
; Bound: 24
; Schema: 0
               OpCapability Shader
          %1 = OpExtInstImport \"GLSL.std.450\"
               OpMemoryModel Logical GLSL450
               OpEntryPoint GLCompute %main \"main\"
               OpExecutionMode %main LocalSize 256 1 1
               OpSource GLSL 450
               OpSourceExtension \"GL_KHR_shader_subgroup_basic\"
               OpName %main \"main\"
               OpName %lock \"lock\"
               OpName %old \"old\"
               OpDecorate %gl_WorkGroupSize BuiltIn WorkgroupSize
       %void = OpTypeVoid
          %3 = OpTypeFunction %void
       %uint = OpTypeInt 32 0
%_ptr_Workgroup_uint = OpTypePointer Workgroup %uint
       %lock = OpVariable %_ptr_Workgroup_uint Workgroup
     %uint_0 = OpConstant %uint 0
%_ptr_Function_uint = OpTypePointer Function %uint
     %uint_1 = OpConstant %uint 1
       %bool = OpTypeBool
     %v3uint = OpTypeVector %uint 3
   %uint_256 = OpConstant %uint 256
       %main = OpFunction %void None %3
          %5 = OpLabel
        %old = OpVariable %_ptr_Function_uint Function
               OpStore %lock %uint_0
               OpStore %old %uint_1
               OpBranch %13
         %13 = OpLabel
               OpLoopMerge %15 %16 None
               OpBranch %14
         %14 = OpLabel
         %17 = OpAtomicExchange %uint %lock %uint_1 %uint_0 %uint_1
               OpStore %old %17
               OpBranch %16
         %16 = OpLabel
         %18 = OpLoad %uint %old
         %20 = OpINotEqual %bool %18 %uint_0
               OpBranchConditional %20 %13 %15
         %15 = OpLabel
               OpStore %lock %uint_1
               OpReturn
               OpFunctionEnd
        ";
        let syntax = parse(input).syntax();
        let mut codegen_ctx = CodegenCx::new(1, 1, 1, Scheduler::HSA);
        let program = codegen_ctx.generate_code(syntax);
        assert_eq!(program.instructions.len(), 20);
        let lock_var_def = program.instructions.get(0).unwrap();
        assert_eq!(lock_var_def.name, InstructionName::Assignment);
        assert_eq!(lock_var_def.arguments.num_args, 1);
        assert_eq!(lock_var_def.arguments.arguments[0].name, "%lock");
        assert_eq!(
            lock_var_def.arguments.arguments[0].value,
            InstructionValue::Int(0)
        );
        assert_eq!(
            lock_var_def.arguments.arguments[0].scope,
            VariableScope::Shared
        );

        let atomic_exchange = program.instructions.get(1).unwrap();
        todo!()
    }
}
