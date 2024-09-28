//! common is used to stored the common program information(e.g. number of blocks, subgroup size, thread numbers,...) in the codegen module.

use super::constant::Constant;
use crate::compiler::parse::symbol_table::{
    BuiltInVariable, ConstantInfo, StorageClass, VariableInfo,
};
use camino::Utf8Path;
use eyre::{eyre, Report, Result};
use smallvec::SmallVec;
use std::fmt::Display;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::str::FromStr;

static LAYOUT_CONFIG_HINT: &str = "(* Layout Configuration *)";
static PROGRAM_HINT: &str = "(* Program *)";
static GLOBAL_VARIABLES_HINT: &str = "(* Global Variables *)";

#[derive(Debug)]
pub enum BinaryExpr {
    Add,
    Sub,
    Mul,
    Div,
    NotEqual,
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum InstructionName {
    Assignment,
    Return,
    Load,
    Store,
    AtomicLoad,
    AtomicStore,
    Branch,
    BranchConditional,
    Label,
    SelectionMerge,
    LoopMerge,
    LogicalNot,
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Add,
    Sub,
    Mul,
    AtomicExchange,
    AtomicCompareExchange,
    GroupAll,
    GroupNonUniformAll,
}

impl Display for InstructionName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionName::Assignment => write!(f, "Assignment"),
            InstructionName::Return => write!(f, "Terminate"),
            // InstructionName::Load => write!(f, "OpLoad"),
            // InstructionName::Store => write!(f, "OpStore"),
            InstructionName::Load | InstructionName::AtomicLoad => write!(f, "OpAtomicLoad"),
            &InstructionName::Store | InstructionName::AtomicStore => write!(f, "OpAtomicStore"),
            InstructionName::Branch => write!(f, "OpBranch"),
            InstructionName::BranchConditional => write!(f, "OpBranchConditional"),
            InstructionName::Label => write!(f, "OpLabel"),
            InstructionName::SelectionMerge => write!(f, "OpSelectionMerge"),
            InstructionName::LoopMerge => write!(f, "OpLoopMerge"),
            InstructionName::LogicalNot => write!(f, "OpLogicalNot"),
            InstructionName::Equal => write!(f, "OpEqual"),
            InstructionName::NotEqual => write!(f, "OpNotEqual"),
            InstructionName::LessThan => write!(f, "OpLess"),
            InstructionName::LessThanEqual => write!(f, "OpLessOrEqual"),
            InstructionName::GreaterThan => write!(f, "OpGreater"),
            InstructionName::GreaterThanEqual => write!(f, "OpGreaterOrEqual"),
            InstructionName::Add => write!(f, "OpAdd"),
            InstructionName::Sub => write!(f, "OpSub"),
            InstructionName::Mul => write!(f, "OpMul"),
            InstructionName::AtomicExchange => write!(f, "OpAtomicExchange"),
            InstructionName::AtomicCompareExchange => write!(f, "OpAtomicCompareExchange"),
            InstructionName::GroupAll => write!(f, "OpGroupAll"),
            InstructionName::GroupNonUniformAll => write!(f, "OpGroupNonUniformAll"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum VariableScope {
    Intermediate,
    Local,
    Shared,
    Global,
    Literal,
}

impl Display for VariableScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableScope::Intermediate => write!(f, "intermediate"),
            VariableScope::Local => write!(f, "local"),
            VariableScope::Shared => write!(f, "shared"),
            VariableScope::Global => write!(f, "global"),
            VariableScope::Literal => write!(f, "literal"),
        }
    }
}

impl VariableScope {
    pub fn cast(storage_class: &StorageClass) -> Self {
        match storage_class {
            StorageClass::Global => VariableScope::Global,
            StorageClass::Local => VariableScope::Local,
            StorageClass::Shared => VariableScope::Shared,
            StorageClass::Intermediate => VariableScope::Intermediate,
            StorageClass::Constant => VariableScope::Literal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExecutionScope {
    // CrossDevice = 0,
    // Device = 1,
    WorkGroup = 2,
    SubGroup = 3,
    Invocation = 4,
    None,
}

impl From<i32> for ExecutionScope {
    fn from(value: i32) -> Self {
        match value {
            2 => ExecutionScope::WorkGroup,
            3 => ExecutionScope::SubGroup,
            4 => ExecutionScope::Invocation,
            _ => ExecutionScope::None,
        }
    }
}

impl Display for ExecutionScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // ExecutionScope::CrossDevice => write!(f, "CrossDevice"),
            // ExecutionScope::Device => write!(f, "Device"),
            ExecutionScope::WorkGroup => write!(f, "workgroup"),
            ExecutionScope::SubGroup => write!(f, "subgroup"),
            ExecutionScope::Invocation => write!(f, "invocation"),
            ExecutionScope::None => write!(f, "none"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum InstructionBuiltInVariable {
    NumWorkgroups,
    WorkgroupSize,
    WorkgroupId,
    LocalInvocationId,
    GlobalInvocationId,
    SubgroupSize,
    NumSubgroups,
    SubgroupId,
    SubgroupLocalInvocationId,
}

impl Display for InstructionBuiltInVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionBuiltInVariable::NumWorkgroups => write!(f, "NumWorkGroups"),
            InstructionBuiltInVariable::WorkgroupSize => write!(f, "WorkGroupSize"),
            InstructionBuiltInVariable::SubgroupSize => write!(f, "SubgroupSize"),
            InstructionBuiltInVariable::NumSubgroups => write!(f, "NumSubgroups"),
            InstructionBuiltInVariable::WorkgroupId => write!(f, "WorkGroupId(t)"),
            InstructionBuiltInVariable::LocalInvocationId => write!(f, "LocalInvocationId(t)"),
            InstructionBuiltInVariable::GlobalInvocationId => write!(f, "GlobalInvocationId(t)"),
            InstructionBuiltInVariable::SubgroupId => write!(f, "SubgroupId(t)"),
            InstructionBuiltInVariable::SubgroupLocalInvocationId => {
                write!(f, "SubgroupInvocationId(t)")
            }
        }
    }
}

impl InstructionBuiltInVariable {
    pub(crate) fn cast(var: BuiltInVariable) -> Self {
        match var {
            BuiltInVariable::NumWorkgroups => InstructionBuiltInVariable::NumWorkgroups,
            BuiltInVariable::WorkgroupSize => InstructionBuiltInVariable::WorkgroupSize,
            BuiltInVariable::WorkgroupId => InstructionBuiltInVariable::WorkgroupId,
            BuiltInVariable::LocalInvocationId => InstructionBuiltInVariable::LocalInvocationId,
            BuiltInVariable::GlobalInvocationId => InstructionBuiltInVariable::GlobalInvocationId,
            BuiltInVariable::SubgroupSize => InstructionBuiltInVariable::SubgroupSize,
            BuiltInVariable::NumSubgroups => InstructionBuiltInVariable::NumSubgroups,
            BuiltInVariable::SubgroupId => InstructionBuiltInVariable::SubgroupId,
            BuiltInVariable::SubgroupLocalInvocationId => {
                InstructionBuiltInVariable::SubgroupLocalInvocationId
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum IndexKind {
    Literal(i32),
    Variable(String),
}

impl Display for IndexKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IndexKind::Literal(value) => write!(f, "Index({})", value),
            IndexKind::Variable(name) => write!(f, "{}", name),
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
pub enum InstructionValue {
    None,
    // Pointer(String),
    BuiltIn(InstructionBuiltInVariable),
    Bool(bool),
    String(String),
    Int(i32),
    UInt(u32),
}

impl Display for InstructionValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionValue::None => write!(f, "\"\""),
            // InstructionValue::Pointer(name) => write!(f, "\"\""),
            InstructionValue::BuiltIn(var) => write!(f, "{}", var),
            InstructionValue::Bool(value) => {
                if *value {
                    write!(f, "TRUE")
                } else {
                    write!(f, "FALSE")
                }
            }
            InstructionValue::Int(value) => write!(f, "{}", value),
            InstructionValue::UInt(value) => write!(f, "{}", value),
            InstructionValue::String(value) => write!(f, "\"{}\"", value),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Scheduler {
    OBE,
    HSA,
}
impl std::fmt::Display for Scheduler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Scheduler::OBE => write!(f, "\"OBE\""),
            Scheduler::HSA => write!(f, "\"HSA\""),
        }
    }
}

impl FromStr for Scheduler {
    type Err = Report;
    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "hsa" => Ok(Self::HSA),
            "obe" => Ok(Self::OBE),
            _ => Err(eyre!("Invalid scheduler: {}", s)),
        }
    }
}
#[derive(Debug)]
pub struct InstructionArgument {
    pub name: String,
    pub scope: VariableScope,
    pub value: InstructionValue,
    pub index: IndexKind,
}

impl Display for InstructionArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Var(\"{}\", \"{}\", {}, {})",
            self.scope, self.name, self.value, self.index
        )
    }
}
#[derive(Debug)]
pub struct InstructionArguments {
    pub name: InstructionName,
    pub num_args: u32,
    pub arguments: SmallVec<[InstructionArgument; 4]>,
}

impl Display for InstructionArguments {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<<")?;
        for idx in 0..self.arguments.len() {
            write!(f, "{}", self.arguments[idx])?;
            if idx != self.arguments.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ">>")
    }
}

#[derive(Debug)]
pub struct Instruction {
    pub position: u32,
    pub name: InstructionName,
    pub scope: ExecutionScope,
    pub arguments: InstructionArguments,
}

#[derive(Debug)]
pub struct Thread {
    pub instructions: SmallVec<[Instruction; 10]>,
}

/// `Program` is a struct that holds the program information.
/// `subgroup_size: u32` is the size of the subgroup.
/// `work_group_size: u32` is the size of the work group.
/// `num_work_groups: u32` is the number of work groups.
/// `num_threads: u32` is the number of threads.
/// `scheduler: Scheduler` is the scheduler type.
/// `thread: Vec<Thread>` is a vector of threads.
/// `constants: Vec<Constant>` is a vector of constants.
#[derive(Debug)]
pub struct Program {
    pub global_vars: Vec<VariableInfo>,
    pub subgroup_size: u32,
    pub work_group_size: u32,
    pub num_work_groups: u32,
    pub num_threads: u32,
    pub scheduler: Scheduler,
    pub instructions: SmallVec<[Instruction; 10]>,
    pub constants: SmallVec<[Constant; 10]>,
}

impl Program {
    fn write_layout(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write layout information to the lines
        writeln!(writer, "SubgroupSize == {}", self.subgroup_size)?;
        writeln!(writer, "WorkGroupSize == {}", self.work_group_size)?;
        writeln!(writer, "NumWorkGroups == {}", self.num_work_groups)?;
        writeln!(
            writer,
            "NumSubgroups == {}",
            self.num_work_groups * self.work_group_size / self.subgroup_size
        )?;
        writeln!(writer, "NumThreads == {}", self.num_threads)?;
        writeln!(writer, "Scheduler == {}", self.scheduler)?;
        Ok(())
    }
    fn write_global_variables(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write global variables to the lines
        writeln!(writer, "InitGPU == ")?;
        writeln!(writer, "\tglobalVars = {{")?;
        for (idx, global_var) in self.global_vars.iter().enumerate() {
            if idx != self.global_vars.len() - 1 {
                writeln!(
                    writer,
                    "\t\tVar(\"{}\", \"{}\", {}, {}),",
                    global_var.get_storage_class(),
                    global_var.get_var_name(),
                    global_var.initial_value(),
                    global_var.get_index(),
                )?;
            } else {
                writeln!(
                    writer,
                    "\t\tVar(\"{}\", \"{}\", {}, {})",
                    global_var.get_storage_class(),
                    global_var.get_var_name(),
                    global_var.initial_value(),
                    global_var.get_index(),
                )?;
            }
        }
        writeln!(writer, "\t}}")?;
        Ok(())
    }
    fn write_program(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write instructions to the lines
        writeln!(
            writer,
            r"ThreadInstructions ==  [t \in 1..NumThreads |-> <<"
        )?;
        for (idx, inst) in self.instructions.iter().enumerate() {
            if idx != self.instructions.len() - 1 {
                writeln!(writer, "\"{}\",", inst.name)?;
            } else {
                writeln!(writer, "\"{}\"", inst.name)?;
            }
        }
        writeln!(writer, ">>]\n")?;

        // Insert ThreadArguments
        writeln!(writer, r"ThreadArguments == [t \in 1..NumThreads |-> <<")?;
        for (idx, inst) in self.instructions.iter().enumerate() {
            if idx != self.instructions.len() - 1 {
                writeln!(writer, "{}, ", inst.arguments)?;
            } else {
                writeln!(writer, "{}", inst.arguments)?;
            }
        }
        writeln!(writer, ">>]\n")?;
        Ok(())
    }

    pub fn write_to_file(&self, path: &Utf8Path) -> Result<()> {
        // Open the file for reading
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let temp_path = path.with_extension("tmp");
        let temp_file = File::create(&temp_path)?;
        let mut writer = BufWriter::new(temp_file);

        let mut found_layout = false;
        let mut found_globals = false;
        let mut found_program = false;

        for line in reader.lines() {
            let line = line?;
            if line.trim() == LAYOUT_CONFIG_HINT {
                found_layout = true;
                self.write_layout(&mut writer)?;
            } else if line.trim() == GLOBAL_VARIABLES_HINT {
                found_globals = true;
                self.write_global_variables(&mut writer)?;
            } else if line.trim() == PROGRAM_HINT {
                found_program = true;
                self.write_program(&mut writer)?;
            } else {
                writeln!(writer, "{}", line)?;
            }
        }
        drop(writer);

        if !found_layout {
            return Err(eyre!("Layout configuration hint not found in the file."));
        }
        if !found_globals {
            return Err(eyre!("Global variables hint not found in the file."));
        }
        if !found_program {
            return Err(eyre!("Program hint not found in the file."));
        }

        // Replace the original file with the new file
        fs::rename(temp_path, path)?;
        Ok(())
    }
}
