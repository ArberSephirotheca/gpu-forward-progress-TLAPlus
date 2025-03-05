use compiler::codegen::common::{Program, Scheduler};
use compiler::codegen::context::CodegenCx;
use compiler::compiler::parse::parser::{parse, parse_save_tokens};
use std::fs::File;
use std::io::Read;
use std::io::{self};
use std::{env, path};

static DEFAULT_PROGRAM_FILE: &str = "./forward-progress/validation/MCProgram.tla";
static DEFAULT_SCHEDULER: Scheduler = Scheduler::OBE;
static DEFAULT_WORKGROUP_SIZE: u32 = 1;
static DEFAULT_SUBGROUP_SIZE: u32 = 1;
static DEFAULT_NUM_WORKGROUPS: u32 = 2;

fn read_spir_v_file(file_path: &str) -> io::Result<String> {
    let mut file = File::open(file_path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}

// fn fuzz(
//     spirv_code: &str,
//     sub_group_size: u32,
//     work_group_size: u32,
//     num_workgroup: u32,
//     scheduler: Scheduler,
// ) -> Program {
//     let (parse, tokens) = parse_save_tokens(spirv_code);
//     let syntax = parse.syntax();
//     let mut codegen_ctx = CodegenCx::new(sub_group_size, work_group_size, num_workgroup, scheduler);
//     codegen_ctx.generate_code_with_origin_line_number(syntax, &tokens);
// }
