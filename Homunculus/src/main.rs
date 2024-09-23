mod codegen;
mod compiler;
use camino::Utf8Path;
use codegen::common::Scheduler;
use codegen::context::CodegenCx;
use compiler::parse::parser::parse;
use eyre::{eyre, Context, Report, Result};
use std::env;
use std::fs::File;
use std::io::Read;
use std::io::{self};

static DEFAULT_PROGRAM_FILE: &str = "MCProgram.tla";

fn read_glsl_file(file_path: &str) -> io::Result<String> {
    let mut file = File::open(file_path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}

fn compile(
    glsl_code: &str,
    sub_group_size: u32,
    work_group_size: u32,
    num_workgroup: u32,
    scheduler: Scheduler,
) -> Result<()> {
    let syntax = parse(glsl_code).syntax();
    let mut codegen_ctx = CodegenCx::new(sub_group_size, work_group_size, num_workgroup, scheduler);
    let program = codegen_ctx.generate_code(syntax);
    let path = Utf8Path::new("./forward-progress/validation");
    let file = path.join(DEFAULT_PROGRAM_FILE);
    program.write_to_file(&file)
}

fn main() {
    // Get the command-line arguments
    let args: Vec<String> = env::args().collect();

    // Check if the user provided a filename
    if args.len() < 6 {
        eprintln!(
            "Usage: {} <glsl_file> <subgroup_size> <workgroup_size> <num_workgroups> <scheduler>",
            args[0]
        );
        return;
    }

    let filename = &args[1];
    let sub_group_size = &args[2]
        .parse::<u32>()
        .expect("SubGroup size must be an non-negative integer");
    let work_group_size = &args[3]
        .parse::<u32>()
        .expect("workGroup size must be an non-negative integer");
    let num_work_group = &args[4]
        .parse::<u32>()
        .expect("numWorkGroup size must be an non-negative integer");
    let scheduler: Scheduler = args[5]
        .parse::<Scheduler>()
        .expect("scheduler must be either HSA or OBE");

    // Read the GLSL file
    match read_glsl_file(filename) {
        Ok(glsl_code) => {
            compile(
                &glsl_code,
                *sub_group_size,
                *work_group_size,
                *num_work_group,
                scheduler,
            )
            .unwrap();
        }
        Err(e) => eprintln!("Failed to read GLSL file '{}': {}", filename, e),
    }
}

