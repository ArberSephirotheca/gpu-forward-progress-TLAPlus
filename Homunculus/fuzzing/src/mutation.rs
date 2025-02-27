use compiler::codegen::common::{Instruction, InstructionName, Program};
use rand::{rng, seq::SliceRandom};

fn mutation(program: &mut Program) {
    program.instructions
}

fn available_label(program: &Program) -> Vec<u32> {
    let mut labels = Vec::new();
    for instruction in &program.instructions {
        if let InstructionName::Label = instruction.name {
            labels.push(instruction.arguments.arguments[0].value.parse().unwrap());
        }
    }
    labels
}

fn modify_condition(instruction: &mut Instruction)
fn switch_branch_label(instruction: &mut Instruction) {
    match &mut instruction.name {
        InstructionName::Branch => {

        }
        InstructionName::BranchConditional => {
            // Switch the branch label
            instruction.arguments.arguments.swap(1, 2);
        }
        InstructionName::Switch => {
            let mut rng = rng();
            // shuffle the targets
            if let Some(labels) = &mut instruction.vec_arguments{
                labels.shuffle(&mut rng);
            }
        }
        _ => {},
    }
}