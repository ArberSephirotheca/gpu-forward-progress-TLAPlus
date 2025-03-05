use compiler::codegen::common::{Instruction, InstructionBuiltInVariable, InstructionName, InstructionValue, Program};
use rand::{random_range, rng, seq::SliceRandom};

fn mutation(program: &mut Program) {
    for  (idx,ref instruction) in program.instructions.clone().into_iter().enumerate() {
        match instruction.name {
            InstructionName::Branch => {
                todo!()
            }
            InstructionName::BranchConditional => {
                todo!()
            }
            InstructionName::Switch => {
                todo!()
            }
            InstructionName::Equal
            | InstructionName::NotEqual
            | InstructionName::LessThan
            | InstructionName::LessThanEqual
            | InstructionName::GreaterThan
            | InstructionName::GreaterThanEqual => {
                fuzz_comparison_condition(instruction, program, idx);
            }
            _ => {}
        }
    }
}

fn available_labels(program: &Program) -> Vec<u32> {
    let mut labels = Vec::new();
    for instruction in &program.instructions {
        if let InstructionName::Label = instruction.name {
            labels.push(instruction.arguments.arguments[0].value.parse().unwrap());
        }
    }
    labels
}

fn fuzz_if_condition(instruction: &Instruction, program: &Program) {
    todo!()
}


fn fuzz_comparison_condition(instruction: &Instruction, program: &mut Program, idx: usize) {
    let mut rng = rng();
    let operand_1 = &instruction.arguments.arguments[0].value.clone();
    let operand_2 = &instruction.arguments.arguments[1].value.clone();
    if let InstructionValue::Int(_) = operand_1{
        if let InstructionValue::BuiltIn(built_in) = operand_2{
            match built_in{
                InstructionBuiltInVariable::GlobalInvocationId => {
                    let totoal_threads = (program.work_group_size * program.num_work_groups) as i32;
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(random_range(0..totoal_threads))
                }
                InstructionBuiltInVariable::LocalInvocationId => {
                    let local_id = random_range(0..program.work_group_size);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(local_id as i32);
                }
                InstructionBuiltInVariable::WorkgroupId => {
                    let work_group_id = random_range(0..program.num_work_groups);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(work_group_id as i32);
                }
                InstructionBuiltInVariable::SubgroupId => {
                    let num_subgroups = program.num_work_groups / program.subgroup_size;
                    let subgroup_id = random_range(0..num_subgroups);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(subgroup_id as i32);
                }
                InstructionBuiltInVariable::SubgroupLocalInvocationId => {
                    let subgroup_local_id = random_range(0..program.subgroup_size);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(subgroup_local_id as i32);
                }
                InstructionBuiltInVariable::NumWorkgroups => {
                    let num_work_groups = random_range(0..program.num_work_groups);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(num_work_groups as i32);
                }
                InstructionBuiltInVariable::NumSubgroups => {
                    let num_subgroups = random_range(0..program.num_work_groups / program.subgroup_size);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(num_subgroups as i32);
                }
                InstructionBuiltInVariable::WorkgroupSize => {
                    let workgroup_size = random_range(0..program.work_group_size);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(workgroup_size as i32);
                }
                InstructionBuiltInVariable::SubgroupSize => {
                    let subgroup_size = random_range(0..program.subgroup_size);
                    program.instructions[idx].arguments.arguments[0].value = InstructionValue::Int(subgroup_size as i32);

                }
            }
        }
    } else if let InstructionValue::Int(_) = operand_2{
        if let InstructionValue::BuiltIn(ref built_in) = operand_1{
            match built_in{
                InstructionBuiltInVariable::GlobalInvocationId => {
                    let totoal_threads = (program.work_group_size * program.num_work_groups) as i32;
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(random_range(0..totoal_threads))
                }
                InstructionBuiltInVariable::LocalInvocationId => {
                    let local_id = random_range(0..program.work_group_size);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(local_id as i32);
                }
                InstructionBuiltInVariable::WorkgroupId => {
                    let work_group_id = random_range(0..program.num_work_groups);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(work_group_id as i32);
                }
                InstructionBuiltInVariable::SubgroupId => {
                    let num_subgroups = program.num_work_groups / program.subgroup_size;
                    let subgroup_id = random_range(0..num_subgroups);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(subgroup_id as i32);   
                }
                InstructionBuiltInVariable::SubgroupLocalInvocationId => {
                    let subgroup_local_id = random_range(0..program.subgroup_size);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(subgroup_local_id as i32);
                }
                InstructionBuiltInVariable::NumWorkgroups => {
                    let num_work_groups = random_range(0..program.num_work_groups);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(num_work_groups as i32);
                }
                InstructionBuiltInVariable::NumSubgroups => {
                    let num_subgroups = random_range(0..program.num_work_groups / program.subgroup_size);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(num_subgroups as i32);
                }
                InstructionBuiltInVariable::WorkgroupSize => {
                    let workgroup_size = random_range(0..program.work_group_size);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(workgroup_size as i32);
                }
                InstructionBuiltInVariable::SubgroupSize => {
                    let subgroup_size = random_range(0..program.subgroup_size);
                    program.instructions[idx].arguments.arguments[1].value = InstructionValue::Int(subgroup_size as i32);
                }
            }
        }
    }
 
    
}

fn fuzz_branch_condition(instruction: &mut Instruction){
    todo!()
}

fn fuzz_loop_condition(instruction: &mut Instruction){
    todo!()
}

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
            // shuffle the labels
            if let Some(labels) = &mut instruction.vec_arguments{
                labels.shuffle(&mut rng);
            }
        }
        _ => {},
    }
}