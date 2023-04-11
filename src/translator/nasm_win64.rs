use halfbrown::HashMap;

use super::label::Label;
use crate::interpreter::{
	cypress::CypressVariable,
	firefly::{
		BinaryOperator, FireflyOperand, FireflyOperation, FireflyPrimitive, FireflyProcedure, FireflyProgram,
		FireflyProjection, FireflyProjector, FireflyStatement, FireflyTerm, FireflyTerminator, FireflyType,
	},
};

pub enum NASMDefinition {
	ASCII(String),
}

#[derive(Debug, Clone, Copy)]
pub enum NASMRegister64 {
	RAX, // Return Value
	RCX, // Argument/Pointer to Argument
	RDX, // Pointer to Environment
	R8,  // Pointer to Return Value
	R9,
	R10, // Temporary,
	R11, // Temporary
	RSP,
	RBP,
}

impl ToString for NASMRegister64 {
	fn to_string(&self) -> String {
		use NASMRegister64::*;
		match self {
			RAX => "rax",
			RCX => "rcx",
			RDX => "rdx",
			R8 => "r8",
			R9 => "r9",
			R10 => "r10",
			R11 => "r11",
			RSP => "rsp",
			RBP => "rbp",
		}
		.to_owned()
	}
}

#[derive(Debug)]
pub enum NASMInstruction {
	Jmp(String),
	PushReg(NASMRegister64),
	PushLabel(String),
	Pop(NASMRegister64),
	AddFromU32(NASMRegister64, u32),
	AddFromRBPMinus(NASMRegister64, u32),
	AddFromReg(NASMRegister64, NASMRegister64),
	SubFromU32(NASMRegister64, u32),
	MovFromReg(NASMRegister64, NASMRegister64),
	MovFromLabel(NASMRegister64, String),
	MovFromU64(NASMRegister64, u64),
	MovFromI64(NASMRegister64, i64),
	MovFromRBPMinus(NASMRegister64, u32),
	MovIntoRBPMinus(u32, NASMRegister64),
	CallLabel(String),
	Leave,
	Ret,
}

impl NASMInstruction {
	pub fn as_line(&self) -> String {
		use NASMInstruction::*;
		match self {
			Jmp(label) => format!("jmp {label}"),
			PushReg(reg) => format!("push {}", reg.to_string()),
			PushLabel(label) => format!("push {label}"),
			Pop(reg) => format!("pop {}", reg.to_string()),
			AddFromU32(reg, imm) => format!("add {}, {imm}", reg.to_string()),
			AddFromRBPMinus(reg, offset) => format!("add {}, [rbp - {offset}]", reg.to_string()),
			AddFromReg(reg_dst, reg_src) => format!("add {}, {}", reg_dst.to_string(), reg_src.to_string()),
			SubFromU32(reg, imm) => format!("sub {}, {imm}", reg.to_string()),
			MovFromReg(reg_dst, reg_src) => format!("mov {}, {}", reg_dst.to_string(), reg_src.to_string()),
			MovFromLabel(reg, label) => format!("mov {}, {label}", reg.to_string()),
			MovFromU64(reg, imm) => format!("mov {}, {imm}", reg.to_string()),
			MovFromI64(reg, imm) => format!("mov {}, {imm}", reg.to_string()),
			MovFromRBPMinus(reg, offset) => format!("mov {}, [rbp - {offset}]", reg.to_string()),
			MovIntoRBPMinus(offset, reg) => format!("mov [rbp - {offset}], {}", reg.to_string()),
			CallLabel(label) => format!("call {label}"),
			Leave => format!("leave"),
			Ret => format!("ret"),
		}
	}
}

pub enum NASMLocation {}

#[derive(Debug)]
pub struct NASMBlock {
	local_label: String,
	instructions: Vec<NASMInstruction>,
}

#[derive(Default)]
pub struct StackFrame {
	label_to_offset_from_frame_pointer: HashMap<Label, (FireflyType, u32)>,
	continuation_to_parameter: HashMap<Label, Label>,
	current_frame_pointer_offset: u32,
}

impl StackFrame {
	pub fn new() -> Self {
		Self {
			label_to_offset_from_frame_pointer: HashMap::new(),
			continuation_to_parameter: HashMap::new(),
			current_frame_pointer_offset: 0,
		}
	}

	pub fn size(&self) -> u32 {
		self.label_to_offset_from_frame_pointer
			.values()
			.fold(0, |acc, (ty, _)| acc + size_of_ty(ty))
	}

	pub fn allocate(&mut self, label: Label, ty: FireflyType) -> u32 {
		self.current_frame_pointer_offset += size_of_ty(&ty) as u32;
		self.label_to_offset_from_frame_pointer
			.insert(label, (ty, self.current_frame_pointer_offset));
		self.current_frame_pointer_offset
	}

	pub fn allocate_phi(&mut self, continuation: Label, parameter: Label, ty: FireflyType) -> u32 {
		self.continuation_to_parameter.insert(continuation, parameter.clone());
		self.allocate(parameter, ty)
	}

	pub fn get(&self, label: &Label) -> Option<(FireflyType, u32)> {
		self.label_to_offset_from_frame_pointer.get(&label).cloned()
	}

	pub fn get_field(&self, projection: &FireflyProjection) -> Option<u32> {
		match projection.root {
			CypressVariable::Local(local) => {
				let (ty, mut offset) = self.get(&local)?;

				// TODO: handle projections with awareness of types.
				for projector in &projection.projectors {
					match projector {
						FireflyProjector::Field(i) => offset += (8 * i) as u32,
						FireflyProjector::Free(i) => offset += (8 * i) as u32,
						FireflyProjector::Procedure => (),
						FireflyProjector::Snapshot => offset += 8,
					}
				}

				Some(offset)
			},
			_ => None, // TODO: This would need a different return type, and wouldn't be relative to the frame pointer.
		}
	}

	pub fn get_phi(&self, continuation: &Label) -> Option<u32> {
		self.label_to_offset_from_frame_pointer
			.get(&self.continuation_to_parameter.get(continuation).copied()?)
			.map(|x| x.1)
	}
}

pub fn emit_assembly(procedures: Vec<NASMProcedure>) -> String {
	let mut assembly = r#"global main
extern printf

section .data
result:
	db "Result: %ld", 10, 0

section .text
"#
	.to_owned();

	for procedure in procedures {
		assembly.push_str(&format!("{}:\n", procedure.label));
		for instruction in procedure.entry {
			assembly.push('\t');
			assembly.push_str(&instruction.as_line());
			assembly.push('\n');
		}

		for block in procedure.block_stack.into_iter().rev() {
			assembly.push_str(&format!("\t{}:\n", block.local_label));
			for instruction in block.instructions {
				assembly.push('\t');
				assembly.push_str(&instruction.as_line());
				assembly.push('\n');
			}
		}
	}

	assembly
}

#[derive(Debug)]
pub struct NASMProcedure {
	label: String,
	entry: Vec<NASMInstruction>,
	block_stack: Vec<NASMBlock>,
}

pub fn emit_program(program: FireflyProgram) -> Option<Vec<NASMProcedure>> {
	let FireflyProgram {
		procedures: ff_procedures,
		entry: ff_entry,
		mut symbol_generator,
	} = program;
	let mut procedures = Vec::new();
	let mut globals = HashMap::new();

	for (&label, ff_procedure) in &ff_procedures {
		procedures.push(emit_procedure(label, ff_procedure)?);
	}

	procedures.push(emit_main(&ff_procedures, ff_entry, &mut globals));

	Some(procedures)
}

pub fn emit_main(
	procedures: &HashMap<Label, FireflyProcedure>,
	entry: Label,
	globals: &mut HashMap<String, NASMDefinition>,
) -> NASMProcedure {
	use NASMDefinition::*;
	use NASMInstruction::*;
	use NASMRegister64::*;
	// FIXME: We assume the entry procedure returns a register-sized value.
	let result = "result".to_owned();

	globals.insert(result.clone(), ASCII("Result: %ld".to_owned()));

	NASMProcedure {
		label: "main".to_owned(),
		entry: Vec::from([
			PushReg(RBP),
			MovFromReg(RBP, RSP),
			SubFromU32(RSP, 0 + 32 + 8),
			CallLabel(emit_procedure_label(entry)),
			MovFromReg(RDX, RAX),
			MovFromU64(RAX, 0),
			MovFromLabel(RCX, result),
			CallLabel("printf".to_owned()),
			MovFromU64(RAX, 0),
			Leave,
			Ret,
		]),
		block_stack: Vec::new(),
	}
}

pub fn emit_procedure(label: Label, procedure: &FireflyProcedure) -> Option<NASMProcedure> {
	use NASMInstruction::*;
	use NASMRegister64::*;
	let mut block_stack = Vec::new();
	let mut stack_frame = StackFrame::default(); // Takes a label and gives an offset from the stack.
	let entry = emit_term(&mut block_stack, &mut stack_frame, &procedure.body)?;

	let stack_size = stack_frame.size();
	let stack_shadow = 32;
	let stack_padding = 16 - ((stack_size + 8) % 16) % 16;

	let prologue = Vec::from([
		PushReg(RBP),
		MovFromReg(RBP, RSP),
		SubFromU32(RSP, stack_size + stack_shadow + stack_padding),
	]);

	// This could enable potential tail recursion elimination
	// Alternatively, introduce a 'functional' while loop primitive and force users to use that instead.
	block_stack.push(NASMBlock {
		local_label: ".entry".to_owned(),
		instructions: entry,
	});

	Some(NASMProcedure {
		label: emit_procedure_label(label),
		entry: prologue,
		block_stack,
	})
}

pub fn emit_term(
	block_stack: &mut Vec<NASMBlock>,
	stack_frame: &mut StackFrame,
	term: &FireflyTerm,
) -> Option<Vec<NASMInstruction>> {
	use NASMInstruction::*;
	use NASMRegister64::*;
	let mut instructions = Vec::new();

	for statement in &term.statements {
		emit_statement(block_stack, statement, &mut instructions, stack_frame)
	}

	emit_terminator(&term.terminator, &mut instructions, stack_frame);

	Some(instructions)
}

pub fn emit_block_local_label(label: Label) -> String {
	["._", label.handle().to_string().as_str()].concat()
}

pub fn emit_statement(
	block_stack: &mut Vec<NASMBlock>,
	statement: &FireflyStatement,
	instructions: &mut Vec<NASMInstruction>,
	stack_frame: &mut StackFrame,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;
	match statement {
		FireflyStatement::Assign { binding, operation } => match operation {
			FireflyOperation::Id(ty, operand) => {
				let var = stack_frame.allocate(binding.clone(), ty.clone());
				match operand {
					FireflyOperand::Copy(projection) => {
						instructions.push(MovFromRBPMinus(
							RAX,
							stack_frame
								.get_field(projection)
								.expect("failed to get field from stack frame"),
						));
						instructions.push(MovIntoRBPMinus(var, RAX));
					},
					FireflyOperand::Constant(primitive) => match primitive {
						FireflyPrimitive::Unity => (),
						FireflyPrimitive::Polarity(pol) => {
							instructions.push(MovFromI64(RAX, *pol as i64));
							instructions.push(MovIntoRBPMinus(var, RAX));
						},
						FireflyPrimitive::Integer(int) => {
							instructions.push(MovFromI64(RAX, *int));
							instructions.push(MovIntoRBPMinus(var, RAX));
						},
						FireflyPrimitive::Procedure(label) => {
							instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())));
							instructions.push(MovIntoRBPMinus(var, RAX));
						},
					},
				}
			},
			FireflyOperation::Binary(BinaryOperator::Add, [left, right]) => {
				instructions.push(MovFromU64(RAX, 0));

				fn push_addition(instructions: &mut Vec<NASMInstruction>, operand: &FireflyOperand, stack_frame: &StackFrame) {
					match operand {
						FireflyOperand::Copy(projection) => {
							instructions.push(AddFromRBPMinus(
								RAX,
								stack_frame
									.get_field(projection)
									.expect("failed to get field from stack frame"),
							));
						},
						FireflyOperand::Constant(FireflyPrimitive::Integer(n)) => {
							instructions.push(MovFromI64(R10, *n));
							instructions.push(AddFromReg(RAX, R10));
						},
						_ => panic!("bad operand"),
					}
				}

				push_addition(instructions, left, stack_frame);
				push_addition(instructions, right, stack_frame);
			},
			FireflyOperation::Binary(BinaryOperator::EqualsQuery, [left, right]) => todo!(),
			FireflyOperation::Pair(fields) => todo!(),
			FireflyOperation::Closure(procedure, captures) => todo!(),
		},
		FireflyStatement::DeclareContinuation {
			label,
			parameter,
			domain,
			body,
		} => {
			stack_frame.allocate_phi(label.clone(), parameter.clone(), domain.clone());

			let instructions = emit_term(block_stack, stack_frame, body).unwrap();

			block_stack.push(NASMBlock {
				local_label: emit_block_local_label(label.clone()),
				instructions,
			});
		},
	}
}

pub fn emit_terminator(
	terminator: &FireflyTerminator,
	instructions: &mut Vec<NASMInstruction>,
	//location_by_variable: &HashMap<CypressVariable, NASMLocation>,
	//stack_variables: &mut HashMap<Label, u32>,
	stack_frame: &mut StackFrame,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;
	match terminator {
		FireflyTerminator::Branch {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => {
			//instructions.extend([
			//
			//])
			unimplemented!();
		},
		FireflyTerminator::Apply {
			procedure,
			snapshot,
			continuation_label,
			argument,
		} => {
			if let Some(continuation_label) = continuation_label {
				unimplemented!(); // FIXME: handle projections!!!!!!!!!
				  /*match &argument.root {
					  CypressVariable::Local(local) => {
						  let source = stack_frame.get(local).unwrap();
						  instructions.push(MovFromRBPMinus(RAX, source));
						  instructions.push(PushLabel(label_from_id(continuation_label.clone())));
						  instructions.push(Jump(label_from_id(continuation_label.clone())));
					  },
					  CypressVariable::Global(_) => unimplemented!(),
				  }*/
			}
		},
		FireflyTerminator::Jump {
			continuation_label,
			argument,
		} => {
			match argument {
				FireflyOperand::Copy(projection) => {
					// FIXME: Assumes size of 8-bytes, wouldn't work for tuples, unit, etc.
					instructions.push(MovFromRBPMinus(
						RAX,
						stack_frame.get_field(projection).expect("no such field"),
					));
				},
				FireflyOperand::Constant(primitive) => match primitive {
					FireflyPrimitive::Unity => (),
					FireflyPrimitive::Polarity(p) => {
						instructions.push(MovFromI64(RAX, *p as i64));
					},
					FireflyPrimitive::Integer(n) => {
						instructions.push(MovFromI64(RAX, *n));
					},
					FireflyPrimitive::Procedure(label) => {
						instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())))
					},
				},
			}

			if let Some(continuation_label) = continuation_label {
				let parameter = stack_frame.get_phi(continuation_label).expect("no such continuation");

				instructions.push(MovIntoRBPMinus(parameter, RAX));
				instructions.push(Jmp(emit_block_local_label(continuation_label.clone())));
			} else {
				instructions.push(Leave);
				instructions.push(Ret);
			}
		},
	}
}

// For now, every size should be a multiple of 8.
pub fn size_of_ty(ty: &FireflyType) -> u32 {
	match ty {
		FireflyType::Unity => 0,
		FireflyType::Polarity => 8,
		FireflyType::Integer => 8,
		FireflyType::Product(factors) => factors.iter().map(size_of_ty).fold(0, core::ops::Add::add),
		FireflyType::Procedure => 8,
		FireflyType::Snapshot => 8,
		FireflyType::Closure => size_of_ty(&FireflyType::Procedure) + size_of_ty(&FireflyType::Snapshot),
	}
}

pub fn emit_procedure_label(label: Label) -> String {
	["_", label.handle().to_string().as_str()].concat()
}

pub fn label_from_id(id: Label) -> String {
	id.handle().to_string()
}
