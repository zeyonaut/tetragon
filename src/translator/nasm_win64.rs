use std::collections::{HashMap, HashSet};

use super::label::{Label, LabelGenerator};
use crate::{
	interpreter::flow::{
		ff_closure_type, BinaryOperator, FlowOperand, FlowOperation, FlowPrimitive, FlowProcedure, FlowProgram, FlowProjection,
		FlowProjector, FlowStatement, FlowTerm, FlowTerminator, FlowType, FlowVariable,
	},
	utility::slice::Slice,
};

pub enum NASMDefinition {
	ASCII(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NASMRegister8 {
	AL,
}

impl core::fmt::Display for NASMRegister8 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use NASMRegister8::*;
		f.write_str(match self {
			AL => "al",
		})
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NASMRegister64 {
	RAX, // Return Value
	RCX, // Argument/Pointer to Argument
	RDX, // Pointer to Environment
	R8,  // Pointer to Return Value
	R9,
	R10, // Temporary Register
	R11, // Cloning/Dropping Temporary Register
	RSP,
	RBP,
	RSI,
	RDI,
}

impl core::fmt::Display for NASMRegister64 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use NASMRegister64::*;
		f.write_str(match self {
			RAX => "rax",
			RCX => "rcx",
			RDX => "rdx",
			R8 => "r8",
			R9 => "r9",
			R10 => "r10",
			R11 => "r11",
			RSP => "rsp",
			RBP => "rbp",
			RSI => "rsi",
			RDI => "rdi",
		})
	}
}

#[derive(Debug)]
pub enum NASMInstruction {
	Jmp(String),
	JNE(String),
	JE(String),
	PushReg(NASMRegister64),
	PushLabel(String),
	Pop(NASMRegister64),
	AddFromU32(NASMRegister64, u32),
	AddFromI32(NASMRegister64, i32),
	AddFromAddress(NASMRegister64, (NASMRegister64, i32)),
	AddFromReg(NASMRegister64, NASMRegister64),
	AddSXIntoAddressFromI32((NASMRegister64, i32), i32),
	SubSXIntoAddressFromI32((NASMRegister64, i32), i32),
	SubFromU32(NASMRegister64, u32),
	MovFromReg(NASMRegister64, NASMRegister64),
	MovFromLabel(NASMRegister64, String),
	MovFromU64(NASMRegister64, u64),
	MovFromI64(NASMRegister64, i64),
	LEA(NASMRegister64, (NASMRegister64, i32)),
	MovFromAddress(NASMRegister64, (NASMRegister64, i32)),
	MovIntoAddressFromReg((NASMRegister64, i32), NASMRegister64),
	MovIntoAddressFromU64((NASMRegister64, i32), u64),
	MovIntoAddressFromI64((NASMRegister64, i32), i64),
	MovIntoAddressFromLabel((NASMRegister64, i32), String),
	MovZXR64FromR8(NASMRegister64, NASMRegister8),
	SetE(NASMRegister8),
	CmpALWithU8(u8),
	CmpWithU8(NASMRegister64, u8),
	CmpReg(NASMRegister64, NASMRegister64),
	RepMovsb,
	RepMovsq,
	CallReg(NASMRegister64),
	CallLabel(String),
	LocalLabel(String),
	Leave,
	Ret,
}

impl NASMInstruction {
	pub fn as_line(&self) -> String {
		use NASMInstruction::*;
		match self {
			Jmp(label) => format!("jmp {label}"),
			JNE(label) => format!("jne {label}"),
			JE(label) => format!("je {label}"),
			PushReg(reg) => format!("push {reg}"),
			PushLabel(label) => format!("push {label}"),
			Pop(reg) => format!("pop {reg}"),
			AddFromU32(reg, imm) => format!("add {reg}, {imm}"),
			AddFromI32(reg, imm) => format!("add {reg}, {imm}"),
			AddFromAddress(dst, (src, offset)) => format!("add {dst}, [{src} + {offset}]"),
			AddFromReg(reg_dst, reg_src) => format!("add {reg_dst}, {reg_src}"),
			AddSXIntoAddressFromI32((dst, offset), imm) => format!("add qword [{dst} + {offset}], {imm}"),
			SubSXIntoAddressFromI32((dst, offset), imm) => format!("sub qword [{dst} + {offset}], {imm}"),
			SubFromU32(reg, imm) => format!("sub {reg}, {imm}"),
			MovFromReg(reg_dst, reg_src) => format!("mov {reg_dst}, {reg_src}"),
			MovFromLabel(reg, label) => format!("mov {reg}, {label}"),
			MovFromU64(reg, imm) => format!("mov {reg}, {imm}"),
			MovFromI64(reg, imm) => format!("mov {reg}, {imm}"),
			LEA(dst, (src, offset)) => format!("lea {dst}, [{src} + {offset}]"),
			MovFromAddress(dst, (src, offset)) => format!("mov {dst}, [{src} + {offset}]"),
			MovIntoAddressFromReg((dst, offset), src) => format!("mov [{dst} + {offset}], {src}"),
			MovIntoAddressFromU64((dst, offset), imm) => format!("mov qword [{dst} + {offset}], {imm}"),
			MovIntoAddressFromI64((dst, offset), imm) => format!("mov qword [{dst} + {offset}], {imm}"),
			MovIntoAddressFromLabel((dst, offset), label) => format!("mov qword [{dst} + {offset}], {label}"),
			RepMovsb => format!("rep movsb"),
			RepMovsq => format!("rep movsq"),
			CallReg(reg) => format!("call {reg}"),
			CallLabel(label) => format!("call {label}"),
			Leave => format!("leave"),
			Ret => format!("ret"),
			MovZXR64FromR8(dst, src) => format!("movzx {dst}, {src}"),
			SetE(dst) => format!("sete {dst}"),
			CmpALWithU8(imm) => format!("cmp al, {imm}"),
			CmpWithU8(reg, imm) => format!("cmp {reg}, {imm}"),
			CmpReg(left, right) => format!("cmp {left}, {right}"),
			LocalLabel(string) => format!("{string}:"),
		}
	}
}

pub enum NASMLocation {}

#[derive(Debug)]
pub struct NASMBlock {
	local_label: String,
	instructions: Vec<NASMInstruction>,
}

#[derive(Default, Debug)]
pub struct StackFrame {
	label_to_offset_from_frame_pointer: HashMap<Label, (FlowType, i32)>,
	continuation_to_parameter: HashMap<Label, Label>,
	current_frame_pointer_offset: i32,
	//min_offset: i32,
	// Used for checking what needs to be dropped at any given terminator (for reference counting).
	current_visibles: HashSet<Label>,
	continuation_to_visibles: HashMap<Label, HashSet<Label>>,
}

impl StackFrame {
	pub fn new() -> Self {
		Self {
			label_to_offset_from_frame_pointer: HashMap::new(),
			continuation_to_parameter: HashMap::new(),
			current_frame_pointer_offset: 0,
			current_visibles: HashSet::new(),
			continuation_to_visibles: HashMap::new(),
		}
	}

	pub fn size(&self) -> u32 {
		self.label_to_offset_from_frame_pointer
			.values()
			.fold(0, |acc, (ty, _)| acc + size_of_ty(ty))
	}

	pub fn allocate(&mut self, label: Label, ty: FlowType, is_owning: bool) -> i32 {
		if is_owning {
			self.current_visibles.insert(label.clone());
		}

		self.current_frame_pointer_offset -= size_of_ty(&ty) as i32;
		self.label_to_offset_from_frame_pointer
			.insert(label, (ty, self.current_frame_pointer_offset));
		self.current_frame_pointer_offset
	}

	// Returns the labels visible before the phi node was allocated.
	pub fn allocate_phi(&mut self, continuation: Label, parameter: Label, ty: FlowType) -> HashSet<Label> {
		let current_visibles = self.current_visibles.clone();
		self.continuation_to_visibles.insert(continuation, current_visibles.clone());
		self.continuation_to_parameter.insert(continuation, parameter.clone());
		self.allocate(parameter.clone(), ty, true);
		current_visibles
	}

	pub fn get(&self, label: &Label) -> Option<(FlowType, i32)> {
		self.label_to_offset_from_frame_pointer.get(&label).cloned()
	}

	fn emit_drop(
		&self,
		ty: FlowType,
		projection: &FlowProjection,
		instructions: &mut Vec<NASMInstruction>,
		symbol_generator: &mut LabelGenerator,
	) {
		use NASMInstruction::*;
		use NASMRegister64::*;
		match ty {
			FlowType::Product(factors) => {
				for (i, factor) in factors.into_vec().into_iter().enumerate() {
					self.emit_drop(
						factor,
						&projection.clone().project(FlowProjector::Field(i)),
						instructions,
						symbol_generator,
					)
				}
			},
			FlowType::Snapshot(Some(requisites)) => {
				if requisites.len() > 0 {
					self.emit_load::<true>(RCX, projection, instructions);
					instructions.push(CallLabel("drop_rc".to_owned()));
				}
			},
			_ => (),
		}
	}

	pub fn emit_drops(
		&self,
		continuation: Option<Label>,
		instructions: &mut Vec<NASMInstruction>,
		symbol_generator: &mut LabelGenerator,
	) {
		let mut droppables = self.current_visibles.clone();
		if let Some(undroppables) =
			continuation.map(|continuation| self.continuation_to_visibles.get(&continuation).unwrap().clone())
		{
			for undroppable in undroppables {
				droppables.remove(&undroppable);
			}
		}

		for droppable in droppables {
			let (ty, _) = self.get(&droppable).unwrap();
			self.emit_drop(
				ty,
				&FlowProjection::new(FlowVariable::Local(droppable)),
				instructions,
				symbol_generator,
			);
		}
	}

	fn emit_clone(
		&self,
		symbol_generator: &mut LabelGenerator,
		ty: FlowType,
		projection: &FlowProjection,
		instructions: &mut Vec<NASMInstruction>,
	) {
		use NASMInstruction::*;
		use NASMRegister64::*;
		match ty {
			FlowType::Product(factors) => {
				for (i, factor) in factors.into_vec().into_iter().enumerate() {
					self.emit_clone(
						symbol_generator,
						factor,
						&projection.clone().project(FlowProjector::Field(i)),
						instructions,
					)
				}
			},
			FlowType::Snapshot(_) => {
				// We increment the reference counter.
				let [skip_clone] = symbol_generator.fresh();

				self.emit_load::<true>(R11, projection, instructions);
				instructions.extend([
					CmpWithU8(R11, 0),
					JE(emit_block_local_label(skip_clone)),
					AddSXIntoAddressFromI32((R11, 0), 1),
					LocalLabel(emit_block_local_label(skip_clone)),
				]);
			},
			_ => (),
		}
	}

	pub fn emit_clones(
		&self,
		symbol_generator: &mut LabelGenerator,
		operand: &FlowOperand,
		instructions: &mut Vec<NASMInstruction>,
	) {
		match operand {
			FlowOperand::Copy(projection) => {
				if let FlowVariable::Local(local) = &projection.root {
					let (mut ty, _) = self.get(local).unwrap();

					for projector in &projection.projectors {
						match projector {
							FlowProjector::Parameter => continue,
							FlowProjector::Field(n) => {
								if let FlowType::Product(factors) = ty {
									ty = factors.get(*n).unwrap().clone();
								} else {
									panic!();
								}
							},
							FlowProjector::Free(n) => {
								if let FlowType::Snapshot(Some(requisites)) = ty {
									ty = requisites.get(*n).unwrap().clone();
								} else {
									panic!();
								}
							},
							FlowProjector::Dereference => unimplemented!(),
						}
					}

					self.emit_clone(symbol_generator, ty, projection, instructions);
				} else {
					unimplemented!();
				}
			},
			FlowOperand::Constant(_) => (),
		}
	}

	pub fn emit_load<const IS_BY_VALUE: bool>(
		&self,
		destination: NASMRegister64,
		projection: &FlowProjection,
		instructions: &mut Vec<NASMInstruction>,
	) {
		use NASMInstruction::*;
		use NASMRegister64::*;
		match projection.root {
			FlowVariable::Local(local) => {
				let (mut ty, mut offset) = self.get(&local).unwrap();
				let mut source = RBP;

				for projector in &projection.projectors {
					match projector {
						FlowProjector::Parameter => {
							let size = size_of_ty(&ty);
							if size <= 8 {
								()
							} else {
								instructions.push(MovFromAddress(destination, (source, offset)));
								source = destination;
								offset = 0;
							}
						},
						FlowProjector::Field(i) => {
							if let FlowType::Product(factors) = ty {
								ty = factors.get(*i).unwrap().clone();
								offset += factors.iter().take(*i).fold(0, |acc, ty| acc + size_of_ty(ty) as i32);
							} else {
								panic!("failed to get field from stack frame");
							}
						},
						FlowProjector::Free(i) => {
							if let FlowType::Snapshot(Some(factors)) = ty {
								instructions.push(MovFromAddress(destination, (source, offset)));
								source = destination;
								offset = 0;
								// We leave space for the reference count.
								offset += 8;
								// We leave space for the destructor.
								offset += 8;

								ty = factors.get(*i).unwrap().clone();
								offset += factors.iter().take(*i).fold(0, |acc, ty| acc + size_of_ty(ty) as i32);
							} else {
								panic!("failed to get field from stack frame");
							}
						},
						FlowProjector::Dereference => unimplemented!(),
					}
				}

				if IS_BY_VALUE {
					instructions.push(MovFromAddress(destination, (source, offset)));
				} else {
					instructions.push(LEA(destination, (source, offset)));
				}
			},
			FlowVariable::Global(_) => unimplemented!(),
		}
	}

	pub fn get_phi(&self, continuation: &Label) -> Option<(FlowType, i32)> {
		self.label_to_offset_from_frame_pointer
			.get(&self.continuation_to_parameter.get(continuation).copied()?)
			.cloned()
	}
}

pub fn emit_assembly(globals: HashMap<String, NASMDefinition>, procedures: Vec<NASMProcedure>) -> String {
	let mut assembly = r#"global main
extern free, malloc, printf

section .data
"#
	.to_owned();
	for (name, definition) in globals {
		assembly.push_str(&name);
		assembly.push_str(":\n\t");
		match definition {
			NASMDefinition::ASCII(string) => {
				assembly.push_str(format!("db `{}`, 0", string.escape_default().to_string()).as_ref())
			},
		}
	}

	assembly.push_str(
		r#"
section .text
"#,
	);

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

pub fn emit_program(program: FlowProgram) -> Option<String> {
	let FlowProgram {
		procedures: ff_procedures,
		entry: ff_entry,
		mut symbol_generator,
	} = program;
	let mut procedures = Vec::new();
	let mut globals = HashMap::new();

	let mut destructors = HashMap::new();

	procedures.push(emit_drop_snapshot());

	for (_, ff_procedure) in &ff_procedures {
		if let Some((_, requisites)) = &ff_procedure.capture {
			emit_destructor(&mut symbol_generator, &mut procedures, &mut destructors, requisites.clone());
		}
	}

	for (&label, ff_procedure) in &ff_procedures {
		procedures.push(emit_procedure(&mut symbol_generator, &destructors, label, ff_procedure)?);
	}

	let codomain = ff_procedures.get(&ff_entry)?.codomain.clone();

	procedures.push(emit_main(ff_entry, codomain, &mut globals));

	Some(emit_assembly(globals, procedures))
}

pub fn emit_main(entry: Label, codomain: FlowType, globals: &mut HashMap<String, NASMDefinition>) -> NASMProcedure {
	use NASMDefinition::*;
	use NASMInstruction::*;
	use NASMRegister64::*;

	let codomain_size = size_of_ty(&codomain);

	let result = "result".to_owned();
	let (format_string, format_offsets) = generate_format(codomain);
	let result_string = format!("Result: {format_string}\n");
	globals.insert(result.clone(), ASCII(result_string));

	// We fit three arguments onto registers RCX, R8, and R9.
	let stack_size = codomain_size + {
		let len = format_offsets.len();
		(if len > 3 { (len - 3) * 8 } else { 0 }) as u32
	};
	let stack_shadow = 32;
	let stack_padding = (16 - ((stack_size + 8) % 16)) % 16;

	let return_offset = -(codomain_size as i32);

	let mut instructions = vec![
		PushReg(RBP),
		MovFromReg(RBP, RSP),
		SubFromU32(RSP, stack_size + stack_shadow + stack_padding),
	];

	if codomain_size > 8 {
		instructions.extend([LEA(R8, (RBP, return_offset)), CallLabel(emit_procedure_label(entry))]);
	} else if codomain_size > 0 {
		instructions.extend([
			CallLabel(emit_procedure_label(entry)),
			MovIntoAddressFromReg((RBP, return_offset), RAX),
		]);
	} else {
		instructions.push(CallLabel(emit_procedure_label(entry)));
	}

	let mut offsets_iter = format_offsets.into_iter();

	if let Some(rdx_offset) = offsets_iter.next() {
		instructions.push(MovFromAddress(RDX, (RBP, return_offset + rdx_offset as i32)));
	}

	if let Some(r8_offset) = offsets_iter.next() {
		instructions.push(MovFromAddress(R8, (RBP, return_offset + r8_offset as i32)));
	}

	if let Some(r9_offset) = offsets_iter.next() {
		instructions.push(MovFromAddress(R9, (RBP, return_offset + r9_offset as i32)));
	}

	for (i, format_offset) in offsets_iter.enumerate() {
		instructions.push(MovFromAddress(RAX, (RBP, return_offset + format_offset as i32)));
		instructions.push(MovIntoAddressFromReg((RSP, (i * 8) as i32 + 32), RAX));
	}

	instructions.extend([
		MovFromU64(RAX, 0),
		MovFromLabel(RCX, result),
		CallLabel("printf".to_owned()),
		MovFromU64(RAX, 0),
		Leave,
		Ret,
	]);

	NASMProcedure {
		label: "main".to_owned(),
		entry: instructions,
		block_stack: Vec::new(),
	}
}

pub fn generate_format(ty: FlowType) -> (String, Vec<u32>) {
	match ty {
		FlowType::Unity => ("*".to_owned(), vec![]),
		FlowType::Polarity => ("%I64d".to_owned(), vec![0]),
		FlowType::Integer => ("%I64d".to_owned(), vec![0]),
		FlowType::Product(factors) => {
			let factors = factors.into_vec();
			let mut string = "(".to_owned();
			let mut offsets = vec![];
			let mut is_leftmost = true;
			let mut current_offset = 0;
			for factor in factors {
				let size = size_of_ty(&factor);
				let (factor_string, factor_offsets) = generate_format(factor);
				let mut factor_offsets = factor_offsets.into_iter().map(|x| x + current_offset).collect::<Vec<_>>();
				offsets.append(&mut factor_offsets);
				if !is_leftmost {
					string.push_str(", ");
					string.push_str(&factor_string);
				} else {
					string.push_str(&factor_string);
					is_leftmost = false;
				}
				current_offset += size;
			}
			string.push(')');
			(string, offsets)
		},
		FlowType::Procedure => ("<proc 0x%I64x>".to_owned(), vec![0]),
		FlowType::Snapshot(_) => ("<snap>".to_owned(), vec![]),
	}
}

pub fn emit_drop_snapshot() -> NASMProcedure {
	use NASMInstruction::*;
	use NASMRegister64::*;

	let stack_size = 8;
	let stack_shadow = 32;
	let stack_padding = (16 - ((stack_size + 8) % 16)) % 16;

	NASMProcedure {
		label: "drop_rc".to_owned(),
		entry: vec![
			CmpWithU8(RAX, 0),
			JNE(".return".to_owned()),
			PushReg(RBP),
			MovFromReg(RBP, RSP),
			SubFromU32(RSP, stack_size + stack_shadow + stack_padding),
			MovIntoAddressFromReg((RBP, -8), RCX),
			SubSXIntoAddressFromI32((RCX, 0), 1),
			MovFromAddress(RAX, (RCX, 0)),
			CmpWithU8(RAX, 0),
			JNE(".skip".to_owned()),
			MovFromAddress(RAX, (RCX, 8)),
			CallReg(RAX),
			MovFromAddress(RCX, (RBP, -8)),
			CallLabel("free".to_owned()),
			LocalLabel(".skip".to_owned()),
			Leave,
			LocalLabel(".return".to_owned()),
			Ret,
		],
		block_stack: vec![],
	}
}

pub fn emit_destructor(
	symbol_generator: &mut LabelGenerator,
	procedures: &mut Vec<NASMProcedure>,
	destructors: &mut HashMap<Slice<FlowType>, String>,
	requisites: Slice<FlowType>,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;

	let stack_size = 8;
	let stack_shadow = 32;
	let stack_padding = (16 - ((stack_size + 8) % 16)) % 16;

	if !destructors.contains_key(&requisites) {
		let [destructor_label] = symbol_generator.fresh();
		let destroy_label = emit_destroy_label(destructor_label);
		destructors.insert(requisites.clone(), destroy_label.clone());
		let mut instructions = vec![
			PushReg(RBP),
			MovFromReg(RBP, RSP),
			SubFromU32(RSP, stack_size + stack_shadow + stack_padding),
			MovIntoAddressFromReg((RBP, -8), RCX),
		];

		let mut offset = 8 + 8;
		for ty in requisites.into_vec().into_iter() {
			let size = size_of_ty(&ty);

			emit_destructor_drop(symbol_generator, offset, ty, &mut instructions);

			offset += size;
		}

		instructions.extend([Leave, Ret]);

		procedures.push(NASMProcedure {
			label: destroy_label,
			entry: instructions,
			block_stack: Vec::new(),
		})
	}
}

fn emit_destructor_drop(
	symbol_generator: &mut LabelGenerator,
	mut offset: u32,
	ty: FlowType,
	instructions: &mut Vec<NASMInstruction>,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;

	match ty {
		FlowType::Product(factors) => {
			for factor in factors.into_vec().into_iter() {
				let size = size_of_ty(&factor);
				emit_destructor_drop(symbol_generator, offset, factor, instructions);
				offset += size;
			}
		},
		FlowType::Snapshot(_) => instructions.extend([
			MovFromAddress(RCX, (RBP, -8)),
			AddFromU32(RCX, offset),
			CallLabel("drop_rc".to_owned()),
		]),
		_ => (),
	}
}

pub fn emit_procedure(
	symbol_generator: &mut LabelGenerator,
	destructors: &HashMap<Slice<FlowType>, String>,
	label: Label,
	procedure: &FlowProcedure,
) -> Option<NASMProcedure> {
	use NASMInstruction::*;
	use NASMRegister64::*;
	let mut block_stack = Vec::new();
	let mut stack_frame = StackFrame::default(); // Takes a label and gives an offset from the stack.

	let parameter_offset = if let Some(parameter) = procedure.parameter {
		Some(stack_frame.allocate(parameter, procedure.domain.clone(), true))
	} else {
		None
	};

	// NOTE: The only procedure without a capture is the entry procedure.
	// A procedure must have a capture in order to be applied as a closure.
	// If not, then the (even if empty) snapshot allocated for it will not be freed.
	// To allow 'clean' procedure calls, we need a separate application terminator that doesn't allocate a snapshot
	// at all (and emit them as appropriate in the hoisting phase).
	let capture_parameter_offset = if let Some((capture_parameter, capture_requisites)) = &procedure.capture {
		if capture_requisites.len() == 0 {
			None
		} else {
			Some(stack_frame.allocate(
				capture_parameter.clone(),
				FlowType::Snapshot(Some(capture_requisites.clone())),
				false,
			))
		}
	} else {
		None
	};

	let codomain_size = size_of_ty(&procedure.codomain);
	let [mailbox] = symbol_generator.fresh();
	let mailbox_offset = if codomain_size > 8 {
		Some(stack_frame.allocate(mailbox.clone(), FlowType::Integer, true)) // FIXME: This is not technically an integer, but a raw pointer.
	} else {
		None
	};

	let entry = emit_term(
		&destructors,
		&mut block_stack,
		&mut stack_frame,
		mailbox_offset,
		&procedure.body,
		symbol_generator,
	)?;

	let stack_size = stack_frame.size();
	let stack_shadow = 32;
	let stack_padding = (16 - ((stack_size + 8) % 16)) % 16;

	// FIXME: We're actually obligated to preserve RSI and RDI here.
	// We could do this at the use sites of RSI and RDI, though.
	// Alternatively, we can store a list of registers we've used and append to the prologue/epilogue as necessary.
	let mut prologue = Vec::from([
		PushReg(RBP),
		MovFromReg(RBP, RSP),
		SubFromU32(RSP, stack_size + stack_shadow + stack_padding),
	]);

	let domain_size = size_of_ty(&procedure.domain);

	if let Some(parameter_offset) = parameter_offset {
		if domain_size == 0 {
			()
		} else {
			prologue.push(MovIntoAddressFromReg((RBP, parameter_offset), RCX));
		}
	}

	if let Some(capture_parameter_offset) = capture_parameter_offset {
		prologue.push(MovIntoAddressFromReg((RBP, capture_parameter_offset), RDX));
	}

	if let Some(mailbox_offset) = mailbox_offset {
		prologue.push(MovIntoAddressFromReg((RBP, mailbox_offset), R8));
	}

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
	destructors: &HashMap<Slice<FlowType>, String>,
	block_stack: &mut Vec<NASMBlock>,
	stack_frame: &mut StackFrame,
	mailbox_offset: Option<i32>,
	term: &FlowTerm,
	symbol_generator: &mut LabelGenerator,
) -> Option<Vec<NASMInstruction>> {
	let mut instructions = Vec::new();

	for statement in &term.statements {
		emit_statement(
			destructors,
			block_stack,
			mailbox_offset,
			statement,
			&mut instructions,
			stack_frame,
			symbol_generator,
		)
	}

	emit_terminator(
		mailbox_offset,
		&term.terminator,
		&mut instructions,
		stack_frame,
		symbol_generator,
	);

	Some(instructions)
}

pub fn emit_block_local_label(label: Label) -> String {
	["._", label.handle().to_string().as_str()].concat()
}

pub fn emit_destroy_label(label: Label) -> String {
	["_destroy_", label.handle().to_string().as_str()].concat()
}

pub fn emit_statement(
	destructors: &HashMap<Slice<FlowType>, String>,
	block_stack: &mut Vec<NASMBlock>,
	mailbox_offset: Option<i32>,
	statement: &FlowStatement,
	instructions: &mut Vec<NASMInstruction>,
	stack_frame: &mut StackFrame,
	symbol_generator: &mut LabelGenerator,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;
	use NASMRegister8::*;
	match statement {
		FlowStatement::Copy { projections } => unimplemented!(),
		FlowStatement::Drop { assignees } => unimplemented!(),
		FlowStatement::Assign { binding, operation } => match operation {
			FlowOperation::Id(ty, operand) => {
				stack_frame.emit_clones(symbol_generator, operand, instructions);

				let var = stack_frame.allocate(binding.clone(), ty.clone(), true);
				match operand {
					FlowOperand::Copy(projection) => {
						let size = size_of_ty(&ty);
						if size == 0 {
							()
						} else if size == 8 {
							stack_frame.emit_load::<true>(RAX, projection, instructions);
							instructions.push(MovIntoAddressFromReg((RBP, var), RAX));
						} else {
							stack_frame.emit_load::<false>(RSI, projection, instructions);
							instructions.extend([LEA(RDI, (RBP, var)), MovFromU64(RCX, u64::from(size) / 8), RepMovsq]);
						}
					},
					FlowOperand::Constant(primitive) => match primitive {
						FlowPrimitive::Unity => (),
						FlowPrimitive::Polarity(pol) => {
							instructions.push(MovFromI64(RAX, *pol as i64));
							instructions.push(MovIntoAddressFromReg((RBP, var), RAX));
						},
						FlowPrimitive::Integer(int) => {
							instructions.push(MovFromI64(RAX, *int));
							instructions.push(MovIntoAddressFromReg((RBP, var), RAX));
						},
						FlowPrimitive::Procedure(label) => {
							instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())));
							instructions.push(MovIntoAddressFromReg((RBP, var), RAX));
						},
					},
				}
			},
			FlowOperation::Binary(BinaryOperator::Add, [left, right]) => {
				let var = stack_frame.allocate(binding.clone(), FlowType::Integer, true);
				instructions.push(MovFromU64(RAX, 0));

				fn push_addition(instructions: &mut Vec<NASMInstruction>, operand: &FlowOperand, stack_frame: &StackFrame) {
					match operand {
						FlowOperand::Copy(projection) => {
							// TODO: this is inefficient, as it doesn't need to use R10 unless some dereference takes place along the way. Even so, it can still leave off the last mov, adding directly using register + offset.
							// NOTE: One way to fix this might be to return a (destination, source, offset) pair. Then, we can use three separate functions for either emitting a by-value mov, a by-value add, or a by-reference mov.
							stack_frame.emit_load::<true>(R10, projection, instructions);
							instructions.push(AddFromReg(RAX, R10));
						},
						FlowOperand::Constant(FlowPrimitive::Integer(n)) => {
							instructions.push(MovFromI64(R10, *n));
							instructions.push(AddFromReg(RAX, R10));
						},
						_ => panic!("bad operand"),
					}
				}

				push_addition(instructions, left, stack_frame);
				push_addition(instructions, right, stack_frame);
				instructions.push(MovIntoAddressFromReg((RBP, var), RAX));
			},
			FlowOperation::Binary(BinaryOperator::EqualsQuery(ty), [left, right]) => {
				let var = stack_frame.allocate(binding.clone(), FlowType::Polarity, true);
				let size = size_of_ty(ty);
				if size == 0 {
					instructions.extend([MovFromI64(RAX, 1), MovIntoAddressFromReg((RBP, var), RAX)])
				} else if size == 8 {
					fn push_load(
						instructions: &mut Vec<NASMInstruction>,
						register: NASMRegister64,
						operand: &FlowOperand,
						stack_frame: &StackFrame,
					) {
						match operand {
							FlowOperand::Copy(projection) => {
								// NOTE: We currently do not support equality queries for oversized values, so this works fine for now.
								stack_frame.emit_load::<true>(register, projection, instructions);
							},
							FlowOperand::Constant(FlowPrimitive::Integer(n)) => {
								instructions.push(MovFromI64(register, *n));
							},
							FlowOperand::Constant(FlowPrimitive::Polarity(b)) => {
								instructions.push(MovFromI64(register, *b as i64));
							},
							FlowOperand::Constant(FlowPrimitive::Unity) => {
								panic!("Invalid operand encountered.");
							},
							FlowOperand::Constant(FlowPrimitive::Procedure(label)) => {
								instructions.push(MovFromLabel(register, emit_procedure_label(label.clone())));
							},
						}
					}

					push_load(instructions, R10, left, stack_frame);
					push_load(instructions, R11, right, stack_frame);
					instructions.extend([
						CmpReg(R10, R11),
						SetE(AL),
						MovZXR64FromR8(RAX, AL),
						MovIntoAddressFromReg((RBP, var), RAX),
					]);
				} else {
					// Equality queries for non-register-sized types?

					unimplemented!();
				}
			},
			FlowOperation::Pair(fields) => {
				for (_, operand) in fields.iter() {
					stack_frame.emit_clones(symbol_generator, operand, instructions);
				}

				let var = stack_frame.allocate(
					binding.clone(),
					FlowType::Product(fields.iter().map(|(ty, _)| ty.clone()).collect::<Vec<_>>().into_boxed_slice()),
					true,
				);

				let mut pigeonhole = 0i32;
				for (ty, operand) in fields.iter() {
					let size = size_of_ty(&ty);
					match operand {
						FlowOperand::Copy(projection) => {
							if size == 0 {
								()
							} else if size == 8 {
								stack_frame.emit_load::<true>(RAX, projection, instructions);
								instructions.push(MovIntoAddressFromReg((RBP, var + pigeonhole), RAX));
							} else {
								stack_frame.emit_load::<false>(RSI, projection, instructions);
								instructions.extend([
									LEA(RDI, (RBP, var + pigeonhole)),
									MovFromU64(RCX, u64::from(size) / 8),
									RepMovsq,
								]);
							}
						},
						FlowOperand::Constant(primitive) => match primitive {
							FlowPrimitive::Unity => (),
							FlowPrimitive::Polarity(pol) => {
								instructions.push(MovFromI64(RAX, *pol as i64));
								instructions.push(MovIntoAddressFromReg((RBP, var + pigeonhole), RAX));
							},
							FlowPrimitive::Integer(int) => {
								instructions.push(MovFromI64(RAX, *int));
								instructions.push(MovIntoAddressFromReg((RBP, var + pigeonhole), RAX));
							},
							FlowPrimitive::Procedure(label) => {
								instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())));
								instructions.push(MovIntoAddressFromReg((RBP, var + pigeonhole), RAX));
							},
						},
					}
					pigeonhole += size as i32;
				}
			},
			FlowOperation::Closure(procedure, captures) => {
				for (_, operand) in captures.iter() {
					stack_frame.emit_clones(symbol_generator, operand, instructions);
				}

				let var = stack_frame.allocate(binding.clone(), ff_closure_type(), true);

				let proc_var = var;

				match procedure {
					FlowOperand::Copy(projection) => {
						stack_frame.emit_load::<true>(RAX, projection, instructions);
						instructions.push(MovIntoAddressFromReg((RBP, proc_var), RAX));
					},
					FlowOperand::Constant(primitive) => match primitive {
						FlowPrimitive::Procedure(label) => {
							instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())));
							instructions.push(MovIntoAddressFromReg((RBP, proc_var), RAX));
						},
						_ => panic!("bad primitive"),
					},
				}

				let snapshot_var = var + 8;

				if captures.len() == 0 {
					// We give a NULL pointer, or zero; this is checked against in drop_rc.
					instructions.push(MovIntoAddressFromU64((RBP, snapshot_var), 0));
				} else {
					// The size to allocate is the size of the reference counter (8, a u64) + (8, the destructor procedure) + the size of a tuple consisting of the captures. Alignment is not an issue, as the maximum alignment should be 8.
					let size = 8
						+ 8 + size_of_ty(&FlowType::Product(
						captures
							.iter()
							.map(|(ty, _)| ty.clone())
							.collect::<Vec<_>>()
							.into_boxed_slice(),
					));
					instructions.push(MovFromU64(RCX, size as u64));
					instructions.push(CallLabel("malloc".to_owned()));
					instructions.push(MovIntoAddressFromU64((RAX, 0), 1));

					let destructor_offset = 8;

					let requisites = captures
						.into_iter()
						.map(|(ty, _)| ty.clone())
						.collect::<Vec<_>>()
						.into_boxed_slice();

					let destructor = destructors.get(&requisites).unwrap().clone();

					instructions.extend([
						MovFromLabel(R10, destructor),
						MovIntoAddressFromReg((RAX, destructor_offset), R10),
					]);

					let mut capture_offset = 8 + 8;
					for (capture_ty, capture) in captures.into_iter() {
						let capture_size = size_of_ty(capture_ty);
						match capture {
							FlowOperand::Copy(projection) => {
								if capture_size == 0 {
									()
								} else if capture_size == 8 {
									stack_frame.emit_load::<true>(R10, projection, instructions);
									instructions.push(MovIntoAddressFromReg((RAX, capture_offset), R10));
								} else {
									stack_frame.emit_load::<false>(RSI, projection, instructions);
									instructions.extend([
										LEA(RDI, (RAX, capture_offset)),
										MovFromU64(RCX, u64::from(size) / 8),
										RepMovsq,
									]);
								}
							},
							FlowOperand::Constant(FlowPrimitive::Integer(n)) => {
								instructions.push(MovIntoAddressFromI64((RAX, capture_offset), *n));
							},
							FlowOperand::Constant(FlowPrimitive::Polarity(b)) => {
								instructions.push(MovIntoAddressFromI64((RAX, capture_offset), *b as i64));
							},
							FlowOperand::Constant(FlowPrimitive::Unity) => {
								panic!("Invalid operand encountered.");
							},
							FlowOperand::Constant(FlowPrimitive::Procedure(label)) => {
								instructions.push(MovIntoAddressFromLabel(
									(RAX, capture_offset),
									emit_procedure_label(label.clone()),
								));
							},
						}
						capture_offset += capture_size as i32;
					}

					instructions.push(MovIntoAddressFromReg((RBP, snapshot_var), RAX));
				}
			},
		},
		FlowStatement::DeclareContinuation {
			label,
			parameter,
			domain,
			body,
		} => {
			let visibles = stack_frame.allocate_phi(label.clone(), parameter.clone(), domain.clone());

			let instructions =
				emit_term(destructors, block_stack, stack_frame, mailbox_offset, body, symbol_generator).unwrap();

			// We restore the visibles and continue on.
			stack_frame.current_visibles = visibles;

			block_stack.push(NASMBlock {
				local_label: emit_block_local_label(label.clone()),
				instructions,
			});
		},
	}
}

pub fn emit_terminator(
	mailbox_offset: Option<i32>,
	terminator: &FlowTerminator,
	instructions: &mut Vec<NASMInstruction>,
	stack_frame: &mut StackFrame,
	symbol_generator: &mut LabelGenerator,
) {
	use NASMInstruction::*;
	use NASMRegister64::*;
	match terminator {
		FlowTerminator::Branch {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => {
			match scrutinee {
				FlowOperand::Copy(projection) => {
					stack_frame.emit_load::<true>(RAX, projection, instructions);
				},
				FlowOperand::Constant(FlowPrimitive::Polarity(b)) => {
					instructions.push(MovFromI64(RAX, *b as i64));
				},
				FlowOperand::Constant(_) => {
					panic!("Invalid operand encountered.");
				},
			}
			instructions.extend([
				CmpALWithU8(0),
				JNE(emit_block_local_label(yes_continuation.clone())),
				Jmp(emit_block_local_label(no_continuation.clone())),
			]);
		},
		FlowTerminator::Apply {
			procedure,
			domain,
			codomain,
			snapshot,
			continuation_label,
			argument,
		} => {
			let codomain_size = size_of_ty(codomain);
			let continuation_and_parameter = if let Some(continuation_label) = continuation_label {
				Some((
					continuation_label,
					stack_frame.get_phi(continuation_label).expect("no such continuation"),
				))
			} else {
				None
			};

			let phi_buffer = if let Some((_, (_, _))) = continuation_and_parameter {
				let [phi_buffer_label] = symbol_generator.fresh();
				let phi_buffer_offset = stack_frame.allocate(phi_buffer_label, codomain.clone(), false);
				Some((FlowProjection::new(FlowVariable::Local(phi_buffer_label)), phi_buffer_offset))
			} else {
				None
			};

			stack_frame.emit_clones(symbol_generator, argument, instructions);
			stack_frame.emit_clones(symbol_generator, snapshot, instructions);

			match argument {
				FlowOperand::Copy(projection) => {
					let size = size_of_ty(domain);
					if size == 0 {
						()
					} else if size == 8 {
						stack_frame.emit_load::<true>(RCX, projection, instructions);
					} else {
						stack_frame.emit_load::<false>(RCX, projection, instructions);
					}
				},
				FlowOperand::Constant(primitive) => match primitive {
					FlowPrimitive::Unity => (),
					FlowPrimitive::Polarity(p) => instructions.push(MovFromI64(RCX, *p as i64)),
					FlowPrimitive::Integer(n) => instructions.push(MovFromI64(RCX, *n)),
					FlowPrimitive::Procedure(label) => {
						instructions.push(MovFromLabel(RCX, emit_procedure_label(label.clone())))
					},
				},
			}
			match snapshot {
				FlowOperand::Copy(projection) => {
					stack_frame.emit_load::<true>(RDX, projection, instructions);
				},
				FlowOperand::Constant(primitive) => match primitive {
					_ => panic!("bad snapshot primitive"),
				},
			}

			if codomain_size > 8 {
				if let Some((_, phi_buffer_offset)) = phi_buffer {
					instructions.push(LEA(R8, (RBP, phi_buffer_offset)));
				} else if let Some(mailbox_offset) = mailbox_offset {
					instructions.push(MovFromAddress(R8, (RBP, mailbox_offset)));
				} else {
					panic!("no mailbox to return an oversized value to")
				}
			}

			let procedure_label = match procedure {
				FlowOperand::Copy(projection) => {
					stack_frame.emit_load::<true>(RAX, projection, instructions);
					None
				},
				FlowOperand::Constant(primitive) => match primitive {
					FlowPrimitive::Procedure(label) => Some(label.clone()),
					_ => panic!("bad procedure primitive"),
				},
			};

			if let Some(procedure_label) = procedure_label {
				instructions.push(CallLabel(emit_procedure_label(procedure_label)));
			} else {
				instructions.push(CallReg(RAX));
			}

			if let Some((continuation, (_, continuation_parameter_offset))) = continuation_and_parameter {
				if let Some((phi_buffer_projection, phi_buffer_offset)) = phi_buffer {
					if codomain_size == 0 {
						()
					} else if codomain_size == 8 {
						instructions.push(MovIntoAddressFromReg((RBP, phi_buffer_offset), RAX));
					} else {
						()
					}

					stack_frame.emit_drops(continuation_label.clone(), instructions, symbol_generator);

					if codomain_size == 0 {
						()
					} else if codomain_size == 8 {
						instructions.push(MovFromAddress(RAX, (RBP, phi_buffer_offset)));
						instructions.push(MovIntoAddressFromReg((RBP, continuation_parameter_offset), RAX));
					} else {
						stack_frame.emit_load::<false>(RSI, &phi_buffer_projection, instructions);
						instructions.extend([
							LEA(RDI, (RBP, continuation_parameter_offset)),
							MovFromU64(RCX, u64::from(codomain_size) / 8),
							RepMovsq,
						]);
					}
				} else {
					panic!("attempted to return to continuation without a buffer for continuation argument");
				}

				instructions.push(Jmp(emit_block_local_label(continuation.clone())));
			} else {
				// TODO: If no drops (which call free) are emitted, we don't have to preserve RAX in RSI.
				// (But this can only happen in a procedure with no snapshots, as snapshots are always dropped)
				if codomain_size == 8 {
					instructions.push(MovFromReg(RSI, RAX));
				}

				stack_frame.emit_drops(continuation_label.clone(), instructions, symbol_generator);

				// TODO: If no drops are emitted, we don't have to preserve RAX in RSI.
				// (But this can only happen in a procedure with no snapshots, as snapshots are always dropped)
				if codomain_size == 8 {
					instructions.push(MovFromReg(RAX, RSI));
				}

				instructions.extend([Leave, Ret])
			}
		},
		FlowTerminator::Jump {
			continuation_label,
			domain,
			argument,
		} => {
			let continuation_and_parameter = if let Some(continuation_label) = continuation_label {
				Some((
					continuation_label,
					stack_frame.get_phi(continuation_label).expect("no such continuation"),
				))
			} else {
				None
			};

			let phi_buffer = if let Some((continuation_label, (_, _))) = continuation_and_parameter {
				if let FlowOperand::Copy(projection) = argument {
					if let FlowVariable::Local(root) = projection.root {
						if stack_frame.current_visibles.contains(&root)
							&& stack_frame.continuation_to_visibles[continuation_label].contains(&root)
							&& projection.is_indirect()
						{
							let [phi_buffer_label] = symbol_generator.fresh();
							let phi_buffer_offset = stack_frame.allocate(phi_buffer_label, domain.clone(), false);
							Some((FlowProjection::new(FlowVariable::Local(phi_buffer_label)), phi_buffer_offset))
						} else {
							None
						}
					} else {
						None
					}
				} else {
					None
				}
			} else {
				None
			};

			stack_frame.emit_clones(symbol_generator, argument, instructions);

			match argument {
				FlowOperand::Copy(projection) => {
					let size = size_of_ty(&domain);

					if let Some((continuation_label, (_, parameter))) = continuation_and_parameter {
						if let Some((_, phi_buffer_offset)) = phi_buffer {
							if size == 0 {
								()
							} else if size == 8 {
								stack_frame.emit_load::<true>(RAX, projection, instructions);
								instructions.push(MovIntoAddressFromReg((RBP, phi_buffer_offset), RAX));
							} else {
								stack_frame.emit_load::<false>(RSI, projection, instructions);
								instructions.extend([
									LEA(RDI, (RBP, phi_buffer_offset)),
									MovFromU64(RCX, u64::from(size) / 8),
									RepMovsq,
								]);
							}
						}

						let projection = if let Some((phi_buffer_projection, _)) = phi_buffer {
							phi_buffer_projection
						} else {
							projection.clone()
						};

						stack_frame.emit_drops(Some(continuation_label.clone()), instructions, symbol_generator);

						if size == 0 {
							()
						} else if size == 8 {
							stack_frame.emit_load::<true>(RAX, &projection, instructions);
							instructions.push(MovIntoAddressFromReg((RBP, parameter), RAX));
						} else {
							stack_frame.emit_load::<false>(RSI, &projection, instructions);
							instructions.extend([LEA(RDI, (RBP, parameter)), MovFromU64(RCX, u64::from(size) / 8), RepMovsq]);
						}

						instructions.push(Jmp(emit_block_local_label(continuation_label.clone())));
					} else {
						if size == 0 {
							()
						} else if size == 8 {
							// TODO: If no drops are emitted, we don't have to preserve RAX in RSI.
							// (But this can only happen in a procedure with no snapshots, as snapshots are always dropped)
							stack_frame.emit_load::<true>(RSI, projection, instructions);
						} else if let Some(mailbox_offset) = mailbox_offset {
							stack_frame.emit_load::<false>(RSI, projection, instructions);
							instructions.extend([
								MovFromAddress(RDI, (RBP, mailbox_offset)),
								MovFromU64(RCX, u64::from(size) / 8),
								RepMovsq,
							]);
						} else {
							panic!("oversized value (or between-sized) but no mailbox to return to")
						}
						stack_frame.emit_drops(None, instructions, symbol_generator);
						// TODO: If no drops are emitted, we don't have to preserve RAX in RSI.
						// (But this can only happen in a procedure with no snapshots, as snapshots are always dropped)
						if size == 8 {
							instructions.push(MovFromReg(RAX, RSI));
						}

						instructions.push(Leave);
						instructions.push(Ret);
					}
				},
				FlowOperand::Constant(primitive) => {
					match primitive {
						FlowPrimitive::Unity => (),
						FlowPrimitive::Polarity(p) => {
							instructions.push(MovFromI64(RAX, *p as i64));
						},
						FlowPrimitive::Integer(n) => {
							instructions.push(MovFromI64(RAX, *n));
						},
						FlowPrimitive::Procedure(label) => {
							instructions.push(MovFromLabel(RAX, emit_procedure_label(label.clone())))
						},
					}

					if let Some((continuation_label, (_, parameter))) = continuation_and_parameter {
						instructions.push(MovIntoAddressFromReg((RBP, parameter), RAX));
						instructions.push(Jmp(emit_block_local_label(continuation_label.clone())));
					} else {
						instructions.push(Leave);
						instructions.push(Ret);
					}
				},
			}
		},
	}
}

// For now, every size should be a multiple of 8.
pub fn size_of_ty(ty: &FlowType) -> u32 {
	match ty {
		FlowType::Unity => 0,
		FlowType::Polarity => 8,
		FlowType::Integer => 8,
		FlowType::Product(factors) => factors.iter().map(size_of_ty).fold(0, core::ops::Add::add),
		FlowType::Procedure => 8,
		FlowType::Snapshot(_) => 8,
	}
}

pub fn emit_procedure_label(label: Label) -> String {
	["_", label.handle().to_string().as_str()].concat()
}

pub fn label_from_id(id: Label) -> String {
	id.handle().to_string()
}
