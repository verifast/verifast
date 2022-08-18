module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
module VfMirRd = VfMirStub.Reader.VfMir

(* Bodies *)
module BodyRd = VfMirStub.Reader.Body
module ContractRd = BodyRd.Contract
module AnnotationRd = BodyRd.Annotation
module LocalDeclRd = BodyRd.LocalDecl
module MutabilityRd = BodyRd.Mutability
module LocalDeclIdRd = BodyRd.LocalDeclId
module BasicBlockRd = BodyRd.BasicBlock
module BasicBlockIdRd = BodyRd.BasicBlockId
module TerminatorRd = BasicBlockRd.Terminator
module TerminatorKindRd = TerminatorRd.TerminatorKind
module FnCallDataRd = TerminatorKindRd.FnCallData
module OperandRd = BasicBlockRd.Operand
module ConstantRd = BasicBlockRd.Constant
module ConstantKindRd = ConstantRd.ConstantKind

(* Types *)
module TyRd = VfMirStub.Reader.Ty
module UIntTyRd = TyRd.UIntTy
module AdtTyRd = TyRd.AdtTy
module AdtDefIdRd = TyRd.AdtDefId
