module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
module OptionRd = VfMirStub.Reader.Option
module VfMirRd = VfMirStub.Reader.VfMir

(* Source Spans *)
module SpanDataRd = VfMirStub.Reader.SpanData
module LocRd = SpanDataRd.Loc
module SourceFileRd = LocRd.SourceFile
module FileNameRd = SourceFileRd.FileName
module RealFileNameRd = FileNameRd.RealFileName
module PathBufRd = RealFileNameRd.PathBuf
module CharPosRd = LocRd.CharPos

(* Bodies *)
module BodyRd = VfMirStub.Reader.Body
module ContractRd = BodyRd.Contract
module AnnotationRd = BodyRd.Annotation
module LocalDeclRd = BodyRd.LocalDecl
module MutabilityRd = VfMirStub.Reader.Mutability
module LocalDeclIdRd = BodyRd.LocalDeclId
module BasicBlockRd = BodyRd.BasicBlock
module BasicBlockIdRd = BodyRd.BasicBlockId
module TerminatorRd = BasicBlockRd.Terminator
module TerminatorKindRd = TerminatorRd.TerminatorKind
module FnCallDataRd = TerminatorKindRd.FnCallData
module OperandRd = BasicBlockRd.Operand
module ConstantRd = BasicBlockRd.Constant
module ConstantKindRd = ConstantRd.ConstantKind
module PlaceRd = BasicBlockRd.Place
module DestinationDataRd = FnCallDataRd.DestinationData
module StatementRd = BasicBlockRd.Statement
module StatementKindRd = StatementRd.StatementKind
module RvalueRd = BasicBlockRd.Rvalue
module SourceInfoRd = BodyRd.SourceInfo

(* Types *)
module TyRd = VfMirStub.Reader.Ty
module UIntTyRd = TyRd.UIntTy
module AdtTyRd = TyRd.AdtTy
module AdtDefIdRd = TyRd.AdtDefId
module FnDefTyRd = TyRd.FnDefTy
module FnDefIdRd = TyRd.FnDefId
module GenArgRd = TyRd.GenArg
module GenArgKindRd = GenArgRd.GenArgKind
module RawPtrTyRd = TyRd.RawPtrTy
module TyConstRd = TyRd.Const
