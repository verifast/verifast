module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
module UtilRd = VfMirStub.Reader.Util
module VfMirRd = VfMirStub.Reader.VfMir

(* Util *)
module Int128Rd = UtilRd.Int128
module UInt128Rd = UtilRd.UInt128
module OptionRd = UtilRd.Option
module IndListRd = UtilRd.IndList
module TextWrapperRd = UtilRd.TextWrapper

(* Source Spans *)
module SpanDataRd = VfMirStub.Reader.SpanData
module LocRd = SpanDataRd.Loc
module SourceFileRd = LocRd.SourceFile
module FileNameRd = SourceFileRd.FileName
module RealFileNameRd = FileNameRd.RealFileName
module CharPosRd = LocRd.CharPos

(* Global *)
module MutabilityRd = VfMirStub.Reader.Mutability
module SymbolRd = VfMirStub.Reader.Symbol
module AnnotationRd = VfMirStub.Reader.Annotation
module UnsafetyRd = VfMirStub.Reader.Unsafety
module IdentRd = VfMirStub.Reader.Ident
module VisibilityRd = VfMirStub.Reader.Visibility

(* Hir *)
module HirRd = VfMirStub.Reader.Hir
module HirGenericsRd = HirRd.Generics
module HirGenericParamRd = HirGenericsRd.GenericParam
module HirGenericParamNameRd = HirGenericParamRd.ParamName
module HirGenericParamKindRd = HirGenericParamRd.GenericParamKind

(* Bodies *)
module BodyRd = VfMirStub.Reader.Body
module TraitImplRd = VfMirStub.Reader.TraitImpl
module ContractRd = BodyRd.Contract
module LocalDeclRd = BodyRd.LocalDecl
module LocalDeclIdRd = BodyRd.LocalDeclId
module BasicBlockRd = BodyRd.BasicBlock
module BasicBlockIdRd = BodyRd.BasicBlockId
module TerminatorRd = BasicBlockRd.Terminator
module TerminatorKindRd = TerminatorRd.TerminatorKind
module FnCallDataRd = TerminatorKindRd.FnCallData
module OperandRd = BasicBlockRd.Operand
module ConstantRd = BodyRd.Constant
module ConstantKindRd = ConstantRd.ConstantKind
module PlaceRd = BodyRd.Place
module PlaceElementRd = PlaceRd.PlaceElement
module DestinationDataRd = FnCallDataRd.DestinationData
module StatementRd = BasicBlockRd.Statement
module StatementKindRd = StatementRd.StatementKind
module RvalueRd = BasicBlockRd.Rvalue
module SourceInfoRd = BodyRd.SourceInfo
module SwitchIntDataRd = TerminatorKindRd.SwitchIntData
module SwitchTargetsRd = SwitchIntDataRd.SwitchTargets
module SwitchTargetsBranchRd = SwitchTargetsRd.Branch
module VarDebugInfoRd = BodyRd.VarDebugInfo
module VarDebugInfoContentsRd = VarDebugInfoRd.VarDebugInfoContents
module ConstValueRd = BodyRd.ConstValue
module ScalarRd = BodyRd.Scalar
module BinaryOpDataRd = RvalueRd.BinaryOpData
module UnaryOpDataRd = RvalueRd.UnaryOpData
module BinOpRd = BinaryOpDataRd.BinOp
module UnOpRd = UnaryOpDataRd.UnOp
module AggregateDataRd = RvalueRd.AggregateData
module AggregateKindRd = AggregateDataRd.AggregateKind

(* Types *)
module TyRd = VfMirStub.Reader.Ty
module IntTyRd = TyRd.IntTy
module UIntTyRd = TyRd.UIntTy
module AdtTyRd = TyRd.AdtTy
module AdtKindRd = TyRd.AdtKind
module AdtDefIdRd = TyRd.AdtDefId
module FnDefTyRd = TyRd.FnDefTy
module FnPtrTyRd = TyRd.FnPtrTy
module FnDefIdRd = TyRd.FnDefId
module GenArgRd = TyRd.GenArg
module GenArgKindRd = GenArgRd.GenArgKind
module RawPtrTyRd = TyRd.RawPtrTy
module RefTyRd = TyRd.RefTy
module TyConstRd = TyRd.Const
module TyConstKindRd = TyRd.ConstKind
module AdtDefRd = TyRd.AdtDef
module VariantDefRd = AdtDefRd.VariantDef
module FieldDefRd = VariantDefRd.FieldDef
module RegionRd = TyRd.Region
