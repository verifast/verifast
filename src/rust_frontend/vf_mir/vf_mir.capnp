@0x810f32815ffa3aa2;

struct Int128 {
    h @0: Int64;
    l @1: UInt64;
}

struct UInt128 {
    h @0: UInt64;
    l @1: UInt64;
}

using BigInt = Int128;
using BigUInt = UInt128;
# Todo @Nima: We are using `BigUInt` for encoding `usize` values. It is better to have a distinct type for them.

struct Option(T) {
    union {
        nothing @0: Void;
        something @1: T;
    }
}

struct IndList(T) {
    union {
        nil @0: Void;
        cons :group {
            h @1: T;
            t @2: IndList(T);
        }
    }
}

struct TextWrapper {text @0: Text;} #The pointer in Option just supports structs

struct CharPos {
    pos @0: UInt64;
}

struct RealFileName {
    struct RemappedData {
        localPath @0: Option(TextWrapper);
        virtualName @1: Text;
    }
    union {
        localPath @0: Text;
        remapped @1: RemappedData;
    }
}

struct FileName {
    union {
        real @0: RealFileName;
        quoteExpansion @1: UInt64;
    }
}

struct SourceFile {
    name @0: FileName;
}

struct Loc {
    file @0: SourceFile;
    # 1 based
    line @1: UInt64;
    # 0 based
    col @2: CharPos;
}

struct SpanData {
    union {
        dummy @0: Void;
        regular :group {
            lo @1: Loc;
            hi @2: Loc;
        }
    }
}

# It is also possible to use `Enum`s here but it would be easier to add
# data to variants later in case it became necessary
struct Unsafety {
    union {
        safe @0: Void;
        unsafe @1: Void;
    }
}

struct Mutability {
    union {
        mut @0: Void;
        not @1: Void;
    }
}

struct Symbol {
    name @0: Text;
}

struct Ident {
    name @0: Symbol;
    span @1: SpanData;
}

struct Visibility {
    union {
        public @0: Void;
        restricted @1: Void;
    }
}

struct Annotation {
    raw @0: Text;
    span @1: SpanData;
    startLine @2: UInt64;
    startCol @3: UInt64;
    endLine @4: UInt64;
    endCol @5: UInt64;
}

struct Hir {
    struct Generics {
        struct GenericParam {
            struct ParamName {
                union {
                    plain @0: Ident;
                    fresh @1: BigUInt;
                }
            }
            struct GenericParamKind {
                union {
                    lifetime @0: Void;
                    type @1: Void;
                    const @2: Void;
                }
            }
            name @0: ParamName;
            bounds @1: Void;
            span @2: SpanData;
            pureWrtDrop @3: Bool;
            kind @4: GenericParamKind;
        }
        params @0: List(GenericParam);
        whereClause @1: Void;
        span @2: SpanData;
    }
}

enum Variance {
    covariant @0;
    invariant @1;
    contravariant @2;
    bivariant @3;
}

struct ScalarInt {
    data @0: UInt128;
    size @1: UInt8;
}

struct ParamConst {
    index @0: UInt32;
    name @1: Text;
}

struct ValTree {
    union {
        leaf @0: ScalarInt;
        branch @1: Void;
    }
}

struct Value {
    ty @0: Ty;
    valTree @1: ValTree;
}

struct ConstKind {
    union {
        param @0: ParamConst;
        infer @2: Void;
        bound @3: Void;
        placeholder @4: Void;
        unevaluated @5: Void;
        value @1: Value;
        error @6: Void;
        expr @7: Void;
    }
}

# Typesystem constant
struct TyConst {
    kind @0: ConstKind;
}

struct Region {
    id @0: Text;
}

struct GenericArgKind {
    union {
        lifetime @0: Region;
        type @1: Ty;
        const @2: TyConst;
    }
}
struct IntTy {
    union {
        iSize @0: Void;
        i8 @1: Void;
        i16 @2: Void;
        i32 @3: Void;
        i64 @4: Void;
        i128 @5: Void;
    }
}

struct UIntTy {
    union {
        uSize @0: Void;
        u8 @1: Void;
        u16 @2: Void;
        u32 @3: Void;
        u64 @4: Void;
        u128 @5: Void;
    }
}


struct GenericArg {
    kind @0: GenericArgKind;
}

struct AdtDefId {
    name @0: Text;
}

struct AdtKind {
    union {
        structKind @0: Void;
        enumKind @1: Void;
        unionKind @2: Void;
    }
}

struct VariantDef {
    struct FieldDef {
        name @0: Symbol;
        ty @1: Ty;
        vis @2: Visibility;
        span @3: SpanData;
    }

    span @2: SpanData;
    name @1: Text;
    #discr @1: UInt64;
    fields @0: List(FieldDef);
}

struct AdtDef {
    id @0: AdtDefId;
    variants @1: List(VariantDef);
    kind @2: AdtKind;
    span @3: SpanData; # The span of the name of the ADT
    defSpan @9: SpanData; # The span of the entire ADT definition
    vis @4: Visibility;
    isLocal @5: Bool;
    hirGenerics @6: Hir.Generics;
    variances @10: List(Variance); # One for each generic lifetime or type parameter
    predicates @7: List(Predicate);
    implementsDrop @8: Bool;
    isReprC @11: Bool;
}

enum AliasTyKind {
    projection @0;
    inherent @1;
    opaque @2;
    weak @3;
}

struct FnDefId {
    name @0: Text;
}

struct TyKind {
    struct AdtTy {
        id @0: AdtDefId;
        kind @1: AdtKind;
        substs @2: List(GenericArg);
    }

    struct FnDefTy {
        id @0: FnDefId;
        substs @1: List(GenericArg);
        lateBoundGenericParamCount @2: UInt16; # The generic args are only for the early-bound params.
    }

    struct FnPtrTy {
        output @0: Ty; # We only need the return type for now
    }

    struct RawPtrTy {
        ty @0: Ty;
        mutability @1: Mutability;
    }

    struct RefTy {
        region @0: Region;
        ty @1: Ty;
        mutability @2: Mutability;
    }

    struct ClosureTy {
        defId @0: Text;
        substs @1: List(GenericArg);
    }

    struct AliasTy {
        kind @0: AliasTyKind;
        defId @1: Text;
        args @2: List(GenericArg);
    }

    struct ArrayTy {
        elemTy @0: Ty;
        size @1: TyConst;
    }

    union {
        bool @0: Void;
        int @1: IntTy;
        uInt @2: UIntTy;
        char @9: Void;
        float @16: Void; # TODO: Elaborate
        adt @3: AdtTy;
        foreign @17: Void; # TODO: Elaborate
        rawPtr @4: RawPtrTy;
        ref @5: RefTy;
        fnDef @6: FnDefTy;
        fnPtr @10: FnPtrTy;
        dynamic @19: Void; # TODO: Elaborate
        closure @20: ClosureTy; # TODO: Elaborate
        coroutineClosure @21: Void; # TODO: Elaborate
        coroutine @22: Void; # TODO: Elaborate
        coroutineWitness @23: Void; # TODO: Elaborate
        never @7: Void;
        tuple @8: List(Ty);
        alias @14: AliasTy;
        param @11: Text;
        bound @24: Void; # TODO: Elaborate
        placeholder @25: Void; # TODO: Elaborate
        infer @26: Void; # TODO: Elaborate
        error @27: Void; # TODO: Elaborate
        str @12: Void;
        array @15: ArrayTy;
        pattern @18: Void; # TODO: Elaborate
        slice @13: Ty;
    }
}

struct Ty {
    kind @0: TyKind;
}

# rustc_middle::ty::generics::GenericParamDefKind
struct GenericParamDefKind {
    union {
        lifetime @0: Void;
        type @1: Void;
        const @2: Void;
    }
}

# rustc_middle::ty::generics::GenericParamDef
struct GenericParamDef {
    name @0: Text;
    kind @1: GenericParamDefKind;
}

# A predicate that can appear in a 'where' clause
struct Predicate {
    struct Outlives {
        region1 @0: Region;
        region2 @1: Region;
    }
    struct Trait { # T : Foo<A, B, C>
        boundRegions @2: List(Text);
        defId @0: Text; # DefId of the trait (Foo)
        args @1: List(GenericArg); # The Self type (T) followed by the trait type args (A, B, C)
    }
    struct Projection { # <T as Trait<A, B, C>>::AssocType<D, E, F> == G
        struct AliasTerm { # <T as Trait<A, B, C>>::AssocType<D, E, F>
            defId @0: Text; # DefId of the associated type Trait::AssocType
            args @1: List(GenericArg); # The Self type (T) followed by the trait args (A, B, C) and the associated type args (D, E, F)
        }
        struct Term {
            union {
                ty @0: Ty;
                const @1: TyConst;
            }
        }
        boundRegions @2: List(Text);
        projectionTerm @0: AliasTerm;
        term @1: Term; # G
    }
    union {
        outlives @0: Outlives;
        trait @2: Trait;
        projection @3: Projection;
        ignored @1: Void; # A predicate that we are ignoring for now
    }
}

struct LocalDeclId {
    name @0: Text;
}

struct LocalDecl {
    mutability @0: Mutability;
    id @1: LocalDeclId;
    ty @2: Ty;
    sourceInfo @3: SourceInfo;
}

struct PlaceKind {
    union {
        mutableRef @0: Void;
        sharedRef @1: Void;
        other @2: Void;
    }
}

struct PlaceElem {
    struct FieldData {
        index @0: UInt32;
        name @1: Option(Symbol);
        ty @2: Ty;
    }
    union {
        deref @0: Void;
        field @1: FieldData;
        boxAsNonNull @8: Ty; # The MIR pattern `(X.0: std::ptr::Unique<T>).0: std::ptr::NonNull<T>` when X is a Box<T>. The Ty is T. Always appears as part of an RValue::Cast(CastKind::Transmute, Operand::Copy(local.BoxAsNonNull)) (https://github.com/rust-lang/rust/blob/18491d5be00eb3ed2f1ccee2ac5b792694f2a7a0/compiler/rustc_mir_transform/src/elaborate_box_derefs.rs#L71)
        index @3: Void;
        constantIndex @4: Void;
        subslice @5: Void;
        downcast @2: UInt32;
        opaqueCast @6: Void;
        subtype @7: Void;
    }
}

struct Place {
    local @0: LocalDeclId;
    localIsMutable @2: Bool;
    projection @1: List(PlaceElem);
    kind @3: PlaceKind;
}

struct Scalar {
    union {
        int @0: ScalarInt;
        ptr @1: Void;
    }
}

struct ConstValue {
    union {
        scalar @0: Scalar;
        zeroSized @2: Void;
        slice @1: Data;
    }
}

struct MirConst {
    struct TyData {
        ty @0: Ty;
        const @1: TyConst;
    }
    union {
        ty @0: TyData;
        val :group {
            constValue @1: ConstValue;
            ty @2: Ty;
        }
        unevaluated :group {
            def @3: Text;
            args @4: List(GenericArg);
        }
    }
}

struct ConstOperand {
    span @0: SpanData;
    const @1: MirConst;
}

struct BasicBlockId {
    index @0: UInt32;
}

struct Operand {
    union {
        copy @0: Place;
        move @1: Place;
        constant @2: ConstOperand;
    }
}

struct AggregateKind {
    struct AdtData {
        struct FieldInfo {
            name @0: Text;
            isZeroSize @1: Bool; # if true, sizeof(field) = 0 && field.ty.OWN = True. This must match the fields treated as ZST (and dropped from the VeriFast struct definition) in translate_adt_def
        }
        adtId @0: AdtDefId;
        variantIdx @1: UInt32;
        variantId @5: Text;
        genArgs @2: List(GenericArg);
        userTypeAnnotationIndex @3: Void;
        unionActiveField @4: UInt32;
        fields @6: List(FieldInfo);
        adtKind @7: AdtKind;
    }
    struct ClosureData {
        closureId @0: Text;
        genArgs @1: List(GenericArg);
    }
    union {
        array @0: Ty; #Elements type
        tuple @1: Void;
        adt @2: AdtData;
        closure @3: ClosureData;
        coroutine @4: Void;
        coroutineClosure @5: Void;
        rawPtr @6: Void; # Create a raw pointer from a thin pointer and metadata (length or vtable)
    }
}

struct Rvalue {
    struct AddressOfData {
        mutability @0: Mutability;
        place @1: Place;
    }

    struct BinaryOpData {
        struct BinOp {
            union {
                add @0: Void;
                sub @1: Void;
                mul @2: Void;
                div @3: Void;
                rem @4: Void;
                bitXor @5: Void;
                bitAnd @6: Void;
                bitOr @7: Void;
                shl @8: Void;
                shr @9: Void;
                eq @10: Void;
                lt @11: Void;
                le @12: Void;
                ne @13: Void;
                ge @14: Void;
                gt @15: Void;
                offset @16: Void;
            }
        }
        operator @0: BinOp;
        operandl @1: Operand;
        operandr @2: Operand;
    }

    struct UnaryOpData {
        struct UnOp {
            union {
                not @0: Void;
                neg @1: Void;
            }
        }
        operator @0: UnOp;
        operand @1: Operand;
    }

    struct RefData {
        struct BorrowKind {
            union {
                shared @0: Void;
                mut @1: Void;
            }
        }
        region @0: Region;
        borKind @1: BorrowKind;
        placeTy @3: Ty;
        place @2: Place;
        isImplicit @4: Bool;
        placeDoesNotNeedDrop @5: Bool;
    }

    struct CastData {
        operand @0: Operand;
        ty @1: Ty;
    }

    struct AggregateData {
        aggregateKind @0: AggregateKind;
        operands @1: List(Operand);
    }

    union {
        # Either move or copy depending on operand type
        use @0: Operand;
        repeat @8: Void;
        ref @1: RefData;
        threadLocalRef @9: Void;
        addressOf @2: AddressOfData;
        len @10: Void;
        cast @3: CastData;
        binaryOp @4: BinaryOpData;
        nullaryOp @11: Void;
        unaryOp @6: UnaryOpData;
        aggregate @5: AggregateData;
        discriminant @7: Place;
        shallowInitBox @12: Void;
    }
}

struct StatementKind {
    struct AssignData {
        lhsPlace @0: Place;
        rhsRvalue @1: Rvalue;
    }

    union {
        assign @0: AssignData;
        nop @1: Void;
    }
}

struct Statement {
    sourceInfo @0: SourceInfo;
    kind @1: StatementKind;
}

struct SwitchTargets {
    struct Branch {
        val @0: UInt128;
        target @1: BasicBlockId;
    }
    branches @0: List(Branch);
    otherwise @1: Option(BasicBlockId);
}

struct UnwindAction {
    union {
        continue @0: Void;
        unreachable @1: Void;
        terminate @2: Void;
        cleanup @3: BasicBlockId;
    }
}

struct TerminatorKind {
    struct SwitchIntData {
        discr @0: Operand;
        discrTy @1: Ty;
        targets @2: SwitchTargets;
    }

    struct FnCallData {
        struct DestinationData {
            place @0: Place;
            basicBlockId @1: BasicBlockId;
        }
        func @0: Operand;
        args @1: List(Operand);
        destination @2: Option(DestinationData);
        unwindAction @5: UnwindAction;
        # The span of the call, without the dot and receiver e.g. `foo(a, b)` in `x.foo(a, b)`
        callSpan @3: SpanData;
        ghostGenericArgList @4: Option(Annotation);
    }

    struct DropData {
        place @0: Place;
        target @1: BasicBlockId;
        unwindAction @2: UnwindAction;
    }

    union {
        goto @0: BasicBlockId;
        switchInt @1: SwitchIntData;
        unwindResume @2: Void;
        unwindTerminate @7: Void;
        return @3: Void;
        unreachable @6: Void;
        call @4: FnCallData;
        drop @5: DropData;
        tailCall @8: Void;
        assert @9: Void;
        yield @10: Void;
        coroutineDrop @11: Void;
        falseEdge @12: Void;
        inlineAsm @13: Void;
    }
}

struct Terminator {
    sourceInfo @0: SourceInfo;
    kind @1: TerminatorKind;
}

struct BasicBlock {
    id @0: BasicBlockId;
    statements @1: List(Statement);
    terminator @2: Terminator;
    isCleanup @3: Bool;
}

struct VarDebugInfoContents {
    union {
        place @0: Place;
        const @1: ConstOperand;
    }
}

struct VarDebugInfo {
    name @0: Symbol;
    sourceInfo @1: SourceInfo;
    value @2: VarDebugInfoContents;
}

struct SourceInfo {
    #struct SourceScope {}
    span @0: SpanData;
    #scope @1: SourceScope;
}

struct Contract {
    annotations @0: List(Annotation);
    span @1: SpanData;
}

struct Body {
    struct DefKind {
        union {
            fn @0: Void;
            assocFn @1: Void;
            closure @2: Void;
        }
    }

    struct GhostDeclBlock {
        start @0: Annotation;
        closeBraceSpan @1: SpanData; # After preprocessing, to match against the span of the inserted VeriFast_ghost_command() call.
    }

    fnSigSpan @21: SpanData;
    defKind @0: DefKind;
    defPath @1: Text;
    moduleDefPath @18: Text; # Empty string if in crate root
    contract @2: Contract;
    output @16: Ty;
    inputs @3: List(Ty);
    localDecls @4: List(LocalDecl);
    basicBlocks @5: List(BasicBlock);
    span @6: SpanData;
    impSpan @7: SpanData;
    varDebugInfo @8: List(VarDebugInfo);
    ghostStmts @9: List(Annotation);
    ghostDeclBlocks @15: List(GhostDeclBlock); # A Rust block starting with a ghost range containing ghost declarations (local predicates and lemmas)
    unsafety @10: Unsafety;
    implBlockHirGenerics @14: Option(Hir.Generics);
    implBlockGenerics @23: List(GenericParamDef);
    implBlockPredicates @19: List(Predicate);
    hirGenerics @11: Hir.Generics;
    generics @20: List(GenericParamDef); # Has only the early-bound generic params
    predicates @17: List(Predicate);
    isTraitFn @12: Bool;
    isDropFn @13: Bool; # Implements std::ops::Drop::drop
    visibility @22: Visibility;
}

struct Trait {
    struct RequiredFn {
        name @0: Text;
        nameSpan @6: SpanData;
        unsafety @4: Unsafety;
        lifetimeParams @7: List(Text);
        inputs @1: List(Ty);
        output @2: Ty;
        argNames @3: List(Text);
        contract @5: List(Annotation);
    }

    name @0: Text;
    requiredFns @1: IndList(RequiredFn);
}

struct TraitImplItem {
    name @0: Text;
    defId @1: Text;
}

struct TraitImpl {
    span @3: SpanData;
    isUnsafe @4: Bool;
    isNegative @5: Bool;
    ofTrait @0: Text;
    genArgs @8: List(GenericArg); # The first argument is the self type
    selfTy @1: Text;
    generics @6: List(GenericParamDef);
    predicates @7: List(Predicate);
    items @2: List(TraitImplItem);
}

struct Module {
    name @0: Text;
    headerSpan @4: SpanData;
    bodySpan @1: SpanData;
    submodules @2: List(Module);
    ghostDeclBatches @3: List(Annotation);
}

struct VfMir {
    targetTriple @7: Text;
    pointerWidth @8: UInt8;
    directives @4: List(Annotation);
    # Todo @Nima: We are using an inductive list to encode ADT definitions because the total size of `List`s
    # shoule be determined before initializing them which is not the case for ADT definitions. The standard way to
    # do this is capnp `orphans` which are not supported for Rust plugin at the time.
    adtDefs @0: IndList(AdtDef);
    traits @5: IndList(Trait);
    traitImpls @3: List(TraitImpl);
    bodies @1: List(Body);
    ghostDeclBatches @2: List(Annotation);
    modules @6: List(Module);
}
#Todo @Nima: For Clarity write a struct fields on top and then inner type definitions
#Todo @Nima: Use a uniform naming. def_path for Rust style definition paths and Name for their corresponding translated names.
