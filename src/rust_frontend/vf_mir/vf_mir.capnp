@0x810f32815ffa3aa2;
# Todo @Nima: Move Util to another capnp file
struct Util {
    struct UInt128 {
        h @0: UInt64;
        l @1: UInt64;
    }

    using BigUInt = UInt128;

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
}

using Util.UInt128;
using Util.BigUInt;
using Util.Option;
using Util.IndList;

struct SpanData {
    struct Loc {
        struct CharPos {
            pos @0: UInt64;
        }
        struct SourceFile {
            struct FileName {
                struct RealFileName {
                    struct PathBuf {
                        inner @0: Text;
                    }
                    union {
                        localPath @0: PathBuf;
                        remapped @1: Void;
                    }
                }
                union {
                    real @0: RealFileName;
                    quoteExpansion @1: UInt64;
                }
            }
            name @0: FileName;
        }
        file @0: SourceFile;
        # 1 based
        line @1: UInt64;
        # 0 based
        col @2: CharPos;
    }
    lo @0: Loc;
    hi @1: Loc;
}

struct Mutability {
    union {
        mut @0: Void;
        not @1: Void;
    }
}

struct Ty {

    struct ConstKind {
        union {
            param @0: Void;
            value @1: Body.ConstValue;
        }
    }

    # Typed constant value
    struct Const {
        ty @0: Ty;
        val @1: ConstKind;
    }

    struct Region {
        id @0: Text;
    }

    struct GenArg {
        struct GenArgKind {
            union {
                lifetime @0: Void;
                type @1: Ty;
                const @2: Void;
            }
        }
        kind @0: GenArgKind;
    }

    struct IntTy {
        union {
            iSize @0: Void;
            i32 @1: Void;
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

    struct AdtDefId {
        name @0: Text;
    }

    struct AdtDef {
        struct VariantDef {
            struct FieldDef {
                struct Visibility {
                    union {
                        public @0: Void;
                        restricted @1: Void;
                        invisible @2: Void;
                    }
                }

                name @0: Text;
                ty @1: Ty;
                vis @2: Visibility;
            }

            #name @0: Text;
            #discr @1: UInt64;
            fields @0: List(FieldDef);
        }

        struct AdtKind {
            union {
                structKind @0: Void;
                enumKind @1: Void;
                unionKind @2: Void;
            }
        }

        id @0: AdtDefId;
        variants @1: List(VariantDef);
        kind @2: AdtKind;
    }

    struct AdtTy {
        id @0: AdtDefId;
        substs @1: List(GenArg);
    }

    struct FnDefId {
        name @0: Text;
    }

    struct FnDefTy {
        id @0: FnDefId;
        idMono @1: Option(FnDefId);
        substs @2: List(GenArg);
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

    struct TyKind {
        union {
            bool @0: Void;
            int @1: IntTy;
            uInt @2: UIntTy;
            adt @3: AdtTy;
            rawPtr @4: RawPtrTy;
            ref @5: RefTy;
            fnDef @6: FnDefTy;
            never @7: Void;
            tuple @8: List(GenArg);
        }
    }

    kind @0: TyKind;
}

struct Body {
    struct SourceInfo {
        struct SourceScope {}
        span @0: SpanData;
        scope @1: SourceScope;
    }

    struct Annotation {
        raw @0: Text;
        span @1: SpanData;
    }

    struct Contract {
        annotations @0: List(Annotation);
    }

    struct DefKind {
        union {
            fn @0: Void;
            assocFn @1: Void;
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

    struct Place {
        struct PlaceElement {
            union {
                deref @0: Void;
                field @1: Void;
            }
        }

        local @0: LocalDeclId;
        projection @1: List(PlaceElement);
    }

    struct Scalar {
        struct Int {
            # Todo
        }
        struct UInt { union {
            usize @0: BigUInt;
            u8 @1: UInt8;
            u16 @2: UInt16;
            u32 @3: UInt32;
            u64 @4: UInt64;
            u128 @5: UInt128;
        }}
        struct Float {
            # Todo
        }
        union {
            bool @0: Bool;
            char @1: Text;
            int @2: Int;
            uint @3: UInt;
            float @4: Float;
            fnDef @5: Void;
        }
    }

    struct ConstValue {
        union {
            scalar @0: Scalar;
            slice @1: Void;
        }
    }

    struct Constant {
        struct ConstantKind {
            union {
                ty @0: Ty.Const;
                val @1: Void;
            }
        }

        span @0: SpanData;
        literal @1: ConstantKind;
    }

    struct BasicBlockId {
        name @0: Text;
    }

    struct BasicBlock {
        struct Operand {
            union {
                copy @0: Place;
                move @1: Place;
                constant @2: Constant;
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

            union {
                # Either move or copy depending on operand type
                use @0: Operand;
                addressOf @1: AddressOfData;
                binaryOp @2: BinaryOpData;
            }
        }

        struct Statement {
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

            sourceInfo @0: SourceInfo;
            kind @1: StatementKind;
        }

        struct Terminator {
            struct TerminatorKind {
                struct SwitchIntData {
                    struct SwitchTargets {
                        struct Branch {
                            val @0: UInt128;
                            target @1: BasicBlockId;
                        }
                        branches @0: List(Branch);
                        otherwise @1: Option(BasicBlockId);
                    }

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
                    cleanup @3: Option(BasicBlockId);
                    fromHirCall @4: Bool;
                    # The span of the function, without the dot and receiver e.g. `foo(a, b)` in `x.foo(a, b)`
                    fnSpan @5: SpanData;
                }

                union {
                    goto @0: BasicBlockId;
                    switchInt @1: SwitchIntData;
                    resume @2: Void;
                    return @3: Void;
                    call @4: FnCallData;
                }
            }

            sourceInfo @0: SourceInfo;
            kind @1: TerminatorKind;
        }

        id @0: BasicBlockId;
        statements @1: List(Statement);
        terminator @2: Terminator;
        isCleanup @3: Bool;
    }

    struct VarDebugInfo {
        struct Symbol {
            name @0: Text;
        }
        struct VarDebugInfoContents {
            union {
                place @0: Place;
                const @1: Constant;
            }
        }
        name @0: Symbol;
        sourceInfo @1: SourceInfo;
        value @2: VarDebugInfoContents;
    }

    defKind @0: DefKind;
    defPath @1: Text;
    contract @2: Contract;
    argCount @3: UInt32;
    localDecls @4: List(LocalDecl);
    basicBlocks @5: List(BasicBlock);
    span @6: SpanData;
    impSpan @7: SpanData;
    varDebugInfo @8: List(VarDebugInfo);
}

struct VfMir {
    # Todo @Nima: We are using an inductive list to encode ADT definitions because the total size of `List`s
    # shoule be determined before initializing them which is not the case for ADT definitions. The standard way to
    # do this is capnp `orphans` which are not supported for Rust plugin at the time.
    adtDefs @0: IndList(Ty.AdtDef);
    bodies @1: List(Body);
}
#Todo @Nima: For Clarity write a struct fields on top and then inner type definitions
#Todo @Nima: Use a uniform naming. def_path for Rust style definition paths and Name for their corresponding translated names.