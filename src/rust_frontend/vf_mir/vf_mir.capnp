@0x810f32815ffa3aa2;
struct Option(T) {
    union {
        nothing @0: Void;
        something @1: T;
    }
}

struct Ty {
    struct IntTy {
        union {
            iSize @0: Void;
            i32 @1: Void;
        }
    }

    struct AdtData {
        struct AdtDef {
            struct VariantDef {
                name @0: Text;
                discr @1: UInt64;
                fields @2: List(Ty);
            }

            variants @0: List(VariantDef);
            #TODO @Nima: We will need AdtFlags. For now it is just struct
        }

        struct AdtSubs {}

        def @0: AdtDef;
        subs @1: List(AdtSubs);
    }

    struct TyKind {
        union {
            bool @0: Void;
            int @1: IntTy;
            adt @2: AdtData;
        }
    }

    kind @0: TyKind;
}

struct Body {
    struct SourceInfo {}

    struct Annotation {
        raw @0: Text;
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

    struct Mutability {
        union {
            mut @0: Void;
            not @1: Void;
        }
    }

    struct LocalDeclId {
        name @0: Text;
    }

    struct LocalDecl {
        mutability @0: Mutability;
        id @1: LocalDeclId;
        ty @2: Ty;
    }

    struct BasicBlockId {
        name @0: Text;
    }

    struct BasicBlock {
        struct Place {
            struct PlaceElement {
                union {
                    deref @0: Void;
                    field @1: Text;
                }
            }

            local @0: LocalDeclId;
            projection @1: List(PlaceElement);
        }

        struct Operand {
            union {
                copy @0: Place;
                move @1: Place;
            }
        }

        struct RValue {
            struct AddressOfData {
                mutability @0: Mutability;
                place @1: Place;
            }

            union {
                # Either move or copy depending on operand type
                use @0: Operand;
                addressOf @1: AddressOfData;
            }
        }

        struct Statement {
            struct StatementKind {
                struct AssignData {
                    place @0: Place;
                    rvalue @1: RValue;
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
                        targets @0: List(BasicBlockId);
                        otherwise @1: Option(BasicBlockId);
                    }

                    discr @0: Operand;
                    targets @1: SwitchTargets;
                }

                union {
                    goto @0: BasicBlockId;
                    switchInt @1: SwitchIntData;
                }
            }

            sourceInfo @0: SourceInfo;
            kind @1: TerminatorKind;
        }

        statements @0: List(Statement);
        terminator @1: Terminator;
    }

    defKind @0: DefKind;
    defPath @1: Text;
    contract @2: Contract;
    argCount @3: UInt32;
    localDecls @4: List(LocalDecl);
    basicBlocks @5: List(BasicBlock);
}

struct VfMir {
    bodies @0: List(Body);
}
#TODO @Nima: For Clarity write a struct fields on top and then inner type definitions