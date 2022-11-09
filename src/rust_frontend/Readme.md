# Rust Frontend
<!-- TODO @Nima: fill in -->
## Module Hierarchy
func VerifyProgram(..) {
    inc VerifyExpr(..)
    func CheckFile(..) {
        inc CheckFile_VerifyExpr(..)
    }
}

func VerifyExpr(..) {
    inc Assertions(..)
    func CheckFile_VerifyExpr {
        inc CheckFile_Assertions(..)
    }
}

func Assertions(..) {
    inc VerifyProgram1(..)
    func CheckFile_Assertions(..) {
        inc CheckFile1(..)
    }
}