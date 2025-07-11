Inductive Instruction : Type :=
    | IPush (n: nat)
    | IMstore
    | IMload
    | IAdd
    | IOutput
    | IEq
    | IJmpi
    | IDup
    | IPop
    | ISwap.

