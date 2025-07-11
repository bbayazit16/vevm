Require Import Vevm.Instruction.

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import String.

Import ListNotations.

Record VmState := {
    stack: list nat;
    pc: nat
}.

Inductive VmResult :=
    | Ok (s : VmState)
    | Err (msg : string).

Definition succeeds (result: VmResult) : bool := match result with
    | Ok state => true
    | Err _ => false
    end.

Definition output (result: VmResult) : nat := match result with
    | Ok state => match state.(stack) with
            | result :: [] => result
            | _ => 0
        end
    | Err _ => 0
    end.

Definition interpret (instr : Instruction) (state: VmState) : VmResult :=
    match instr with
        | IPush n => Ok {| stack := n :: state.(stack) ; pc := state.(pc) + 1 |}
        | IAdd => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (a + b) :: s' ; pc := state.(pc) + 1 |}
            | _ => Err "add failed"
            end
        | IOutput => match state.(stack) with
            | a :: rest' => Ok {| stack := [a] ; pc := state.(pc) + 1 |}
            | _ => Err "output failed"
            end
        | IEq => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (if Nat.eqb a b then 1 else 0) :: s' ; pc := state.(pc) + 1 |}
            | _ => Err "eq failed"
            end
        | IJmp => match state.(stack) with
            | should_jump :: address :: s' => if should_jump then
                Ok {|stack := s'; pc := address |}
                else Ok {| stack := s'; pc := state.(pc) + 1 |}
            | _ => Err "jmp failed"
            end
        | IDup => match state.(stack) with
            | a :: s' => Ok {| stack := (a :: (a :: s')) ; pc := state.(pc) + 1 |}
            | _ => Err "dup failed"
            end
        | IPop => match state.(stack) with
            | a :: s' => Ok {| stack := s'; pc := state.(pc) + 1 |}
            | _ => Err "nothing to pop"
            end
        | ISwap => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (b :: (a :: s')) ; pc := state.(pc) + 1 |}
            | _ => Err "swap failed"
            end
end.

Fixpoint interpret_all' (instrs: list Instruction) (state: VmState) (fuel: nat) : VmResult :=
    match fuel with
    | 0 => Err "out of fuel"
    | S fuel' =>
        match List.nth_error instrs state.(pc) with
            | None => Err "pc out of bounds"
            | Some IOutput =>
             match interpret IOutput state with
                | Err e     => Err e
                | Ok state' => Ok state'
             end
            | Some instr => match interpret instr state with
                | Err e => Err e
                | Ok state' => interpret_all' instrs state' fuel'
            end
        end
    end.


Definition interpret_all (instrs: list Instruction) : VmResult :=
    interpret_all' instrs {| stack := []; pc := 0 |} 1000.
(*

result = 0
i = 0
while i != 5:
    result += i
    i += 1
return result

*)

Definition program : list Instruction := [ 
  
].

Compute interpret_all program.


(* Require Extraction.

Extraction Language OCaml.
Extract Constant Nat.add => "( + )".
Extract Inductive nat => "int" ["0" "succ" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" ["Some" "None"].


Extraction "vm.ml" interpret. *)
