Require Import Vevm.Instruction.

From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import Structures.OrderedTypeEx.

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import String.

Import ListNotations.

Module NatMap := FMapAVL.Make(Nat_as_OT).

Record VmState := {
    stack: list nat;
    pc: nat;
    memory : NatMap.t nat;
    halted: bool;
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
        | IPush n => Ok {| stack := n :: state.(stack) ; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
        | IMstore => match state.(stack) with
            | offset :: value :: s' => Ok {|
                stack := s' ; pc := state.(pc) + 1; memory := (NatMap.add offset value state.(memory)); halted := false;
            |}
            | _ => Err "mstore failed"
            end
        | IMload => match state.(stack) with
            | offset :: s' =>
                match NatMap.find offset state.(memory) with
                    | Some found => Ok {| stack := found :: s'; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
                    | None => Err "failed to find key"
                end
            | _ => Err "failed to find key"
            end
        | IAdd => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (a + b) :: s' ; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "add failed"
            end
        | IOutput => match state.(stack) with
            | a :: rest' => Ok {| stack := [a] ; pc := state.(pc); memory := state.(memory); halted := true |}
            | _ => Err "output failed"
            end
        | IEq => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (if Nat.eqb a b then 1 else 0) :: s' ; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "eq failed"
            end
        | IJmpi => match state.(stack) with
            | should_jump :: address :: s' => if Nat.eqb should_jump 1 then
                Ok {|stack := s'; pc := address; memory := state.(memory); halted := false |}
                else Ok {| stack := s'; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "jmp failed"
            end
        | IDup => match state.(stack) with
            | a :: s' => Ok {| stack := (a :: (a :: s')) ; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "dup failed"
            end
        | IPop => match state.(stack) with
            | a :: s' => Ok {| stack := s'; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "nothing to pop"
            end
        | ISwap => match state.(stack) with
            | a :: b :: s' => Ok {| stack := (b :: (a :: s')) ; pc := state.(pc) + 1; memory := state.(memory); halted := false |}
            | _ => Err "swap failed"
            end
end.

Fixpoint interpret_all' (instrs: list Instruction) (state: VmState) (fuel: nat) : VmResult :=
    match fuel with
    | 0 => Err "out of fuel"
    | S fuel' =>
        if state.(halted) then
            Ok state
        else
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


Definition interpret_all (instrs: list Instruction): VmResult :=
    interpret_all' instrs {| stack := []; pc := 0 ; memory := NatMap.empty nat; halted := false |} 1000.


Definition interpret_all_with_fuel (instrs: list Instruction) (fuel: nat): VmResult :=
    interpret_all' instrs {| stack := []; pc := 0 ; memory := NatMap.empty nat; halted := false |} fuel.


(* Require Extraction.

Extraction Language OCaml.
Extract Constant Nat.add => "( + )".
Extract Inductive nat => "int" ["0" "succ" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" ["Some" "None"].


Extraction "vm.ml" interpret. *)
