Require Import Vevm.Vm.
Require Import Vevm.Instruction.

From Stdlib Require Import List.
Import ListNotations.

(*

result = 0
i = 0
while i != 5:
    result += i
    i += 1
return result

*)
Definition loop_sum_to_n (n: nat) : list Instruction :=
  [
    IPush 0; IPush 0; IMstore;
    IPush 0; IPush 1; IMstore;

    IPush 1; IMload;
    IPush (n + 1); IEq;
    IPush 29; ISwap; IJmpi;

    IPush 0; IMload;
    IPush 1; IMload;
    IAdd;
    IPush 0; IMstore;

    IPush 1; IMload;
    IPush 1; IAdd;
    IPush 1; IMstore;

    IPush 6; IPush 1; IJmpi;

    IPush 0; IMload; IOutput
  ].

Definition sum_up_to_n n := Nat.div (n * (n + 1)) 2.

(* Compute ((interpret_all_with_fuel (loop_sum_to_n 0) 39)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 1) 62)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 2) 85)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 3) 108)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 5) 154)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 6) 177)).
Compute (output (interpret_all_with_fuel (loop_sum_to_n 40) 959)).
Compute sum_up_to_n 40. *)

(* min fuel amount := 39 + 23n *)

Theorem loop_sum_to_n_correctness :
  forall (n: nat), exists (fuel: nat),
    output (interpret_all_with_fuel (loop_sum_to_n n) fuel) = sum_up_to_n n.
Proof.
  intros n.

  induction n as [| n IHn].
  - exists (39 + 23 * 0).
    compute.
    reflexivity.
  - destruct IHn as [fuel_n fuel_IHn].
    exists (fuel_n + 23).
    

Admitted.


