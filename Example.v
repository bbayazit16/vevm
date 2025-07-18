Require Import Vevm.Vm.
Require Import Vevm.Instruction.
Require Import Vevm.VmProofs.

From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

Definition two_n_plus_eight_program (n: nat) : list Instruction := [
    IPush n;
    IPush n;
    IAdd;
    IPush 8;
    IAdd;
    IOutput
].

Definition two_n_plus_eight (n: nat) := 2 * n + 8.

(* Compute output (interpret_all_with_fuel (two_n_plus_eight_program 24) 6). *)

Theorem two_n_plus_eight_correctness :
  forall (n: nat), exists (fuel: nat),
    output (interpret_all_with_fuel (two_n_plus_eight_program n) fuel) = two_n_plus_eight n.
Proof.
  intros n.
  exists 6.
  simpl.
  unfold two_n_plus_eight.
  lia.
Qed.
