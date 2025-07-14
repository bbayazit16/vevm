Require Import Vevm.Instruction.
Require Import Vevm.Vm.

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import String.

Import ListNotations.
Open Scope string_scope.

Lemma fuel_step_same :
  forall program state output_state fuel,
  interpret_all' program state fuel = Ok output_state ->
  interpret_all' program state (S fuel) = Ok output_state.
Proof.
  intros program state output_state fuel H.
  generalize dependent output_state.
  generalize dependent state.
  
  induction fuel as [|fuel' IHfuel]; intros state output_state H.
  (* H = fuel ok, interpret_all' program state fuel = Ok output_state *)
  - compute in H; discriminate.
  - unfold interpret_all' in H |- *; fold interpret_all' in H |- *.
    destruct (List.nth_error program (pc state)) as [instr|]; [|discriminate].
    destruct instr; (destruct (interpret _ state); [apply IHfuel; exact H | discriminate]) || exact H.
Qed.

Theorem more_fuel_ok:
  forall instrs state output_state fuel more_fuel,
  more_fuel >= fuel ->
  interpret_all' instrs state fuel = Ok output_state ->
  interpret_all' instrs state more_fuel = Ok output_state.
Proof.
  intros instrs state output_state fuel more_fuel.
  remember (more_fuel - fuel) as fuel_dist.

  generalize dependent more_fuel.
  induction fuel_dist as [| fuel_dist' IHdist].
  - intros more_fuel fuel_same more_fuel_ge_fuel interpret_ok.
    assert (eq: more_fuel = fuel) by lia.
    rewrite eq.
    exact interpret_ok.
  - intros more_fuel s_fuel_dist_eq more_fuel_ge_fuel interpret_ok.
    destruct more_fuel as [| more_fuel'].
      + inversion s_fuel_dist_eq.
      + apply fuel_step_same.
        assert (H1: fuel_dist' = more_fuel' - fuel) by lia.
        (* True because H1 says more_fuel' - fuel which
          is a natural number and so must be positive, otherwise
          this doesn't follow from S more_fuel' >= fuel.
        *)
        assert (H2: more_fuel' >= fuel) by lia.
        apply (IHdist more_fuel' H1 H2 interpret_ok).
Qed.

Theorem empty_program_fails:
  forall fuel, exists msg, interpret_all_with_fuel [] fuel = Err msg.
Proof.
  intros fuel.
  unfold interpret_all_with_fuel, interpret_all'.
  destruct fuel; simpl; eexists; reflexivity.
Qed.

Theorem empty_program_result:
  forall fuel, output (interpret_all_with_fuel [] fuel) = 0.
Proof.
  intros fuel.
  destruct (empty_program_fails fuel) as [err_msg].
  rewrite H.
  unfold output.
  reflexivity.
Qed.

Theorem more_fuel_output_same:
    forall program fuel more_fuel,
    more_fuel >= fuel ->
        succeeds (interpret_all_with_fuel program fuel) = true ->
            output (interpret_all_with_fuel program fuel) = output (interpret_all_with_fuel program more_fuel).
Proof.
  intros program fuel more_fuel more_fuel_ge_fuel succeeds_fuel.
  unfold succeeds in succeeds_fuel.
  destruct (interpret_all_with_fuel program fuel) as [output_state | err_msg] eqn:fuel_ok.
  - unfold interpret_all_with_fuel in fuel_ok.
    assert (more_fuel_res : interpret_all' program {| stack := []; pc := 0; memory := NatMap.empty nat |} more_fuel = Ok output_state).
    apply (more_fuel_ok program {| stack := []; pc := 0; memory := NatMap.empty nat |} output_state fuel more_fuel more_fuel_ge_fuel fuel_ok).
    unfold interpret_all_with_fuel.
    rewrite more_fuel_res.
    reflexivity.
  - inversion succeeds_fuel.
Qed.
