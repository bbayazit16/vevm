Require Import Vevm.Instruction.
Require Import Vevm.Semantics.
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

Theorem all_programs_terminate :
  forall program fuel, exists result, interpret_all_with_fuel program fuel = result.
Proof.
  intros program fuel.
  remember (interpret_all_with_fuel program fuel) as actual_result.
  exists actual_result.
  reflexivity.
Qed.

Ltac solve_complete nth_ok H :=
    subst;
    rewrite nth_ok in H;
    injection H as H;
    subst;
    reflexivity.

Theorem interpret_complete :
  forall instructions instruction stack pc memory out_state,
    nth_error instructions pc = Some instruction ->
    step {| stack := stack; pc := pc; memory := memory |} instructions out_state ->
    interpret instruction {| stack := stack; pc := pc; memory := memory |} = Ok out_state.
Proof.
  intros instructions instruction stack pc memory out_state.
  intros nth_ok step_ok.
  
  inversion step_ok.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - subst.
    rewrite nth_ok in H2.
    injection H2 as H2.
    subst.
    simpl.
    rewrite H6.
    reflexivity.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - subst.
    rewrite nth_ok in H2.
    injection H2 as H2.
    subst.
    destruct should_jump as [|[|n]].
      * reflexivity.
      * exfalso. apply H6. reflexivity.
      * reflexivity.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
Qed.

Theorem interpret_sound:
  forall instrs instr stack pc memory output_state,
    nth_error instrs pc = Some instr ->
    interpret instr {|
      stack := stack;
      pc := pc;
      memory := memory
    |} = Ok output_state ->
    step {| stack := stack; pc := pc; memory := memory |} instrs output_state.
Proof.
  
(* Theorem interpret_sound:
    forall state instruction output_state,
    interpret instruction state = Ok output_state ->
    step state [instruction] output_state.
Proof.
  intros state instruction output_state H_interp_result.

  (* destruct (List.nth_error [instruction] state.(pc)) as [i|]. *)
  destruct state as [stack pc memory].
  simpl in *.

  destruct instruction.
  - simpl in *.
    injection H_interp_result as H_interp_result.
    rewrite <- H_interp_result.
    apply SIPush. *)


    (*   
    injection H_interp_result as H_interp_result.
    rewrite <- H_interp_result.
    (* clear H_interp_result. *)
    (* assert (H_case: i = (IPush n)).
    admit.
    subst i. *)
    
    destruct state as [stack pc memory].
    apply SIPush.
    simpl in *.
    subst output_state. *)
