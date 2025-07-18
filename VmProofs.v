Require Import Vevm.Instruction.
Require Import Vevm.Semantics.
Require Import Vevm.Vm.

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From Stdlib Require Import Arith.PeanoNat.

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
    destruct (List.nth_error program (pc state)) as [instr|] eqn:H_instr_is.
    destruct state.(halted).
    + exact H.
    + destruct instr; (destruct (interpret _ state); [apply IHfuel; exact H | discriminate]) || exact H.
    + exact H.
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
    assert (more_fuel_res : interpret_all' program {| stack := []; pc := 0; memory := NatMap.empty nat; halted := false |} more_fuel = Ok output_state).
    apply (more_fuel_ok program {| stack := []; pc := 0; memory := NatMap.empty nat; halted := false |} output_state fuel more_fuel more_fuel_ge_fuel fuel_ok).
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

(* Haltedness and completion is not the same thing in this VM, because
  interpret_all eventually hits 'PC out of bounds' unless there's an
  IOutput.

  In other words, all programs must end with 'IOutput' instruction executed.
  This doesn't mean that IOutput must literally be the last instruction, but
  only that it must be the last instruction to be executed for a successful
  program.
*)
Definition has_halted (state : VmState) (instructions : list Instruction) : Prop :=
  exists output,
    state.(stack) = [output] /\
    state.(halted) = true /\
    List.nth_error instructions state.(pc) = Some IOutput.

(* The given state is terminal for the instructions.
   So an output state where we advanced by semantics (step) does not exist.
*)
Definition terminal (state : VmState) (instructions : list Instruction) : Prop :=
  forall output_state, ~(step state instructions output_state).


(* If a program halts, then it is in terminal step. Semantically it is impossible
  for a program to proceed further.
*)
Theorem halted_implies_terminal :
  forall state program, has_halted state program -> terminal state program.
Proof.
  intros state program H_halted.
  destruct H_halted as [out [H_stack [H_halted H_nth]]].
  intros output_state H_step.

  inversion H_step; subst; simpl in *; rewrite H in H_nth; try discriminate H_nth.
  discriminate H_halted.
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
    step {| stack := stack; pc := pc; memory := memory; halted := false |} instructions out_state ->
    interpret instruction {| stack := stack; pc := pc; memory := memory; halted := false |} = Ok out_state.
Proof.
  intros instructions instruction stack pc memory out_state.
  intros nth_ok step_ok.
  
  inversion step_ok.
  - solve_complete nth_ok H4.
  - solve_complete nth_ok H4.
  - subst.
    rewrite nth_ok in H2.
    injection H2 as H2.
    subst.
    simpl.
    rewrite H6.
    reflexivity.
  - subst.
    rewrite nth_ok in H4.
    injection H4 as H4.
    subst.
    simpl.
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
  forall instructions instruction stack pc memory output_state,
    nth_error instructions pc = Some instruction ->
    interpret instruction {|
      stack := stack;
      pc := pc;
      memory := memory;
      halted := false
    |} = Ok output_state ->
    step {| stack := stack; pc := pc; memory := memory; halted := false |} instructions output_state.
Proof.
  intros instructions instruction stack pc memory output_state.
  intros nth_ok interpret_ok.

  destruct instruction.
  - simpl in *.
    injection interpret_ok as H_instr_eq.
    rewrite <- H_instr_eq.
    apply SIPush.
    exact nth_ok.
 - simpl in *.
    destruct stack as [| offset others].
    discriminate interpret_ok.
    destruct others as [| value s'].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIMstore.
    exact nth_ok.
    reflexivity.
  - simpl in *.
    destruct stack as [| offset others].
    discriminate interpret_ok.

    destruct NatMap.find as [prev_found' |] eqn:found.
    + injection interpret_ok as H_instr_eq.
      subst.
      (* For some reason, unless you explicitly pass offset := offset
      Coq can't find variable offset
      *)
      apply SIMload with (offset := offset).
      * exact nth_ok.
      * reflexivity.
      * exact found.
    + discriminate interpret_ok.
 - simpl in *.
    destruct stack as [| a others].
    discriminate interpret_ok.
    destruct others as [| b s'].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIAdd.
    exact nth_ok.
    reflexivity.
  - simpl in *.
    destruct stack as [| output_value rest].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIOutput with (rest := rest).
    exact nth_ok.
    reflexivity.
   - simpl in *.
    destruct stack as [| a others].
    discriminate interpret_ok.
    destruct others as [| b s'].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIEq.
    exact nth_ok.
    reflexivity.
 - simpl in *.
    destruct stack as [| jump_ineq others].
    discriminate interpret_ok.
    destruct others as [| address s'].
    discriminate interpret_ok.

    destruct (Nat.eqb jump_ineq 1) eqn:do_jump.
      + inversion interpret_ok as [H_eq_vm].
        subst.
        apply SIJmpiTrue.
        * exact nth_ok.
        * apply Nat.eqb_eq in do_jump.
          rewrite <- do_jump.
          reflexivity.
      + inversion interpret_ok as [H_eq_vm].
        subst.
        apply Nat.eqb_neq in do_jump.
        apply SIJmpiFalse with (should_jump := jump_ineq) (address := address).
        * exact nth_ok.
        * reflexivity.
        * exact do_jump.
  - simpl in *.
    destruct stack as [| a rest].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIDup.
    exact nth_ok.
    reflexivity.
  - simpl in *.
    destruct stack as [| a rest].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SIPop with (a := a).
    exact nth_ok.
    reflexivity.
  - simpl in *.
    destruct stack as [| a others].
    discriminate interpret_ok.
    destruct others as [| b s'].
    discriminate interpret_ok.

    inversion interpret_ok as [H_eq_vm].
    apply SISwap.
    exact nth_ok.
    reflexivity.
Qed.

Theorem interpret_correct:
  forall instructions instruction stack pc memory out_state,
    nth_error instructions pc = Some instruction ->
    step {| stack := stack; pc := pc; memory := memory; halted := false |} instructions out_state <->
    interpret instruction {| stack := stack; pc := pc; memory := memory; halted := false |} = Ok out_state.
Proof.
  intros.
  split.
  - apply interpret_complete.
    exact H.
  - apply interpret_sound.
    exact H.
Qed.

(* isr = Inversion; Subst; Reflexivity  *)
Ltac isr H := inversion H; subst; reflexivity.

Theorem interpret_sets_halted_false :
  forall instruction state output_state,
    instruction <> IOutput ->
    interpret instruction state = Ok output_state ->
    output_state.(halted) = false.
Proof.
  intros instruction state output_state H_not_ioutput H_interp_ok.
  destruct instruction; simpl in H_interp_ok.

  - isr H_interp_ok.

  - destruct (state.(stack)) as [| offset [| value s']].
    + discriminate.
    + discriminate.
    + isr H_interp_ok.

  - destruct state.(stack) as [| offset s'].
    + discriminate.
    + destruct (NatMap.find offset state.(memory)).
      * isr H_interp_ok.
      * discriminate.

  - destruct (state.(stack)) as [| a [| b s']].
    + discriminate.
    + isr H_interp_ok.
    + isr H_interp_ok.

  - exfalso.
    apply H_not_ioutput.
    reflexivity.

  - destruct state.(stack) as [| a [| b s']].
    + discriminate.
    + discriminate.
    + isr H_interp_ok.

  - destruct state.(stack) as [| sj [| addr s']].
    + discriminate.
    + discriminate.
    + destruct (Nat.eqb sj 1).
      * isr H_interp_ok.
      * isr H_interp_ok.

  - destruct state.(stack) as [| a s'].
    + discriminate.
    + isr H_interp_ok.

  - destruct state.(stack) as [| a s'].
    + discriminate.
    + isr H_interp_ok.

  - destruct state.(stack) as [| a [| b s']].
    + discriminate.
    + discriminate.
    + isr H_interp_ok.
Qed.

(* ia_sic = Interpret_All_Sound_Instruction_Case *)
Ltac ia_sic
  instr instructions IH interpret_ok nth_err initial_state output_state H_halted :=
  (* sso = single step output state *)
  (* dro = destruct result output *)
  destruct (interpret instr initial_state) as [sso_state|] eqn:dro_eq;
  [ apply (@steps_transitive initial_state sso_state output_state instructions);
    [ destruct initial_state as [stack pc memory halted];
      simpl in H_halted;
      subst halted;
      (* forall instructions instruction stack pc memory output_state *)
      apply (@interpret_sound instructions instr stack pc memory sso_state);
      [ exact nth_err | exact dro_eq ]
    | apply IH; exact interpret_ok ]
  | discriminate interpret_ok ].

Theorem interpret_all_sound:
  forall fuel instructions output_state,
    interpret_all' instructions
    {| stack := []; pc := 0; memory := NatMap.empty nat; halted := false |} fuel = Ok output_state ->
      steps {| stack := []; pc := 0; memory := NatMap.empty nat; halted := false |} instructions output_state.
Proof.
  intros fuel.
  (*
    don't need: remember {| stack := []; pc := 0; memory := NatMap.empty nat |}
    as initial_state_val eqn:initial_state_eq.

    Initial state has to be generalized otherwise it's impossible to apply the IH later on.
  *)
  generalize {| stack := []; pc := 0; memory := NatMap.empty nat; halted := false |} as initial_state.
  induction fuel as [|fuel IH_fuel].
  - intros initial_state instructions output_state interpret_ok.
    simpl in interpret_ok.
    discriminate interpret_ok.
  - intros initial_state instructions output_state interpret_ok.
    simpl in interpret_ok.
    destruct (initial_state.(halted)) eqn:H_halted.
    + injection interpret_ok as H_eq.
      subst output_state.
      apply steps_reflexive.
    + destruct (nth_error instructions (pc initial_state)) as [instr|] eqn:nth_err.
      * destruct instr.
        ** ia_sic (IPush n) instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IMstore instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IMload instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IAdd instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** (* Needed because IOutput is separately matched in interpret_all, which makes the proof a little different *)
          destruct initial_state as [stack pc memory halted].
          --- destruct stack as [|a others] eqn:stack_destruct.
            ++ subst.
               simpl in interpret_ok.
               discriminate interpret_ok.
            ++ subst.
               simpl in interpret_ok, nth_err, H_halted.
               subst halted.
               injection interpret_ok as H_output_state_eq.
               subst.
               apply steps_transitive with (state2 := {| stack := [a]; pc := pc; memory := memory; halted := true |}).
               *** apply interpret_sound with (IOutput).
                  -- exact nth_err.
                  -- simpl.
                      reflexivity.
               *** apply steps_reflexive.
        ** ia_sic IEq instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IJmpi instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IDup instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic IPop instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
        ** ia_sic ISwap instructions IH_fuel interpret_ok nth_err initial_state output_state H_halted.
      * discriminate interpret_ok.
Qed.

Lemma step_means_not_halted:
  forall state output_state program,
    step state program output_state -> state.(halted) = false.
Proof.
  intros.
  inversion H; reflexivity.
Qed.

Lemma halted_execution_keeps_state_same:
  forall state output_state program,
    state.(halted) = true ->
    steps state program output_state ->
    output_state = state.
Proof.
  intros state output_state program H_halt H_steps.
  inversion H_steps; subst.
  - reflexivity.
  - exfalso.
    pose proof (step_means_not_halted state state2 program H).
    rewrite H1 in H_halt.
    discriminate H_halt.
Qed.

Lemma halted_interpret_ok:
  forall program state fuel,
    state.(halted) = true ->
    interpret_all' program state (S fuel) = Ok state.
Proof.
  intros program state fuel H_halt.
  simpl.
  rewrite H_halt.
  reflexivity.
Qed.

(* rsse = Rewrite H1; Simpl; Subst; Exact H2 *)
Ltac rsse H1 H2 := rewrite H1; simpl; subst; exact H2.

(*
  This proof took a much longer time to complete, particularly because I realized
  late that it's harder to prove IOutput case without assigning a halted state
  to the VmState. The key idea for the IOutput case is that if a state
  has halted, then semantically output state must be equal to state.
*)
Theorem interpret_all_complete :
  forall instructions final_state,
    steps {| stack := []; pc := 0 ; memory := NatMap.empty nat; halted := false |} instructions final_state ->
    has_halted final_state instructions ->
    exists fuel,
      interpret_all' instructions
      {| stack := []; pc := 0 ; memory := NatMap.empty nat; halted := false |} fuel = Ok final_state.
Proof.
  intros instructions final_state steps_ok halts_instrs.

  induction steps_ok as [| s1 s2 s3 instrs IH].
  - destruct halts_instrs as [out [H1 [H2 H3]]].
    exists 1.
    apply halted_interpret_ok.
    exact H2.
  - pose proof (IHsteps_ok halts_instrs) as H_fuel.
    
    destruct H_fuel as [fuel_witness H_fuel_eq].
    exists (S fuel_witness).
    
    simpl.
    destruct s1 as [stack1 pc1 memory1].
    inversion IH; subst; simpl.
    + rsse H5 H_fuel_eq.
    + rsse H5 H_fuel_eq.
    + rewrite H5.
      simpl.
      subst.
      rewrite H7.
      exact H_fuel_eq.
    + rsse H5 H_fuel_eq.
    + rewrite H5.
      remember {| stack := [a] ; pc := pc1; memory := memory1; halted := true |} as s2 eqn:H_eq_s2.
      
      assert (s3 = s2).
      apply halted_execution_keeps_state_same with (program := instrs).
      * rewrite H_eq_s2.
        reflexivity.
      * exact steps_ok.
      * rewrite -> H. reflexivity. 
    + rsse H5 H_fuel_eq.
    + rsse H5 H_fuel_eq.
    + rewrite -> H5.
      simpl.
      subst.
      apply Nat.eqb_neq in H7.
      rewrite H7.
      exact H_fuel_eq.
    + rsse H5 H_fuel_eq.
    + rsse H5 H_fuel_eq.
    + rsse H5 H_fuel_eq.
Qed.
