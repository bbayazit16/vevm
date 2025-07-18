Require Import Vevm.Instruction.
Require Import Vevm.Vm.

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Lia.

Import ListNotations.

Inductive step : VmState -> list Instruction -> VmState -> Prop :=
    | SIPush : forall stack pc memory instructions n,
        List.nth_error instructions pc = Some (IPush n) ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := n :: stack; pc := pc + 1; memory := memory; halted := false |}

    | SIMstore : forall stack pc memory instructions offset value stack',
        List.nth_error instructions pc = Some IMstore ->
        stack = offset :: value :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := NatMap.add offset value memory; halted := false |}

    | SIMload : forall stack pc memory instructions offset stack' found,
        List.nth_error instructions pc = Some IMload ->
        stack = offset :: stack' ->
        NatMap.find offset memory = Some found ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := found :: stack'; pc := pc + 1; memory := memory; halted := false |}

    | SIAdd : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some IAdd ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := (a + b) :: stack'; pc := pc + 1; memory := memory; halted := false |}

    | SIOutput : forall stack pc memory instructions a rest,
        List.nth_error instructions pc = Some IOutput ->
        stack = a :: rest ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := [a]; pc := pc; memory := memory; halted := true |}

    | SIEq : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some IEq ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := (if Nat.eqb a b then 1 else 0) :: stack'; pc := pc + 1; memory := memory; halted := false |}

    | SIJmpiTrue : forall stack pc memory instructions address stack',
        List.nth_error instructions pc = Some IJmpi ->
        stack = 1 :: address :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := stack'; pc := address; memory := memory; halted := false |}

    (* ONLY if should_jump != 1; not just 0, although 0 is probably
    the most common way to do this. I included this because simplify
    specifying == 0 makes things more complicated from a well-defined
    program perspective.
    *)
    | SIJmpiFalse : forall stack pc memory instructions should_jump address stack',
        List.nth_error instructions pc = Some IJmpi ->
        stack = should_jump :: address :: stack' ->
        should_jump <> 1 ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := memory; halted := false |}

    | SIDup : forall stack pc memory instructions a stack',
        List.nth_error instructions pc = Some IDup ->
        stack = a :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := a :: a :: stack'; pc := pc + 1; memory := memory; halted := false |}

    | SIPop : forall stack pc memory instructions a stack',
        List.nth_error instructions pc = Some IPop ->
        stack = a :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := memory; halted := false |}

    | SISwap : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some ISwap ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory; halted := false |}
            instructions
            {| stack := b :: a :: stack'; pc := pc + 1; memory := memory; halted := false |}
.

Inductive steps : VmState -> list Instruction -> VmState -> Prop :=
  | steps_reflexive : forall state instrs,
      steps state instrs state
    (* 
        Take one step with step state1 instrs, obtaining state2.
        Thus there's at least one step taken from there.

        After obtaining state2, take arbitrary number of steps,
        including possibly 0, and reach state3. There you get state3,
        and thus => steps state1 instrs state3.
    *)
  | steps_transitive : forall state1 state2 state3 instrs,
      step state1 instrs state2 ->
      steps state2 instrs state3 ->
      steps state1 instrs state3.
