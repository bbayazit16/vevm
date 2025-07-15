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
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := n :: stack; pc := pc + 1; memory := memory |}

    | SIAdd : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some IAdd ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := (a + b) :: stack'; pc := pc + 1; memory := memory |}

    | SIMstore : forall stack pc memory instructions offset value stack',
        List.nth_error instructions pc = Some IMstore ->
        stack = offset :: value :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := NatMap.add offset value memory |}

    | SIMload : forall stack pc memory instructions offset stack' found,
        List.nth_error instructions pc = Some IMload ->
        stack = offset :: stack' ->
        NatMap.find offset memory = Some found ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := found :: stack'; pc := pc + 1; memory := memory |}

    | SIOutput : forall stack pc memory instructions a rest,
        List.nth_error instructions pc = Some IOutput ->
        stack = a :: rest ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := [a]; pc := pc + 1; memory := memory |}

    | SIEq : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some IEq ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := (if Nat.eqb a b then 1 else 0) :: stack'; pc := pc + 1; memory := memory |}

    | SIJmpiTrue : forall stack pc memory instructions address stack',
        List.nth_error instructions pc = Some IJmpi ->
        stack = 1 :: address :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := stack'; pc := address; memory := memory |}

    | SIJmpiFalse : forall stack pc memory instructions should_jump address stack',
        List.nth_error instructions pc = Some IJmpi ->
        stack = should_jump :: address :: stack' ->
        should_jump <> 1 ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := memory |}

    | SIDup : forall stack pc memory instructions a stack',
        List.nth_error instructions pc = Some IDup ->
        stack = a :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := a :: a :: stack'; pc := pc + 1; memory := memory |}

    | SIPop : forall stack pc memory instructions a stack',
        List.nth_error instructions pc = Some IPop ->
        stack = a :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := stack'; pc := pc + 1; memory := memory |}

    | SISwap : forall stack pc memory instructions a b stack',
        List.nth_error instructions pc = Some ISwap ->
        stack = a :: b :: stack' ->
        step
            {| stack := stack; pc := pc; memory := memory |}
            instructions
            {| stack := b :: a :: stack'; pc := pc + 1; memory := memory |}
.
