Set Implicit Arguments.

Require Import Arith.
Require Import List.
Import ListNotations.

Inductive rexp (A : Type) :=
  | Empty : rexp A
  | Atom : A -> rexp A
  | Alt : rexp A -> rexp A -> rexp A
  | Conc : rexp A -> rexp A -> rexp A
  | Star : rexp A -> rexp A.

Section Semantic.

Print List.

Variable A : Type.
Definition word := list A.
Definition lang := word -> Prop.

Variable w : word.
Variable wb we : word.
Variable l : lang.

Definition langEps (w : word) := w = nil.
Definition lang0 (w : word) := False.
Definition langAtom (a : A) (w : word) := w = cons a nil.

Inductive star (L : lang) : lang :=
  | NilI : star L nil
  | ConsI : forall wb we : list A, L wb -> star L we -> star L (wb ++ we).

Lemma LNilI: star l nil.
  apply NilI.
Qed.

Lemma LConsI: l wb -> star l we -> star l (wb ++ we).
  apply ConsI.
Qed.

Require Import ListSet.

Lemma set_eqI: forall lang1 lang2 : lang,
  lang1 = lang2 <-> forall x, lang1 x <-> lang2 x.
  split.
  intro.
  rewrite H.
  tauto.
  intro.
Admitted.

(* star lang0 = lang0 *)
Lemma epsilonExists: star langEps = langEps.
  apply set_eqI.
  split.
  induction 1.
  reflexivity.
  rewrite H.
  rewrite IHstar.
  simpl.
  reflexivity.
  intro H.
  rewrite H.
  apply NilI.
Qed.

Lemma epsilonAlt: star lang0 = langEps.
  apply set_eqI.
  split.
  induction 1.
  reflexivity.
  exfalso.
  assumption.
  intro H.
  rewrite H.
  apply NilI.
Qed.

Lemma epsilon': star (star langEps) = langEps.
  repeat rewrite epsilonExists.
  reflexivity.
Qed.

Lemma epsilon'': star (star (star langEps)) = langEps.
  repeat rewrite epsilonExists.
  reflexivity.
Qed.

Fixpoint L (r : rexp A): lang :=
  match r with
  | Empty _ => lang0
  | Atom a => langAtom a
  | Alt r1 r2 => fun w => L r1 w \/ L r2 w
  | Conc r1 r2 => fun w => exists wb we, w = wb ++ we /\ L r1 wb /\ L r2 we
  | Star r1 => star (L r1)
  end.

End Semantic.

Section Test.

Definition regexA := Conc (Atom 1) (Atom 2).
Definition LA := L regexA.

Goal LA [1; 2].
  unfold LA.
  simpl.
  exists [1].
  exists [2].
  split.
  reflexivity.
  split; unfold langAtom; reflexivity.
Qed.

Definition regexB := Alt regexA (Atom 1).
Definition LB := L regexB.

Goal LB [1] /\ LB [1; 2].
  unfold LB.
  simpl.
  split.
  right.
  compute.
  reflexivity.
  left.
  exists [1].
  exists [2].
  split.
  reflexivity.
  split; reflexivity.
Qed.

End Test.