Set Implicit Arguments.

Require Import Arith.
Require Import List Ensembles.
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
Definition lang := Ensemble word.

Variable w : word.
Variable wb we : word.
Variable l : lang.

Definition langEps : lang := Singleton _ nil.
Definition lang0 : lang := Empty_set _.
Definition langAtom (a : A) := Singleton _ [a].

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

(* star lang0 = lang0 *)
Lemma epsilonExists: star langEps = langEps.
  apply Extensionality_Ensembles.
  split.
  intros v H.
  induction H.
  reflexivity.
  inversion_clear H.
  inversion_clear IHstar.
  reflexivity.
  intros v H.
  inversion_clear H.
  apply NilI.
Qed.

Lemma epsilonAlt: star lang0 = langEps.
  apply Extensionality_Ensembles.
  split.
  induction 1.
  reflexivity.
  exfalso.
  inversion_clear H.
  intros v H.
  inversion_clear H.
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

Inductive conc (l1 l2 : lang): lang :=
  | In_conc : forall wb we, l1 wb -> l2 we -> conc l1 l2 (wb ++ we).

Fixpoint L (r : rexp A): lang :=
  match r with
  | Empty _ => lang0
  | Atom a => langAtom a
  | Alt r1 r2 => Union _ (L r1) (L r2)
  | Conc r1 r2 => conc (L r1) (L r2)
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