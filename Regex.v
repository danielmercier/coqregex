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
  | In_star_nil : star L nil
  | In_star_cons : forall wb we : list A, L wb -> star L we -> star L (wb ++ we).

Lemma NilI: star l nil.
  apply In_star_nil.
Qed.

Lemma LConsI: l wb -> star l we -> star l (wb ++ we).
  apply In_star_cons.
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
  apply In_star_nil.
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
  apply In_star_nil.
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

Lemma alt_commute : forall r1 r2, L (Alt r1 r2) = L (Alt r2 r1).
Proof.
  intros r1 r2.
  simpl.
  apply Extensionality_Ensembles.
  split; intros v H.
  inversion_clear H; [right | left]; assumption.
  inversion_clear H; [right | left]; assumption.
Qed.

Lemma mt_seq : L (Conc (Empty _) (Empty _)) = lang0.
Proof.
  simpl.
  apply Extensionality_Ensembles.
  split; intros v H.
  *inversion_clear H.
  inversion_clear H0.
  *inversion_clear H.
Qed.

Lemma eps : L (Star (Empty _)) = langEps.
Proof.
  simpl.
  apply Extensionality_Ensembles.
  split; intros v H.
  *inversion_clear H.
    +apply In_singleton.
    +inversion_clear H0.
  *inversion_clear H.
  apply In_star_nil.
Qed.

End Semantic.

Section Test.

Definition regexA := Conc (Atom 1) (Atom 2).
Definition LA := L regexA.

Goal LA [1; 2].
  unfold LA.
  simpl.
  apply In_conc with (wb := [1]) (we := [2]); apply In_singleton.
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
  apply In_conc with (wb := [1]) (we := [2]); reflexivity.
Qed.

End Test.