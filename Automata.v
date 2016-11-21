Set Implicit Arguments.

Require Import List Logic Basics FunctionalExtensionality ClassicalFacts Ensembles.
Require Import ListSet Decidable.
Import ListNotations.

Section Nfa.

Variable A S: Type.

(*Un automate est un triplet, avec :
  - un  état initial
  - une fonction de transition qui,
    à partir d'un état et une action, donne un ensemble d'états.
  - un ensemble d'états finaux
*)
Record nfa := mkNfa {
  start : S;
  next : A -> S -> Ensemble S;
  fin : Ensemble S
}.

(*Composition de deux ensemble de deux éléments*)
Inductive compose (ens1 ens2 : Ensemble (S * S)) : Ensemble (S * S) :=
  (*si a, b appartient a ens1 et b, c a ens2 alors on appartient a la composé des deux*)
  | In_compose : forall a b c, ens1 (a, b) -> ens2 (b, c) -> compose ens1 ens2 (a, c).

(*Les couples (p, q) après avoir lu a*)
Inductive step nfa a : Ensemble (S * S) :=
  | In_step : forall p q, In _ (next nfa a p) q -> step nfa a (p, q).

(*Les couples (p, q) après avoir lu le mot list A*)
Inductive steps nfa : list A -> Ensemble (S * S) :=
  (*nil les états sont les états courants*)
  | In_steps_nil : forall s, steps nfa [] (s, s)
  (*cons, les états sont la composition de la tete avec le steps de la suite*)
  | In_steps_cons : forall h q sa sc, compose (step nfa h) (steps nfa q) (sa, sc) -> steps nfa (h::q) (sa, sc).

Definition accepts (nfa: nfa) (w: list A) :=
  exists k: S, In _ (fin nfa) k /\ In _ (steps nfa w) (start nfa, k).

Lemma simpl_step_cons : forall nfa h q, steps nfa (h::q) = compose (step nfa h) (steps nfa q).
Proof.
  intros nfa h q.
  apply Extensionality_Ensembles.
  split.
  *intros (x, y) H.
  inversion_clear H.
  assumption.
  *intros (x, y) H.
  apply In_steps_cons.
  assumption.
Qed.

Lemma compose_assoc :
  forall ens1 ens2 ens3, compose (compose ens1 ens2) ens3 = compose ens1 (compose ens2 ens3).
Proof.
  intros ens1 ens2 ens3.
  apply Extensionality_Ensembles.
  split; intros (x, y) H.
  *inversion_clear H.
  inversion_clear H0.
  apply In_compose with b0.
  assumption.
  apply In_compose with b.
  assumption.
  assumption.
  *inversion_clear H.
  inversion_clear H1.
  apply In_compose with b0.
  apply In_compose with b.
  assumption.
  assumption.
  assumption.
Qed.  

Lemma steps_append : forall nfa v w, steps nfa (v ++ w) = compose (steps nfa v) (steps nfa w).
Proof.
  intros nfa v w.
  induction v; apply Extensionality_Ensembles.
  *split.
    +simpl.
    intros (x, y) H.
    apply In_compose with x.
    apply In_steps_nil.
    assumption.
    +simpl.
    intros (x, y) H.
    inversion_clear H.
    (assert (b = x)).
    inversion_clear H0.
    trivial.
    rewrite H in H1.
    assumption.
  *split.
    +simpl.
    intros (x, y) H.
    rewrite simpl_step_cons.
    rewrite simpl_step_cons in H.
    rewrite IHv in H.
    rewrite compose_assoc.
    assumption.
    +simpl.
    intros (x, y) H.
    rewrite simpl_step_cons.
    rewrite simpl_step_cons in H.
    rewrite IHv.
    rewrite <- compose_assoc.
    assumption.
Qed.

Lemma in_steps_append : forall nfa v w x y, steps nfa (v ++ w) (x, y) = compose (steps nfa v) (steps nfa w) (x, y).
Proof.
  intros nfa v w x y.
  rewrite steps_append.
  reflexivity.
Qed.

Lemma accepts_conv_steps :
  forall nfa w, accepts nfa w <-> exists q, steps nfa w (start nfa, q) /\ fin nfa q.
Proof.
  intros nfa w.
  unfold accepts.
  split.
  *intro H.
  destruct H.
  exists x.
  split; destruct H; assumption.
  *intro H.
  destruct H.
  exists x.
  split; destruct H; assumption.
Qed.

End Nfa.

Section Test.

Inductive next1 : nat -> nat -> Ensemble nat :=
  | next001 : next1 0 0 1
  | next111 : next1 1 1 1.

Definition nfa1 :=
  mkNfa
    (0)
    next1
    (Singleton nat 1).

Goal accepts nfa1 [0].
  unfold accepts.
  exists 1.
  split.
  apply In_singleton.
  unfold In.
  apply In_steps_cons.
  apply In_compose with 1.
  apply In_step.
  simpl.
  apply next001.
  apply In_steps_nil.
Qed.

Goal accepts nfa1 [0; 1].
  unfold accepts.
  exists 1.
  split.
  apply In_singleton.
  apply In_steps_cons.
  apply In_compose with 1.
  apply In_step.
  apply next001.
  apply In_steps_cons.
  apply In_compose with 1.
  apply In_step.
  apply next111.
  apply In_steps_nil.
Qed.

End Test.