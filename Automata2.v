Set Implicit Arguments.

Require Import List Logic Basics FunctionalExtensionality ClassicalFacts Ensembles.
Require Import ListSet Bool Peano_dec.
Import ListNotations.


(* Blocage avec ListSet, utilisation d'un autre type de set
     - blocage sur step (comment faire le forall sur les couples states)
Section PropSet.
Variables A B C: Type.
Definition set (A: Type) := A -> Prop.
Definition singleton (x: A) := fun y => x = y.
Definition set_map (f: A -> B) (s: set A) : set B :=
  fun b => exists a, s a /\ f a = b.
Definition sets_union (s: set (set A)): set A :=
  fun a => exists sub_set, s sub_set /\ sub_set a.
Definition set_union (s1 s2 : set A) :=
  fun x => s1 x \/ s2 x.
Definition composition (r: set (A * B)) (s: set (B * C)): set (A * C) :=
  (fun elem =>
      let (a, c) := elem in
      exists b, r (a, b) /\ s (b, c)).
End PropSet.

Definition prepend_list_set (A: Type) (a: A) (s: set (list A)) : set (list A) :=
  fun r =>
    match r with
    | [] => False
    | b::rq => a = b /\ s rq
    end.*)

Section Nfa.

Variable A S: Type.
Variable Seq_dec: forall x y:S, {x = y} + {x <> y}.

(*Un automate est un triplet, avec :
  - un  état initial
  - une fonction de transition qui,
    à partir d'un état et une action, donne un ensemble d'états.
  - un ensemble d'états finaux
*)
Record nfa := mkNfa {
  start : S;
  next : A -> S -> set S;
  fin : set S
}.

Fixpoint accepts_from nfa s w :=
  match w with
  | [] => set_mem Seq_dec s (fin nfa)
  | h::q =>
      let aux :=
        fun b s =>
          b || accepts_from nfa s q
      in
      set_fold_left aux (next nfa h s) false
  end.

Definition accepts nfa w := accepts_from nfa (start nfa) w.

(*(*Inductive accepts_from (nfa: nfa) (s: S) : list A -> Prop :=
| accepts_nil : In _ (fin nfa) s -> accepts_from nfa s []
| accepts_cons : forall e h q, In _ (next nfa h s) e -> accepts_from nfa e q -> accepts_from nfa s (h::q).

Definition accepts (nfa: nfa) : list A -> Prop := accepts_from nfa (start nfa).

Fixpoint nfa_accepts (nfa: nfa) (w: list A) (s: S): Prop :=
  match w with
  | [] => fin nfa s
  | a::wq => exists y, (next nfa a s y) /\ nfa_accepts nfa wq y
  end.*)

(*Les couples (p, q)*)
Inductive step nfa a : Ensemble (S * S) :=
  | In_step : forall p q, In _ (next nfa a p) q -> step nfa a (p, q).
Hint Resolve step.

Inductive steps nfa : list A -> Ensemble (S * S) :=
  | In_steps_nil : forall s, steps nfa [] (s, s)
  | In_steps_cons : forall h q sa sb sc, step nfa h (sa, sb) -> steps nfa q (sb, sc) -> steps nfa (h::q) (sa, sc).

Definition accepts (nfa: nfa) (w: list A) :=
  exists k: S, In _ (fin nfa) k /\ In _ (steps nfa w) (start nfa, k).

(*Fixpoint delta (nfa: nfa) (w: list A) (s: S): set S :=
  match w with
  | nil => Singleton s
  | h::q => sets_union (set_map (delta nfa q) (next nfa h s))
  end.*)

(*Definition accepts (nfa: nfa) (w: list A): Prop :=
  nfa_accepts nfa w (start nfa).*)

(*Tout les couples(p, q) de states S qui ont une transition a
Definition step (nfa: nfa) (a: A): set (S * S) :=
  fun c => 
    let (p, q) := c in
    next nfa a p q.

(*Tout les couples(p, q) de states S*)
Fixpoint steps (nfa: nfa) (w: list A): set (S * S) :=
  match w with
  | nil => 
    (fun c =>
      let (p, q) := c in
      p = q)
  | h::wq =>
    composition (step nfa h) (steps nfa wq)
  end.

Variable v w: list A.

Lemma set_eqI: forall s r : set (S * S),
  s = r <-> forall x, s x <-> r x.

  split.
  intro.
Admitted.

Lemma assoc_composition :
  forall s r t : set (S * S), composition (composition s r) t = composition s (composition r t).

  intros.
  unfold composition.
Admitted.

Lemma steps_append : forall r, steps r (v ++ w) = composition (steps r v) (steps r w).
Proof.
  induction v.
  intro r.
  apply set_eqI.
  intro x.
  destruct x as (a, b).
  simpl.
  split.
  intro.
  exists a.
  tauto.
  intro.
  destruct H.
  destruct H.
  rewrite H.
  assumption.
  simpl ((a :: l) ++ w).
  intro r.
  simpl (steps r (a :: l)).
  simpl (steps r (a :: l ++ w)).
  rewrite assoc_composition.
  rewrite IHl.
  reflexivity.
Qed.

Lemma in_steps_append :
    forall p q r,
    steps r (v ++ w) (p, q) <-> composition (steps r v) (steps r w) (p, q).

  intros p q r.
  apply set_eqI.
  rewrite steps_append.
  reflexivity.
Qed.

Lemma delta_conv_steps : forall r p,
  delta r w p = (fun q => steps r w (p, q)).
Admitted.

End Nfa.

Section Test.

Axiom H : prop_extensionality.

Goal composition (singleton (1, 2)) (singleton (2, 3)) = singleton (1, 3).
  apply functional_extensionality.
  intro x.
  destruct x as (a, b).
  apply H.
  compute.
  split.
  intro.
  destruct H0.
  destruct H0.

Admitted.

Goal *)*)
End Nfa.

Section Test.

Definition next1 (a s : nat) : set nat :=
  match a, s with
  | 0, 0 => [1]
  | 1, 1 => [1]
  | _, _ => []
  end.

Definition nfa1 :=
  mkNfa
    (0)
    next1
    ([1]).

Goal accepts eq_nat_dec nfa1 [0] = true.
  auto.
Qed.

Goal accepts eq_nat_dec nfa1 [0; 1] = true.
  auto.
Qed.

End Test.