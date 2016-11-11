Set Implicit Arguments.

Add Rec LoadPath "." as Top.

Require Import Regex Automata.
Require Import List Bool Ensembles.
Import ListNotations.

Section Nae.

Variable A S: Type.

Definition word := list A.

Definition nae := nfa (option A) S.

Definition eps (nae : nae) := step nae None.

(*Cloture reflexive transitive*)
Inductive rtrancl (T: Type) (ens : Ensemble (T * T)) : Ensemble (T * T) :=
  | rtrancl_refl : forall s, rtrancl ens (s, s)
  | rtrancl_intro_rtrancl : forall a b c, rtrancl ens (a, b) -> In _ ens (b, c) -> rtrancl ens (a, c).

(*On utilise steps car mieux pour raisonner après, blocage avec l'autre version de accepts_eps_from*)
Inductive steps_nae nae : list A -> Ensemble (S * S) :=
  | In_steps_nil : forall p q, rtrancl (eps nae) (p, q) -> steps_nae nae [] (p, q)
  | In_steps_cons :
      forall h q sa sb sc sd,
        rtrancl (eps nae) (sa, sb) ->
        step nae (Some h) (sb, sc) ->
        steps_nae nae q (sc, sd) ->
          steps_nae nae (h::q) (sa, sd).

Inductive accepts_eps_from (nae: nae) (s: S) : list A -> Prop :=
  | acc_nil : In _ (fin nae) s -> accepts_eps_from nae s []
  | acc_cons : forall e h q, In _ (next nae (Some h) s) e -> accepts_eps_from nae e q -> accepts_eps_from nae s (h::q)
  | acc_none : forall e w, In _ (next nae None s) e -> accepts_eps_from nae e w -> accepts_eps_from nae s w.

Definition accepts_eps nae w : Prop :=
  exists k, In _ (fin nae) k /\ In _ (steps_nae nae w) (start nae, k).

End Nae.

Section BitsNAe.

Variable A : Type.

Definition bitsNAe := nae A (list bool).

Definition empty_set := fun r : list bool => False.

Inductive atom_next (a: A) : option A -> list bool -> Ensemble (list bool) :=
  | nextA : atom_next a (Some a) [true] [false].

Definition atom (a: A): bitsNAe :=
  mkNfa
    ([true])
    (atom_next a)
    (Singleton _ [false]).

Inductive prepend_list_set (A: Type) (b: A) (ens: Ensemble (list A)) : Ensemble (list A) :=
  | in_prep : forall q, In _ ens q -> prepend_list_set b ens (b::q).

(*Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  | nextL : forall a q s, In _ (next nae1 a s) q -> alt_next nae1 nae2 a (true::q) s
  | nextR : forall a q s, In _ (next nae2 a s) q -> alt_next nae1 nae2 a (false::q) s.*)

Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  | nextNL : alt_next nae1 nae2 None [] (true::start nae1)
  | nextNR : alt_next nae1 nae2 None [] (false::start nae2)
  | nextL : forall a q s, In _ (next nae1 a q) s -> alt_next nae1 nae2 a (true::q) (true::s)
  | nextR : forall a q s, In _ (next nae2 a q) s -> alt_next nae1 nae2 a (false::q) (true::s).

Inductive alt_fin (nae1 nae2: bitsNAe): Ensemble (list bool) :=
  | finL : forall s, In _ (fin nae1) s -> alt_fin nae1 nae2 (true::s)
  | finR : forall s, In _ (fin nae1) s -> alt_fin nae1 nae2 (false::s).

Definition alt (nae1: bitsNAe) (nae2: bitsNAe): bitsNAe :=
  let start1 := start nae1 in
  let start2 := start nae2 in

  let next1 := next nae1 in
  let next2 := next nae2 in

  let fin1 := fin nae1 in
  let fin2 := fin nae2 in

  mkNfa
    ([])
    (alt_next nae1 nae2)
    (alt_fin nae1 nae2).

(*Definition conc (nae1: bitsNAe) (nae2: bitsNAe): bitsNAe :=
  let start1 := start nae1 in
  let start2 := start nae2 in

  let next1 := next nae1 in
  let next2 := next nae2 in

  let fin1 := fin nae1 in
  let fin2 := fin nae2 in

  mkNfa
    (true::start1)
    (fun t s =>
      match s with
      | [] => empty_set
      | true::q => prepend_list_set true (next1 t q)
      | false::q => prepend_list_set false (next2 t q)
      end)
    (prepend_list_set false fin2).

Fixpoint to_nfae (rexp: rexp A): bitsNAe :=
  match rexp with
  | Empty _ => mkNfa ([]) (fun s t => empty_set) (fun s => s = [])
  | Atom a => atom a
  | Alt r1 r2 => alt (to_nfae r1) (to_nfae r2)
  | Conc r1 r2 => conc (to_nfae r1) (to_nfae r2)
  | Star r => mkNfa ([]) (fun s t => empty_set) (fun s => s = [])
  end.*)

End BitsNAe.

Section Test.

Definition rexp1 := Atom 1.
Definition nfae1 := atom 1.

Lemma acc_nfae1 : accepts_eps nfae1 [1].
  unfold accepts_eps.
  exists ([false]).
  split.
  apply In_singleton.
  unfold In.
  Print steps_nae.
  simpl.
  apply In_steps_cons with (sb := [true]) (sc := [false]).
  apply rtrancl_refl.
  apply In_step.
  compute.
  apply nextA.
  apply In_steps_nil.
  apply rtrancl_refl.
Qed.

Definition nfae2 := alt (atom 1) (atom 2).

Variable A: Type.

Goal forall nae: bitsNAe A, accepts_eps nae [] ->
        exists s: list bool, In _ (fin nae) s -> rtrancl (eps nae) (start nae, s).

  intros nae H.
  unfold accepts_eps in H.
  destruct H.
  destruct H as (H, H').
  exists x.
  intros _.
  inversion H'.
  assumption.
Qed.

Lemma step_imp_next:
  forall (na : bitsNAe A) (a : option A) (p q : list bool),
    In _ (step na a) (p, q) -> In _ (next na a p) q.
Proof.
  intros na a p q H.
  inversion_clear H.
  assumption.
Qed.

(*Bon ça prouve le goal suivant mais ça à l'air faux quand meme*)
Lemma rtrancl_imp_step :
  forall (na : bitsNAe A) (a : option A) (p q : list bool),
    rtrancl (step na a) (p, q) -> step na a (p, q).
Admitted.

Goal forall nae1 nae2: bitsNAe A, accepts_eps nae1 [] -> accepts_eps (alt nae1 nae2) [].
  intros nae1 nae2 H.
  inversion H as (x, H').
  destruct H' as (H', H'').
  inversion_clear H''.
  unfold accepts_eps.
  exists (true::x).
  split; simpl; try apply finL; try assumption.
  apply In_steps_nil.
  apply rtrancl_intro_rtrancl with (b := true::start nae1); try apply rtrancl_refl.
  apply rtrancl_intro_rtrancl with (b := []); try apply rtrancl_refl.
  apply In_step.
  apply nextNL.
  unfold eps.
  apply In_step.
  apply nextL.
  apply step_imp_next.
  apply rtrancl_imp_step.
  assumption.
Qed.

Goal forall (w : list A) (nae1 nae2 : bitsNAe A),
        accepts_eps nae1 w -> accepts_eps (alt nae1 nae2) w.
  intros w nae1 nae2.
  induction 1.
  destruct H as (H, H').
  unfold accepts_eps.
  exists (true::x).
  split.
  *
    simpl.
    apply finL.
    assumption.
  *
  induction w.
  **
    apply In_steps_nil.
    simpl.
    Print rtrancl.
    apply rtrancl_intro_rtrancl with (b := true::start nae1).
    ***
      apply rtrancl_intro_rtrancl with (b := []); try apply rtrancl_refl.
      unfold eps.
      apply In_step.
      simpl.
      unfold In.
      Print alt_next.
      apply nextNL.
    ***
    unfold eps.
    apply In_step.
    simpl.
    Print alt_next.
Qed.

(*Blocage....*)
Goal forall (w : list A) (nae1 nae2 : bitsNAe A),
        accepts_eps nae1 w -> accepts_eps nae2 w -> accepts_eps (alt nae1 nae2) w.

  unfold accepts_eps.
  intros w nae1 nae2 H H'.
  simpl.
  apply acc_none with (e := (false::(start nae2))).
  *
    unfold In.
    simpl.
    apply nextNR.
  *
  Print accepts_eps_from.
  induction w.
  


Goal accepts_eps nfae2 [1].
  Print acc_cons.
  apply acc_none with (e := [true; true]).
  unfold In.
  simpl.
  Print nextNL.
  apply nextNL.
  Print accepts_eps_from.
  apply acc_cons with (e := .

Goal forall x : nat, accepts (to_nfae (Atom x)) [Some x].
  intro x.
  compute.
  exists [false].
  tauto.

Goal accepts nfae1 [Some 1].
Proof.
  compute.
  exists [false].
  tauto.
Qed.

Goal accepts nfae1 = L rexp1.

Definition rexp2 := Conc (Atom 1) (Atom 2).
Definition nfae2 := to_nfae rexp2.

Goal accepts nfae2 [Some 1; Some 3].
Proof.
  unfold accepts.
  simpl.
  unfold prepend_list_set.
  exists [true; false].
  split.
  tauto.
  exists [false; false].
  split; tauto.
Qed.

Definition rexp3 := Alt (Atom 1) (Atom 2).
Definition nfae3 := to_nfae rexp3.

Goal accepts nfae3 [Some ] /\ accepts nfae3 [Some 2].
Proof.
  split; compute.
  *
  exists [true; false].
  split.
  intro.
  discriminate H.
  reflexivity.
Qed.

End Test.