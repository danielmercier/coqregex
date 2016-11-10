Set Implicit Arguments.

Add Rec LoadPath "." as Top.

Require Import Regex Automata.
Require Import List Bool Ensembles.
Import ListNotations.

Section Nae.

Variable A S: Type.

Definition word := list A.

Definition nae := nfa (option A) S.

Inductive accepts_eps_from (nae: nae) (s: S) : list A -> Prop :=
  | acc_nil : In _ (fin nae) s -> accepts_eps_from nae s []
  | acc_cons : forall e h q, In _ (next nae (Some h) s) e -> accepts_eps_from nae e q -> accepts_eps_from nae s (h::q)
  | acc_none : forall e w, In _ (next nae None s) e -> accepts_eps_from nae e w -> accepts_eps_from nae s w.

Definition accepts_eps nae : list A -> Prop := accepts_eps_from nae (start nae).

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

Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  | nextL : forall a q s, In _ (next nae1 a s) q -> alt_next nae1 nae2 a (true::q) s
  | nextR : forall a q s, In _ (next nae2 a s) q -> alt_next nae1 nae2 a (false::q) s.

Inductive alt_fin (nae1 nae2: bitsNAe): Ensemble (list bool) :=
  | finL : forall s, In _ (fin nae1 s) -> alt_fin nae1 nae2 (true::s)
  | finR : forall s, In _ (fin nae1 s) -> alt_fin nae1 nae2 (false::s)

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
    (fun r =>
      match r with
      | [] => False
      | true::q => fin1 q 
      | false::q => fin2 q
      end).

Definition conc (nae1: bitsNAe) (nae2: bitsNAe): bitsNAe :=
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

Goal accepts_eps nfae1 [1].
  apply acc_cons with (e := [false]).
  compute.
  apply nextA.
  apply acc_nil.
  compute.
  apply In_singleton.
Qed.

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