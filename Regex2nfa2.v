Set Implicit Arguments.

Add Rec LoadPath "." as Top.

Require Import Regex Automata2.
Require Import List ListSet Bool Arith.
Import ListNotations.

Definition bool_list_dec : forall x y: list bool, {x = y} + {x <> y} := list_eq_dec bool_dec.

Section Nae.

Variable A St: Type.
Variable Seq_dec: forall x y:St, {x = y} + {x <> y}.

Definition word := list A.

Definition nae := nfa (option A) St.

(*Non recurisif sur un argument, on  ajoute donc un entier qui sera 2 fois la taille de la liste,
  on considère qu'il y a une altérnence entre transition None et transition Some*)
Fixpoint accepts_eps_from (nae : nae) (l: nat) s w :=
  match l with
  | 0 => set_mem Seq_dec s (fin nae)
  | S n =>
      let aux l :=
        fun b s =>
          b || accepts_eps_from nae n s l
      in
      if set_fold_left (aux w) (next nae (None) s) false then
        true
      else
        match w with
        | [] => set_mem Seq_dec s (fin nae)
        | h::q => set_fold_left (aux q) (next nae (Some h) s) false
        end
  end.

Definition accepts_eps (nae: nae) w := accepts_eps_from nae (length w * 2)(start nae) w.

(*
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
*)
End Nae.

Section BitsNAe.

Variable A : Type.
Variable Aeq_dec : forall x y:A, {x = y} + {x <> y}.


Definition bitsNAe := nae A (list bool).

Fixpoint atom_next (a: A) oa lb: set (list bool) :=
  match lb with
  | [true] =>
    match oa with
    | Some x =>
      if Aeq_dec x a then [[false]] else []
    | _ => []
    end
  | _ => []
  end.

Definition atom (a: A): bitsNAe :=
  mkNfa
    ([true])
    (atom_next a)
    ([[false]]).

Definition prepend_list_set (b: bool) (ens: set (list bool)) :=
  set_map bool_list_dec (fun l => b::l) ens.

(*Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  | nextL : forall a q s, In _ (next nae1 a s) q -> alt_next nae1 nae2 a (true::q) s
  | nextR : forall a q s, In _ (next nae2 a s) q -> alt_next nae1 nae2 a (false::q) s.

Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  | nextNL : alt_next nae1 nae2 None [] (true::start nae1)
  | nextNR : alt_next nae1 nae2 None [] (false::start nae2)
  | nextL : forall a q s, In _ (next nae1 a q) s -> alt_next nae1 nae2 a (true::q) (true::s)
  | nextR : forall a q s, In _ (next nae2 a q) s -> alt_next nae1 nae2 a (false::q) (true::s).

Inductive alt_fin (nae1 nae2: bitsNAe): Ensemble (list bool) :=
  | finL : forall s, In _ (fin nae1) s -> alt_fin nae1 nae2 (true::s)
  | finR : forall s, In _ (fin nae1) s -> alt_fin nae1 nae2 (false::s).*)

Fixpoint alt_next (nae1 nae2: bitsNAe) oa lb: set (list bool) :=
  match oa with
  | None =>
      match lb with
      | [] => [true::start nae1; false::start nae2]
      | _ => []
      end
  | Some x =>
      match lb with
      | true::q => prepend_list_set true (next nae1 oa q)
      | false::q => prepend_list_set false (next nae2 oa q)
      | _ => []
      end
  end.

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
    (set_union bool_list_dec (prepend_list_set true fin1) (prepend_list_set false fin2)).

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
Definition nfae1 := atom eq_nat_dec 1.

Lemma acc_nfae1 : accepts_eps bool_list_dec nfae1 [1] = true.
  auto.
Qed.

Definition nfae2 := alt (atom eq_nat_dec 1) (atom eq_nat_dec 2).

Goal accepts_eps bool_list_dec nfae2 [1] = true.
Proof.
  auto.
Qed.

Goal forall (A : Type) (nae1 nae2 : bitsNAe A) w,
  accepts_eps bool_list_dec nae1 w = true -> accepts_eps bool_list_dec (alt nae1 nae2) w = true.
Proof.
  intros A nae1 nae2 w.
  intros H.
  induction w.
  compute.
Qed.

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

(*Bon ça prouve le goal suivant mais ça à l'air faux quand meme hein*)
Lemma rtrancl_imp_step :
  forall (na : bitsNAe A) (a : option A) (p q : list bool),
    rtrancl (step na a) (p, q) -> step na a (p, q).
Admitted.

Goal forall nae1 nae2: bitsNAe A, accepts_eps nae1 [] -> accepts_eps (alt nae1 nae2) [].
intros nae1 nae2 H.
induction H.
destruct H as (H, H').
unfold accepts_eps.
exists (true::x).
split.
apply finL.
assumption.
simpl.
Print In_steps_nil.
apply In_steps_nil.
unfold eps.
inversion_clear H'.
Print rtrancl.
apply rtrancl_trans with (b := true::start nae1).
apply rtrancl_base.
apply In_step.
simpl.
apply nextNL.
apply rtrancl_base.
apply In_step.
Print nextL.
simpl.
apply nextL.
induction H0.
Admitted.

Goal forall (nae1 nae2 : bitsNAe A),
  next (alt nae1 nae2) None [] (true::start nae1).
Proof.
  intros nae1 nae2.
  apply nextNL.
Qed.

Goal forall h q (nae1 nae2: bitsNAe A), ((accepts_eps nae1 q) -> accepts_eps (alt nae1 nae2) q) -> accepts_eps nae1 (h::q) -> accepts_eps (alt nae1 nae2) (h::q).
Proof.
  intros h q nae1 nae2 IH H.
  induction H.
  destruct H as (H, H').
  exists (true::x).
  split.
  * apply finL.
  assumption.
  * simpl.
  inversion_clear H'.
  apply In_steps_cons with (sb := true::sb) (sc := true::sc).
  apply rtrancl_trans with (true::start nae1).
  apply rtrancl_base.
  apply In_step.
  apply nextNL.
  apply rtrancl_base.
  apply In_step.
  apply nextL.
  
Qed.

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
  induction H0.
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