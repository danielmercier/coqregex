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
  (*Réfléxivité*)
  | rtrancl_refl : forall s, rtrancl ens (s, s)
  (*Transitivité*)
  | rtrancl_trans : forall a b c, rtrancl ens (a, b) -> ens (b, c) -> rtrancl ens (a, c).

Lemma rtrancl_base (T: Type) : forall (ens : Ensemble (T * T)) x y, ens (x, y) -> rtrancl ens (x, y).
Proof.
  intros ens x y.
  intro H.
  apply rtrancl_trans with x.
  apply rtrancl_refl.
  assumption.
Qed.

Lemma ens_trans_rtrancl (T: Type) : forall (ens : Ensemble (T * T)) a b c, ens (a, b) -> rtrancl ens (b, c) -> rtrancl ens (a, c).
Proof.
  intros ens a b c.
  intros H H'.
  inversion H'.
  rewrite <- H2.
  apply rtrancl_base; assumption.
  apply rtrancl_trans with b0.
  apply rtrancl_trans with b.
  apply rtrancl_base; assumption.
Admitted.

Lemma rtrancl_trans_rtrancl (T: Type) :
  forall (ens : Ensemble (T * T)) a b c, rtrancl ens (a, b) -> rtrancl ens (b, c) -> rtrancl ens (a, c).
Proof.
  intros ens a b c.
  intros H H'.
  inversion H.
  assumption.
  inversion H'.
  rewrite <- H6.
  assumption.
  apply rtrancl_trans with b1.
Admitted.

(*Ensemble des états atteint après list A*)
Inductive steps_nae nae : list A -> Ensemble (S * S) :=
  (*Si la liste est vide*)
  | In_steps_nil : forall p q, rtrancl (eps nae) (p, q) -> steps_nae nae [] (p, q)
  (*Si la liste à un élément*)
  | In_steps_cons :
      forall h q sa sd,
        compose (compose (rtrancl (eps nae)) (step nae (Some h))) (steps_nae nae q) (sa, sd) ->
        steps_nae nae (h::q) (sa, sd).

(*Accéptation d'un automate*)
Definition accepts_eps nae w : Prop :=
  exists k, In _ (fin nae) k /\ In _ (steps_nae nae w) (start nae, k).

Lemma steps_epsclosure : forall nae w, compose (rtrancl (eps nae)) (steps_nae nae w) = steps_nae nae w.
Proof.
  intros nae w.
  destruct w; apply Extensionality_Ensembles.
  *split; intros (x, y) H.
    +inversion_clear H.
    inversion_clear H1.
    apply In_steps_nil.
    apply rtrancl_trans_rtrancl with b; assumption.
    +inversion_clear H.
    apply In_compose with x.
    apply rtrancl_refl.
    apply In_steps_nil.
    assumption.
  *split; intros (x, y) H.
    +inversion_clear H.
    apply In_steps_cons.
    inversion_clear H1.
    rewrite compose_assoc in H.
    inversion_clear H.
    rewrite compose_assoc.
    apply In_compose with b0.
    apply rtrancl_trans_rtrancl with b; assumption.
    assumption.
    +inversion_clear H.
    inversion_clear H0.
    inversion_clear H.
    apply In_compose with b0.
    assumption.
    apply In_steps_cons.
    apply In_compose with b.
    apply In_compose with b0.
    apply rtrancl_refl.
    assumption.
    assumption.
Qed.

Lemma in_steps_epsclosure : forall nae p q r w, rtrancl (eps nae) (p, q) -> steps_nae nae w (q, r) -> steps_nae nae w (p, r).
Proof.
  intros nae p q r w.
  intros H H'.
  rewrite <- steps_epsclosure.
  apply In_compose with q; assumption.
Qed.

Lemma epsclosure_steps: forall nae w, compose (steps_nae nae w) (rtrancl (eps nae)) = steps_nae nae w.
Proof.
  intros nae w.
  induction w; apply Extensionality_Ensembles; split; intros (x, y) H.
  *apply In_steps_nil.
  inversion_clear H.
  inversion_clear H0.
  apply rtrancl_trans_rtrancl with b; assumption.
  *inversion_clear H.
  apply In_compose with x.
  apply In_steps_nil.
  apply rtrancl_refl.
  assumption.
  *apply In_steps_cons.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H0.
  apply In_compose with b0.
  apply In_compose with b1.
  assumption.
  assumption.
  rewrite <- IHw.
  apply In_compose with b; assumption.
  *inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  apply In_compose with y; try apply rtrancl_refl.
  apply In_steps_cons.
  apply In_compose with b.
  apply In_compose with b0; assumption.
  assumption.
Qed.

Lemma in_epsclosure_steps : forall nae p q r w,  steps_nae nae w (p, q) -> rtrancl (eps nae) (q, r) -> steps_nae nae w (p, r).
Proof.
  intros nae p q r w.
  intros H H'.
  rewrite <- epsclosure_steps.
  apply In_compose with q; assumption.
Qed.

End Nae.

Section BitsNAe.

Variable A : Type.

Definition bitsNAe := nae A (list bool).

Definition empty_set := fun r : list bool => False.

Inductive atom_next (a: A) : option A -> list bool -> Ensemble (list bool) :=
  | Next_atomA : atom_next a (Some a) [true] [false].

Definition atom (a: A): bitsNAe :=
  mkNfa
    ([true])
    (atom_next a)
    (Singleton _ [false]).

(*On défini inductivement l'ensemble des états auquels on prepend un élément b*)
Inductive prepend_list_set (A: Type) (b: A) (ens: Ensemble (list A)) : Ensemble (list A) :=
  (*L'élément est dans l'ensemble si*)
  | In_prep : forall q, In _ ens q -> prepend_list_set b ens (b::q).

(*On défini inductivement la fonction next pour alt*)
Inductive alt_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  (*[] est l'état initial du nouvelle automate, cette regle ajoute une transition epsilon vers
    le start du premier automote, prepend de true*)
  | Next_altNL : alt_next nae1 nae2 None [] (true::start nae1)
  (*[] est l'état initial du nouvelle automate, cette regle ajoute une transition epsilon vers
    le start du premier automote, prepend de false*)
  | Next_altNR : alt_next nae1 nae2 None [] (false::start nae2)
  (*Si l'etat initial est de la forme true::q, on renvoie l'ensemble des next a q du 1er automate, pour toute transition a et
    prepend de true*)
  | Next_altL : forall a q s, In _ (next nae1 a q) s -> alt_next nae1 nae2 a (true::q) (true::s)
  (*Si l'état initial est de la forme true::q, on renvoie l'ensemble des next a q du 2nd automate, pour toute transition a et
    prepend de false*)
  | Next_altR : forall a q s, In _ (next nae2 a q) s -> alt_next nae1 nae2 a (false::q) (true::s).

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
    (*L'union des fin, avec les états du 1er automate, prepend de true
      et les états du 2nd automate prepend de false*)
    (Union _ (prepend_list_set true (fin nae1)) (prepend_list_set false (fin nae2))).

(*concaténation de deux automates*)
Inductive conc_next (nae1 nae2: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  (*Si l'etat initial est de la forme true::q, on renvoie l'ensemble des next a q du 1er automate, pour toute transition a et
    prepend de true*)
  | Next_concL : forall oa q s, next nae1 oa q s -> conc_next nae1 nae2 oa (true::q) (true::s)
  (*Lorsque l'on arrive a la fin du premier automate (l'etat s prepend de true), on fait une epsilon transition vers le start du second prepend de false*)
  | Next_concFL : forall oa s, fin nae1 s -> conc_next nae1 nae2 oa (true::s) (false::start nae2)
  (*Si l'etat initial est de la forme false::q, on renvoie l'ensemble des next a q du 2nd automate, pour toute transition a et
    prepend de true*)
  | Next_concR : forall oa q s, next nae2 oa q s -> conc_next nae1 nae2 oa (false::q) (false::s).

Definition conc (nae1: bitsNAe) (nae2: bitsNAe): bitsNAe :=
  let start1 := start nae1 in
  let start2 := start nae2 in

  let next1 := next nae1 in
  let next2 := next nae2 in

  let fin1 := fin nae1 in
  let fin2 := fin nae2 in

  mkNfa
    (true::start1)
    (conc_next nae1 nae2)
    (*Les états finaux sont ceux de fin2 prepend de false*)
    (prepend_list_set false fin2).

(*Le star de l'automate, on ajoute un état inital []*)
Inductive star_next (nae1: bitsNAe): option A -> list bool -> Ensemble (list bool) :=
  (*transition depuis l'etat inital vers le start de l'automate, prepend de true*)
  | Next_starSN : star_next nae1 None [] (true::start nae1)
  (*transition depsuis un des états finaux vers l'état inital de l'automate*)
  | Next_starN : forall s, fin nae1 s -> star_next nae1 None (true::s) (true::start nae1)
  (*Si l'etat initial est de la forme true::q, on renvoie l'ensemble des next a q de l'automate, pour toute transition a et
    prepend de true*)
  | Next_star : forall oa s q, next nae1 oa s q -> star_next nae1 oa (true::s) (true::q).

Definition star (nae1: bitsNAe): bitsNAe :=
  let start1 := start nae1 in

  let next1 := next nae1 in

  let fin1 := fin nae1 in

  mkNfa
    ([])
    (star_next nae1)
    (*tout les états finaux de l'autamate, prepend de true plus [], le nouvelle état initial*)
    (Add _ (prepend_list_set true fin1) []).

(*
  Exemple de definition utilisé avant, plus dur de prouver avec
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
    (prepend_list_set false fin2).*)

Fixpoint to_nfae (rexp: rexp A): bitsNAe :=
  match rexp with
  | Empty _ => mkNfa ([]) (fun s t => empty_set) (fun s => s = [])
  | Atom a => atom a
  | Alt r1 r2 => alt (to_nfae r1) (to_nfae r2)
  | Conc r1 r2 => conc (to_nfae r1) (to_nfae r2)
  | Star r => star (to_nfae r)
  end.

Lemma fin_atom : forall a q, fin (atom a) q <-> (q = [false]).
Proof.
  intros a q.
  simpl.
  split; intro H.
  inversion H; reflexivity.
  rewrite H.
  apply In_singleton.
Qed.

Lemma start_atom: forall a, start (atom a) = [true].
Proof.
  intro a.
  simpl.
  reflexivity.
Qed.

Lemma eps_atom: forall a, eps (atom a) = Empty_set _.
Proof.
  intro a.
  unfold eps.
  apply Extensionality_Ensembles; split; intros x H.
  *inversion_clear H.
  inversion_clear H0.
  *inversion_clear H.
Qed.

Lemma in_step_atom_Some: forall a b p q, step (atom a) (Some b) (p, q) <-> (p = [true] /\ q = [false] /\ b = a).
Proof.
  intros a b p q.
  split; intro H.
  inversion_clear H.
  inversion_clear H0.
  tauto.
  apply In_step.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  rewrite H1.
  apply Next_atomA.
Qed.

Lemma False_False_in_steps_atom: forall a w,  steps_nae (atom a) w ([false], [false]) <-> (w = []).
Proof.
  intros a w.
  induction w; split; intro H.
  *reflexivity.
  *apply In_steps_nil.
  apply rtrancl_refl.
  *inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H2.
  destruct H.
  inversion H0.
  inversion H3.
  inversion_clear H4.
  inversion H5.
  *inversion H.
Qed.

Lemma start_fin_in_steps_atom : forall a w, steps_nae (atom a) w (start (atom a), [false]) <-> (w = [a]).
Proof.
  intros a w.
  induction w; split; intro H.
  *inversion H.
  inversion H2.
  inversion H5.
  inversion H6.
  inversion H8.
  *inversion H.
  *inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H2.
  inversion H.
  rewrite <- H4 in H1.
  apply False_False_in_steps_atom in H1.
  rewrite H1.
  reflexivity.
  *apply In_steps_cons.
  inversion H.
  simpl.
  apply In_compose with [false].
  apply In_compose with [true].
  apply rtrancl_refl.
  apply In_step.
  apply Next_atomA.
  apply False_False_in_steps_atom.
  reflexivity.
Qed.

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
  apply In_steps_cons.
  apply In_compose with [false].
  apply In_compose with [true].
  apply rtrancl_refl.
  apply In_step.
  compute.
  apply Next_atomA.
  apply In_steps_nil.
  apply rtrancl_refl.
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

End Test.