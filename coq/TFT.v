Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Import Nat.
From Coq Require Import Lia.
From Coq Require Import Omega.
From Coq Require Import Lists.List.
From Coq Require Import String.
Open Scope string_scope.
Import ListNotations.
From TFT Require Import Maps.

Definition peer := string.

Definition hist := list (peer * bool).
Print eqb_string.
Lemma eqb_reflect : forall x y, reflect (x = y) (eqb_string x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply eqb_string_true_iff.
Qed.

Hint Resolve eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac inv H := inversion H; clear H; subst.

Fixpoint count (h:hist) : nat :=
  match h with
  | [] => 0
  | (_, true)::t => (count t) + 1
  | (_, false)::t => (count t) - 1
  end.

Example exp1:
  count [] = 0 . 
Proof.
  simpl. auto.
Qed.
  
Example exp2:
  count (("p1", false)::(("p1", true):: [])) = 0.
Proof.
  simpl. auto.
Qed.

Example exp3:
  count (("p2", true)::(("p1", true):: [])) = 2.
Proof.
  simpl. auto.
Qed.

Fixpoint get (h:hist) (p:peer) : bool :=
  match h with
  | [] => false
  | (p', val)::t => if eqb_string p' p then val else get t p 
  end.

Example exp4:
  get (("p2", true)::(("p1", true):: [])) "p2" = true.
Proof.
  simpl. auto.
Qed.

Example exp5:
  get (("p1", false)::(("p1", true):: [])) "p1" = false.
Proof.
  simpl. auto.
Qed.

Example exp6:
  get [] "p3" = false.
Proof.
  simpl. auto.
Qed.

(* Theorem exists_nonzero: forall h,
  (count h) > 0 -> (exists p, (get h p) = true).
Proof.
  intros.
  induction h.
  - inversion H.
  - destruct a.
    destruct b.
    + exists p. simpl. rewrite <- eqb_string_refl. auto.
    + simpl in H. apply gt_n_S in H.
      assert(H1: forall x, S (x - 1) > 1 -> x > 0).
      intros. lia.
      apply H1 in H. apply IHh in H. destruct H as [pe H2].
      exists pe.  
*)


Inductive event : Type :=
  | ESend (p1 p2 : peer)
  | EJoinWithout (p : peer)
  | EJoinWith (p : peer)
  | ELeave (p : peer).

Definition join_hist := hist.
Definition left_hist := hist.
Definition sent_hist := hist.
Definition holds_hist := hist.
Definition state := (join_hist * left_hist * sent_hist * holds_hist)%type.

Definition eqb_bool (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition update_state (s:state) (e : event) : state :=
  match s with
  | (joined, has_left, has_sent, holds) =>
    match e with
      | ESend p1 p2 =>
        (joined, has_left, ((p1, true)::has_sent), ((p2, true)::holds)) (* Check if already sent?? *)
      | EJoinWithout p => ( ((p, true)::joined), has_left, has_sent, ((p, false)::holds))
      | EJoinWith p => ( ((p, true)::joined), has_left, has_sent, ((p, true)::holds))
      | ELeave p => ( ((p, false)::joined), 
                      ((p, true)::has_left), 
                        has_sent, 
                        holds )
    end
  end.
Definition joined (s:state) : join_hist := 
  match s with
  | (h, _, _, _) => h
  end.

Definition has_left (s:state) : left_hist := 
  match s with
  | (_, h, _, _) => h
  end.

Definition has_sent (s:state) : sent_hist := 
  match s with
  | (_, _, h, _) => h
  end.

Definition holds (s:state) : holds_hist := 
  match s with
  | (_, _, _, h) => h
  end.

Definition relation (X : Type) := X -> X -> Prop.

Reserved Notation " t '-->' t' " (at level 40).
Inductive action : state -> state -> Prop := 
  | A_Send : forall st p1 p2, 
    get (holds st) p1 = true /\ 
    get (holds st) p2 = false /\
    get (joined st) p1 = true /\
    get (joined st) p2 = true  ->
    st --> ((joined st), (has_left st), ((p1, true)::(has_sent st)), ((p2, true)::(holds st)))
  | A_Join_Without : forall st p,
    get (joined st) p = false /\
    get (has_left st) p = false /\
    (exists q, get (joined st) q = true) ->
    st --> ( ((p, true)::(joined st)), (has_left st), (has_sent st), ((p, false)::(holds st)))
  | A_Join_With : forall st p,
    get (joined st) p = false /\
    get (has_left st) p = false /\
    (exists q, get (joined st) q = true) ->
    st --> ( ((p, true)::(joined st)), (has_left st), (has_sent st), ((p, true)::(holds st)))
  | A_Leave : forall st p,
    get (joined st) p = true /\
    get (has_left st) p = false /\
    ( get (has_sent st) p = true \/ 
      ( forall q, ( get (joined st) q = true -> 
                    ( get (holds st) q = true /\ get (has_sent st) q = false) 
                  )
      )    
    ) ->
    st --> ( ((p, false)::(joined st)), ((p, true)::(has_left st)), 
                        has_sent st, holds st)
where " st '-->' st' " := (action st st').

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R y z ->
                    multi R x y ->
                    multi R x z.

Compute update_state (("b", true)::[],[],[],[]) (EJoinWithout "a").
Example test1:
  (("b", true)::[],[],[],[]) --> ((("a",true)::(("b", true)::[])), [],[],[("a", false)]).
Proof.
  apply A_Join_Without. 
  split.
  - simpl. auto.
  - split. 
    + simpl. auto.
    + exists "b". simpl. auto.
Qed.

Notation " st '-->*' st' " := (multi action st st') (at level 40).

Example test2:
  (("b", true)::[],[],[],[]) -->* ((("a",true)::(("b", true)::[])), [],[],[("a", false)]).
Proof.
  apply multi_step with (("b", true)::[],[],[],[]).
  apply A_Join_Without. 
  split.
  - simpl. auto.
  - split. 
    + simpl. auto.
    + exists "b". simpl. auto.
  - apply multi_refl.
Qed.

Definition initial (st: state) :=
  (forall p, get (has_left st) p = false /\ get (has_sent st) p = false) /\
  (exists seeder, get (joined st) seeder = true /\ get (holds st) seeder = true).

Definition Init (init: state -> Prop) (inv: state -> Prop) := 
  forall i, init i -> inv i.

Definition Inductive (inv: state -> Prop) := 
  forall st st',
  st --> st' -> inv st -> inv st'.
  
Definition Inv (init: state -> Prop) (inv: state -> Prop) :=
  forall i st, 
  init i ->
  inv i /\ (i -->* st -> inv st).

Theorem Safe_Inductive (init inv : state -> Prop):
  Init init inv /\ Inductive inv -> Inv init inv.
Proof.
  unfold Init. unfold Inductive. unfold Inv.
  intros.
  destruct H.
  split.
  - apply H. auto.
  - intros. 
    induction H2. 
    + apply H. auto.
    + apply H1 with y. 
      * auto.
      * auto.
Qed.


Definition prepared_cannot_send_inv (st:state) :=
  forall p, get (joined st) p = false /\ get (has_left st) p = false ->
            get (has_sent st) p = false.

Theorem prepared_cannot_send_init: Init initial prepared_cannot_send_inv.
Proof.
  unfold Init. unfold initial. unfold prepared_cannot_send_inv.
  intros.
  inv H. inv H0. inv H2. inv H0. apply H1.
Qed.

Theorem prepared_cannot_send_inductive: Inductive prepared_cannot_send_inv.
Proof.
  unfold Inductive. unfold prepared_cannot_send_inv.
  intros. inv H1. 
  induction H;  try(inv H; simpl in H2; simpl in H3; inv H4; inv H5; simpl).
  - bdestruct (eqb_string p1 p). inv H5. rewrite H2 in H4. inv H4.
    auto.
  - bdestruct (eqb_string p0 p). inv H2.
    apply H0. split; auto.
  - apply H0; split; auto.
    bdestruct (eqb_string p0 p). inv H2.
    auto.
  - bdestruct (eqb_string p0 p). inv H3.
    apply H0; auto.
  - bdestruct (eqb_string p0 p). inv H3.
    apply H0; auto.
Qed.

Theorem prepared_cannot_send_invariant: Inv initial prepared_cannot_send_inv.
Proof.
  apply (Safe_Inductive initial prepared_cannot_send_inv).
  split. apply prepared_cannot_send_init. apply prepared_cannot_send_inductive.
Qed.

Definition sent_holds_inv (st: state) :=
  forall p, get (has_sent st) p = true -> get (holds st) p = true.

Theorem sent_holds_init: Init initial sent_holds_inv.
Proof.
  unfold Init. unfold initial. unfold sent_holds_inv. intros.
  destruct H. destruct H1. destruct H1.
  destruct (H p). rewrite H0 in H4. inversion H4.
Qed.

Theorem sent_holds_invariant: Inv initial sent_holds_inv.
Proof.
  unfold Inv. intros.
  split.
  - apply sent_holds_init; auto.
  - intros. 
    unfold sent_holds_inv.
    intros.
    induction H0. 
    + unfold initial in H. inv H. inv H2. inv H. destruct (H0 p).
      rewrite H1 in H4. inv H4.
    + induction H0; try(inv H0; simpl in H1; inv H4; inv H5; simpl); 
      try(bdestruct (eqb_string p2 p); auto);
      try(bdestruct (eqb_string p1 p); auto);
      try(bdestruct (eqb_string p0 p); auto).
      * inv H0. simpl in H1. inv H4. rewrite H3. auto.
      * inv H5.   
        assert(Ha: get (has_sent st) p = false).
        apply (prepared_cannot_send_invariant x st); auto.
        rewrite H1 in Ha. inv Ha.
Qed.

Definition remaining_holds_inv (st: state) :=
(*  (exists p, get (joined st) p = true) -> count (holds st) > count (has_sent st).*)
    forall p, 
    (get (has_sent st) p = true /\ get (joined st) p = true) -> 
    (exists q, get (holds st) q = true /\ 
               get (has_sent st) q = false /\
               get (joined st) q = true
    ).

Theorem remaining_holds_init: Init initial remaining_holds_inv.
Proof.
  unfold Init. unfold initial.
  unfold remaining_holds_inv.
  intros. 
  inv H0. 
  inv H. inv H3.
  exists x. inv H. split; auto.
  split. apply H0. auto.
Qed. 

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. 
  unfold not. intros. 
  apply H in H1. unfold not in H0. auto.
Qed.


Theorem remaining_holds_invariant: Inv initial remaining_holds_inv.
Proof.
  unfold Inv.
  intros. split. apply remaining_holds_init; auto.
  intros. 
  induction H0.
  - apply remaining_holds_init; auto.
  - assert(Hinit: initial x); auto.
    apply IHmulti in H.
    induction H0;
    try(inv H0; inv H3; inv H4; unfold remaining_holds_inv; simpl; intros);
    try(unfold remaining_holds_inv in H).
    + apply (sent_holds_invariant x st) in Hinit.
      inv Hinit.
      apply H7 in H1. unfold sent_holds_inv in H1.
      assert(get (has_sent st) p2 = true -> get (holds st) p2 = true); auto.
      apply contrapositive in H8.
      apply not_true_iff_false in H8.

      bdestruct (eqb_string p1 p); auto. inv H4;
      try(exists p2; bdestruct (eqb_string p2 p2); bdestruct (eqb_string p p2); try(repeat(split; auto))).
      * inv H9.  rewrite H2 in H0.  inv H0.
      * unfold not in H4. assert (p2 = p2); auto. apply H4 in H12. inv H12.
      * exists p2. 
        try(bdestruct (eqb_string p2 p2); bdestruct (eqb_string p1 p2); try(repeat(split; auto))).
        inv H11. rewrite H2 in H0; auto.
        unfold not in H10. assert (p2 = p2); auto. apply H10 in H12. inv H12.
      * apply not_true_iff_false. auto.
    + bdestruct (eqb_string p p0).
      inv H4. 
      apply (prepared_cannot_send_invariant x st) in Hinit.
      inv Hinit.
      apply H5 in H1.
      unfold prepared_cannot_send_inv in H1.
      assert (get (has_sent st) p0 = false). apply H1; auto.
      rewrite H6 in H8; inv H8.
      apply H in H4. inv H4. inv H6. inv H7. 
      exists x1.
      bdestruct (eqb_string p x1). split.
      inv H7. rewrite H2 in H8; inv H8.
      split; auto.
      split; auto.
    + bdestruct (eqb_string p p0). inv H4. 
      apply (prepared_cannot_send_invariant x st) in Hinit.
      inv Hinit.
      apply H5 in H1.
      unfold prepared_cannot_send_inv in H1.
      assert (get (has_sent st) p0 = false). apply H1; auto.
      rewrite H6 in H8; inv H8.
      apply H in H4. inv H4. inv H6. inv H7. 
      exists x1.
      bdestruct (eqb_string p x1). split.
      inv H7. rewrite H2 in H8; inv H8.
      split; auto.
      split; auto.
    + bdestruct (eqb_string p p0); auto. inv H4; inv H7. inv H4.
      assert(get (has_sent st) p = true /\ get (joined st) p = true); auto.
      apply H in H4. repeat(try(inv H4)). inv H8. inv H9.
      exists x0.
      split; auto.
      split; auto.
      bdestruct (eqb_string p x0); auto. inv H9. rewrite H3 in H8; inv H8.
    + bdestruct (eqb_string p p0); auto. inv H4; inv H7. inv H4.
      apply H3 in H7. inv H7. rewrite H6 in H8; inv H8.
Qed.

    
  
