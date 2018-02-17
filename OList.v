(** * Option-List (OList) *)

(* TODO: edit imports. *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Basics.

Module OList.

(** Dimensions and configurations. *)
Definition dim := nat.
Definition tag := bool.
Definition L : tag := true.
Definition R : tag := false.
Definition config := dim -> tag.

(** Formula syntax. *)
Inductive formula : Type :=
  | litT : tag -> formula
  | litD : dim -> formula
  | comp : formula -> formula
  | join : formula -> formula -> formula
  | meet : formula -> formula -> formula.

(* TODO: add scope to notation. *)
Notation "~ x" := (comp x) (at level 75, right associativity).
Infix "\/" := join (at level 85, right associativity).
Infix "/\" := meet (at level 80, right associativity).

(** Formula semantics. *)
Fixpoint semf (x : formula) (c : config) : tag :=
  match x with
  | litT t   => t
  | litD d   => c d
  | ~ x      => negb (semf x c)
  | x1 \/ x2 => (semf x1 c) || (semf x2 c)
  | x1 /\ x2 => (semf x1 c) && (semf x2 c)
  end.

(** Variational option definition. *)
Inductive var : Type :=
  | one : option nat -> var
  | chc : formula -> var -> var -> var.

(** Selection operation for variational option. *)
Fixpoint vsel (c : config) (v : var) : option nat :=
  match v with
  | one o      => o
  | chc x l r  => if semf x c then vsel c l else vsel c r
  end.

(** Option-list definition. *)
Definition olist := list var.

(** Selection operation for option-list. *)
Fixpoint osel (c : config) (o : olist) : list nat :=
  match o with
  | []     => []
  | h :: t => match vsel c h with
              | None   => osel c t
              | Some y => y :: osel c t
              end
  end.

(** ** Map *)
(** Definition of map operation for option-list and a formal proof of
    soundness. *)
Section Map.

(** Helper function of map operation for option-list. *)
Fixpoint hmap (f : nat -> nat) (v : var) : var :=
  match v with
  | one None     => one None
  | one (Some n) => one (Some (f n))
  | chc x l r    => chc x (hmap f l) (hmap f r)
  end.

(** Map operation for option-list. *)
Fixpoint omap (f : nat -> nat) (o : olist) : olist :=
  match o with
  | []     => []
  | h :: t => hmap f h :: omap f t
  end.

(* Lemma used in proof of [omap_sound]. *)
Lemma vsel_none : forall (c : config) (f : nat -> nat) (e : var),
                  vsel c e = None ->
                  vsel c (hmap f e) = None.
Proof.
  intros c f e H.
  induction e as [o | x l IHl r IHr].
  (* Case: [e = one o]. *)
    destruct o as [n |].
    (* Subcase: [o = Some n]. *)
      simpl vsel in H.
      inversion H.
    (* Subcase: [o = None]. *)
      reflexivity.
  (* Case: [e = chc x l r]. *)
    simpl.
    simpl in H.
    destruct (semf x c).
    (* Subcase: [semf x c = L]. *)
      rewrite -> IHl by apply H.
      reflexivity.
    (* Subcase: [semf x c = R]. *)
      rewrite -> IHr by apply H.
      reflexivity.
Qed.

(* Lemma used in proof of [omap_sound]. *)
Lemma vsel_some : forall (c : config) (f : nat -> nat) (e : var) (n : nat),
                  vsel c e = Some n ->
                  vsel c (hmap f e) = Some (f n).
Proof.
  intros c f e n H.
  induction e as [o | x l IHl r IHr].
  (* Case: [e = one o]. *)
    destruct o as [n' |].
    (* Subcase: [o = Some n']. *)
      simpl vsel in H.
      inversion H.
      reflexivity.
    (* Subcase: [o = None]. *)
      simpl vsel in H.
      inversion H.
  (* Case: [e = chc x l r]. *)
    simpl.
    simpl in H.
    destruct (semf x c).
    (* Subcase: [semf x c = L]. *)
      rewrite -> IHl by apply H.
      reflexivity.
    (* Subcase: [semf x c = R]. *)
      rewrite -> IHr by apply H.
      reflexivity.
Qed.

Infix "*" := compose.

(** The map operation for option-list is sound. *)
Theorem omap_sound : forall (c : config) (f : nat -> nat) (o : olist),
                       (osel c * omap f) o = (map f * osel c) o.
Proof.
  intros c f o.
  unfold compose.
  induction o as [| h t IH].
  (* Case: [o = nil]. *)
    reflexivity.
  (* Case: [o = cons h t]. *)
    simpl omap.
    destruct (vsel c h) as [n |] eqn : H.
    (* Subcase: [vsel c h = Some n]. *)
      simpl osel.
      rewrite -> vsel_some with (n := n) by apply H.
      rewrite -> H.
      simpl map.
      rewrite -> IH.
      reflexivity.
    (* Subcase: [vsel c h = None]. *)
      simpl osel.
      rewrite -> vsel_none by apply H.
      rewrite -> H.
      apply IH.
Qed.

End Map.

(** ** Bind *)
(** Definition of bind operation for option-list and a formal proof of
    soundness. *)
Section Bind.

(** Helper function of bind operation for option-list. *)
Fixpoint hzip (x : formula) (o o' : olist) : olist :=
  match o, o' with
  | [], _            => map (fun v : var => chc x (one None) v) o'
  | _, []            => map (fun v : var => chc x v (one None)) o
  | h :: t, h' :: t' => chc x h h' :: hzip x t t'
  end.

(** Helper function of bind operation for option-list. *)
Fixpoint hbind (f : nat -> olist) (v : var) : olist :=
  match v with
  | one None     => []
  | one (Some n) => f n
  | chc x l r    => hzip x (hbind f l) (hbind f r)
  end.

(** Bind operation for option-list. *)
Fixpoint obind (f : nat -> olist) (o : olist) : olist :=
  match o with
  | []     => []
  | h :: t => hbind f h ++ obind f t
  end.

(** Lemma used to simplify goals in later proofs. *)
Lemma osel_cons_chc_l :
  forall (c : config) (x : formula) (l r : var) (o : olist),
  semf x c = L ->
  osel c (chc x l r :: o) = osel c (l :: o).
Proof.
  intros c x l r o H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Lemma used to simplify goals in later proofs. *)
Lemma osel_cons_chc_r :
  forall (c : config) (x : formula) (l r : var) (o : olist),
  semf x c = R ->
  osel c (chc x l r :: o) = osel c (r :: o).
Proof.
  intros c x l r o H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Selection for option-list distributes over append. *)
Lemma osel_app : forall (c : config) (o o' : olist),
                 osel c (o ++ o') = osel c o ++ osel c o'.
Proof.
  intros c o o'.
  induction o as [| h t IH].
  (* Case: [o = nil]. *)
    reflexivity.
  (* Case: [o = cons h t]. *)
    simpl.
    destruct (vsel c h) as [n |].
    (* Subcase: [vsel c h = Some n]. *)
      rewrite <- app_comm_cons.
      rewrite -> IH.
      reflexivity.
    (* Subcase: [vsel c h = None]. *)
      apply IH.
Qed.

(** Lemma used to simplify goals in later proofs. *)
Lemma ozip_nil_l : forall (x : formula) (o : olist),
                   hzip x [] o = map (fun v : var => chc x (one None) v) o.
Proof.
  destruct o;
    unfold hzip;
    reflexivity.
Qed.

(** Lemma used to simplify goals in later proofs. *)
Lemma ozip_nil_r : forall (x : formula) (o : olist),
                   hzip x o [] = map (fun v : var => chc x v (one None)) o.
Proof.
  destruct o;
    unfold hzip;
    reflexivity.
Qed.

(** Lemma used to simplify goals in later proofs. *)
Lemma osel_ozip_l : forall (c : config) (x : formula),
                    semf x c = L ->
                    forall o o' : olist, osel c (hzip x o o') = osel c o.
Proof.
  intros c x H.
  assert (H' : forall o : olist, osel c (hzip x [] o) = []).
  (* Proof of assertion [H']. *)
    intro o.
    induction o as [| h t IH].
    (* Case: [o = nil]. *)
      reflexivity.
    (* Case: [o = cons h t]. *)
      rewrite -> ozip_nil_l.
      simpl map.
      rewrite -> osel_cons_chc_l by apply H.
      simpl.
      rewrite <- ozip_nil_l.
      apply IH.
  (* Proof of [osel_ozip_l]. *)
  intro o.
  induction o as [| h t IH].
  (* Case: [o = nil]. *)
    apply H'.
  (* Case: [o = cons h t]. *)
    destruct o' as [| h' t'];
      simpl hzip;
      rewrite -> osel_cons_chc_l by apply H;
      try (rewrite <- ozip_nil_r);
      destruct h as [o | y l r];
        try (destruct o);
        simpl;
        rewrite -> IH;
        reflexivity.
Qed.

(** Lemma used to simplify goals in later proofs. *)
Lemma osel_ozip_r : forall (c : config) (x : formula),
                    semf x c = R ->
                    forall o o' : olist,
                    osel c (hzip x o' o) = (osel c o).
Proof.
  intros c x H.
  assert (H' : forall o : olist, osel c (hzip x o []) = []).
  (* Proof of assertion [H']. *)
    intro o.
    induction o as [| h t IH].
    (* Case: [o = nil]. *)
      reflexivity.
    (* Case: [o = cons h t]. *)
      rewrite -> ozip_nil_r.
      simpl map.
      rewrite -> osel_cons_chc_r by apply H.
      simpl.
      rewrite <- ozip_nil_r.
      apply IH.
  (* Proof of [osel_ozip_r]. *)
  intros o.
  induction o as [| h t IH].
  (* Case: [o = nil]. *)
    apply H'.
  (* Case: [o = cons h t]. *)
    destruct o' as [| h' t'];
      simpl hzip;
      rewrite -> osel_cons_chc_r by apply H;
      try (rewrite <- ozip_nil_l);
      destruct h as [o | y l r];
        try (destruct o);
        simpl;
        try (rewrite <- ozip_nil_l);
        rewrite -> IH;
        reflexivity.
Qed.

Infix "*" := compose.

(** The bind operation for option-list is sound. *)
Theorem obind_sound : forall (c : config) (f : nat -> olist) (o : olist),
                        (osel c * obind f) o =
                        (flat_map (osel c * f) * osel c) o.
Proof.
  intros c f o.
  unfold compose.
  induction o as [| h t IH].
  (* Case: [o = nil]. *)
    reflexivity.
  (* Case: [o = cons h t]. *)
    simpl obind.
    rewrite -> osel_app.
    induction h as [o | x l IHl r IHr].
    destruct o.
    (* Subcase: [h = one (Some n)]. *)
      simpl.
      rewrite -> IH.
      reflexivity.
    (* Subcase: [h = one None]. *)
      simpl.
      apply IH.
    (* Subcase: [h = chc x l r]. *)
      simpl hbind.
      destruct (semf x c) eqn : H.
        rewrite -> osel_ozip_l by apply H.
        rewrite -> osel_cons_chc_l by apply H.
        apply IHl.
        rewrite -> osel_ozip_r by apply H.
        rewrite -> osel_cons_chc_r by apply H.
        apply IHr.
Qed.

End Bind.

End OList.
