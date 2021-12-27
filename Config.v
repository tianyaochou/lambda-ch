From CHSTLC Require Import Terms.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.

Definition buffer := list tm.

Definition channels := list buffer.

Inductive config : Type :=
| Config : channels -> list tm -> config
.

Fixpoint update {A} (n : nat) (a : A) (l : list A) : (list A) :=
match l with
| [] => l
| h :: t => match n with
          | 0 => a :: t
          | S n' => h :: (update n' a t)
          end
end.

Fixpoint give_chs (n : nat) (v : tm) (chs : channels) :=
match chs with
| [] => []
| h :: t => match n with
          | O => (h ++ [v]) :: t
          | S n' => h :: (give_chs n' v t)
          end
end.

Inductive cfg_step : config -> config -> Prop :=
| cs_give : forall E n T v result1 result2 chs thrds,
    value v -> fillCtx E (tm_give (tm_ch n T) v) result1 ->
    fillCtx E (tm_unit) result2 ->
    n < length chs -> cfg_step (Config chs (result1 :: thrds)) (Config (give_chs n v chs) (result2 :: thrds))
| cs_take : forall E n T result1 result2 chs thrds v t,
    fillCtx E (tm_take (tm_ch n T)) result1 ->
    fillCtx E v result2 ->
    n < length chs -> nth_error chs n = Some (v :: t) ->
    cfg_step (Config chs (result1 :: thrds)) (Config (update n t chs) (result2 :: thrds))
| cs_fork : forall E t result1 result2 chs thrds,
    fillCtx E (tm_fork t) result1 ->
    fillCtx E (tm_unit) result2 ->
    cfg_step (Config chs (result1 :: thrds)) (Config chs ([t; result2] ++ thrds))
| cs_mkch : forall E T result1 result2 chs thrds,
    fillCtx E (tm_mkch T) result1 ->
    fillCtx E (tm_ch (length thrds) T) result2 ->
    cfg_step (Config chs (result1 :: thrds)) (Config (chs ++ [[]]) (result2 :: thrds))
| cs_term : forall E t1 t2 result1 result2 chs thrds,
    fillCtx E t1 result1 ->
    fillCtx E t2 result2 ->
    step t1 t2 ->
    cfg_step (Config chs (result1 :: thrds)) (Config chs (result2 :: thrds))
| cs_sub : forall E t t' result result' chs chs' thrds, fillCtx E t result ->
                                             fillCtx E t' result' ->
                                             cfg_step (Config chs (t :: thrds)) (Config chs' (t' :: thrds)) ->
                                             cfg_step (Config chs (result :: thrds)) (Config chs' (result' :: thrds))
| cs_pop : forall v chs thrds,
    value v -> cfg_step (Config chs (v :: thrds)) (Config chs thrds)
.

Global Hint Constructors cfg_step : core.

Lemma nth_error_some_length : forall A n l (v : A), Some v = nth_error l n -> n < length l.
Proof.
  intros. apply nth_error_Some. intros contr. rewrite <- H in contr. inversion contr.
Qed.

Lemma subterm_swap : forall E t t' result, fillCtx E t result -> exists result', fillCtx E t' result'.
Proof.
  induction E; intros; eauto.
  - inversion H; subst. eapply IHE in H4. destruct H4. eauto.
  - inversion H; subst. eapply IHE in H5. destruct H5. eauto.
  - inversion H; subst. eapply IHE in H5. destruct H5. eauto.
  - inversion H; subst. eapply IHE in H1. destruct H1. eauto.
  - inversion H; subst. eapply IHE in H4. destruct H4. eauto.
  - inversion H; subst. eapply IHE in H5. destruct H5. eauto.
  - inversion H; subst. eapply IHE in H1. destruct H1. eauto.
Qed.

Fixpoint channels_bounded (t : tm) (chs : channels) :=
match t with
| tm_var x => True
| tm_abs x T t => channels_bounded t chs
| tm_unit => True
| tm_app t1 t2 => channels_bounded t1 chs /\ channels_bounded t2 chs
| tm_let x t1 t2 => channels_bounded t1 chs /\ channels_bounded t2 chs
| tm_fork t => channels_bounded t chs
| tm_give t1 t2 => channels_bounded t1 chs /\ channels_bounded t2 chs
| tm_take t => channels_bounded t chs
| tm_mkch T => True
| tm_ch n T => n < length chs
end.

Lemma subterm_bounded : forall E t result chs, fillCtx E t result -> channels_bounded result chs ->
                                          channels_bounded t chs.
Proof.
  induction E; intros; inversion H; subst; try destruct H0; eauto.
Qed.

Theorem config_progress : forall c,
match c with
| Config chs thrds => match thrds with
                     | [] => True
                     | h :: t => forall T, empty ⊢ h ∈ T -> channels_bounded h chs ->
                                    (value h) \/ (exists h' chs', h' <> [] -> cfg_step c (Config chs' (h' ++ t))) \/
                                      (exists E n T, fillCtx E (tm_take (tm_ch n T)) h ->
                                                nth_error chs n = Some [])
                     end
end.
  intros [chs thrds].
  destruct thrds; auto. intros.
  assert (H' := H).
  apply progress in H. destruct H as [ | []].
  - auto.
  - destruct H. right. left. exists [x], chs. simpl. eauto.
  - destruct H as [E H]. destruct H as [|[|[]]].
    + destruct H. right. left. assert (H'' := H). eapply subterm_swap in H. destruct H. exists [x0]. simpl. eauto.
    + destruct H as (c & H & H1). assert (H'' := H).
      eapply subterm_type in H; eauto. destruct H. inversion H; subst.
      apply canonical_channel in H4; auto. destruct H4; subst. right. remember (nth_error chs x0).
      destruct o.
      * destruct b.
        {
          right. exists E, x0, x. intros. auto.
        }
        {
          left. assert (H''' := H''). apply subterm_swap with (t' := t0) in H'''. destruct H'''.
          exists [x1]. simpl. eexists. intros. eapply cs_take. eapply H''. eapply H2. apply nth_error_some_length in Heqo. auto.
          symmetry in Heqo. eapply Heqo.
        }
      * eapply subterm_bounded in H''; eauto. simpl in H''. symmetry in Heqo. apply nth_error_None in Heqo.
        lia.
    + destruct H as (c & v & H & H1 & H2). assert (H'' := H).
      eapply subterm_type in H; eauto. destruct H. inversion H; subst. apply canonical_channel in H6; auto.
      destruct H6; subst. right. left. assert (H''' := H''). apply subterm_swap with (t' := tm_unit) in H''.
      destruct H''. exists [x0]. simpl. eexists. intros.  eapply cs_give; eauto. eapply subterm_bounded in H'''; eauto.
      simpl in H'''. destruct H'''. auto.
    (* + destruct H as (f & H & H1). right. left. do 2 eexists. eapply cs_sub. eapply H. *)
      (* apply subterm_swap with (t' := tm_unit) in H. destruct H. eapply H. *)
    + destruct H as (f & H & H1). right. left. assert (H'' := H). apply subterm_swap with (t' := tm_unit) in H.
      destruct H. exists [f; x], chs. intros. eauto.
Qed.

(* Theorem cfg_preservation : forall c, *)
(*     match c with *)
(*     | Config chs thrds => match thrds with *)
(*                          | [] => True *)
(*                          | h :: t => forall h' T chs' f, empty ⊢ h ∈ T -> *)
(*                                                      cfg_step (Config chs (h::t)) (Config chs' (f ++ [h'] ++ t)) -> *)
(*                                                      empty ⊢ h' ∈ T *)
(*                          end *)
(*     end. *)
(* Proof. *)
(*   intros [chs thrds]. *)
(*   destruct thrds as [|h t]; trivial. *)
(*   intros. generalize dependent T. remember (f ++ [h'] ++ t). destruct l. *)
(*   - destruct f; inversion Heql. *)
(*   - induction H0; intros. *)
