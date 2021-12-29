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
| cs_give : forall n T v chs thrds,
    value v -> n < length chs ->
    cfg_step (Config chs ((tm_give (tm_ch n T) v) :: thrds)) (Config (give_chs n v chs) (tm_unit :: thrds))
| cs_take : forall n T chs thrds v t,
    n < length chs -> nth_error chs n = Some (v :: t) ->
    cfg_step (Config chs ((tm_take (tm_ch n T)) :: thrds)) (Config (update n t chs) (v :: thrds))
| cs_fork : forall t chs thrds,
    cfg_step (Config chs ((tm_fork t) :: thrds)) (Config chs (tm_unit :: (thrds ++ [t])))
| cs_mkch : forall T chs thrds,
    cfg_step (Config chs ((tm_mkch T) :: thrds)) (Config (chs ++ [[]]) ((tm_ch (length chs) T) :: thrds))
| cs_term : forall E t1 t2 result1 result2 chs thrds,
    fillCtx E t1 result1 ->
    fillCtx E t2 result2 ->
    step t1 t2 ->
    cfg_step (Config chs (result1 :: thrds)) (Config chs (result2 :: thrds))
| cs_sub : forall E t t' result result' chs chs' thrds thrds',
    ~ value t ->
    fillCtx E t result ->
    fillCtx E t' result' ->
    cfg_step (Config chs (t :: thrds)) (Config chs' (t' :: thrds')) ->
    cfg_step (Config chs (result :: thrds)) (Config chs' (result' :: thrds'))
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
                                    (value h) \/ (exists h' chs' t', cfg_step c (Config chs' (h' :: t'))) \/
                                      (exists E n T, fillCtx E (tm_take (tm_ch n T)) h ->
                                                nth_error chs n = Some [])
                     end
end.
  intros [chs thrds].
  destruct thrds; auto. intros.
  assert (H' := H).
  apply progress in H. destruct H as [ | []].
  - auto.
  - destruct H. right. left. exists x, chs, thrds. simpl. eauto.
  - destruct H as [E H]. destruct H as [|[|[]]].
    + destruct H. right. left. assert (H'' := H). eapply subterm_swap in H. destruct H. exists x0. eexists.
      exists thrds. eapply cs_sub; eauto. intros contr. inversion contr.
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
          exists x1. simpl. eexists. eexists. eapply cs_sub; eauto. intros contr. inversion contr. eapply cs_take.
          eapply subterm_bounded in H''; eauto. symmetry in Heqo. eauto.
        }
      * eapply subterm_bounded in H''; eauto. simpl in H''. symmetry in Heqo. apply nth_error_None in Heqo.
        lia.
    + destruct H as (c & v & H & H1 & H2). assert (H'' := H).
      eapply subterm_type in H; eauto. destruct H. inversion H; subst. apply canonical_channel in H6; auto.
      destruct H6; subst. right. left. assert (H''' := H''). apply subterm_swap with (t' := tm_unit) in H''.
      destruct H''. exists x0. simpl. eexists. eexists. intros. eapply cs_sub; eauto. intros contr. inversion contr.
      eapply cs_give; eauto. eapply subterm_bounded in H'''; eauto.
      simpl in H'''. destruct H'''. auto.
    (* + destruct H as (f & H & H1). right. left. do 2 eexists. eapply cs_sub. eapply H. *)
      (* apply subterm_swap with (t' := tm_unit) in H. destruct H. eapply H. *)
    + destruct H as (f & H & H1). right. left. assert (H'' := H). apply subterm_swap with (t' := tm_unit) in H.
      destruct H. exists x, chs, (thrds ++ [f]). eapply cs_sub; eauto. intros contr. inversion contr.
Qed.

Fixpoint all_typed (l : list tm) (T : ty) :=
match l with
| [] => True
| h :: t => empty ⊢ h ∈ T /\ all_typed t T
end.

Fixpoint channels_typed (t : tm) (chs : channels) :=
match t with
| tm_var x => True
| tm_abs x T t => channels_typed t chs
| tm_unit => True
| tm_app t1 t2 => channels_typed t1 chs /\ channels_typed t2 chs
| tm_let x t1 t2 => channels_typed t1 chs /\ channels_typed t2 chs
| tm_fork t => channels_typed t chs
| tm_give t1 t2 => channels_typed t1 chs /\ channels_typed t2 chs
| tm_take t => channels_typed t chs
| tm_mkch T => True
| tm_ch n T => exists b, nth_error chs n = Some b /\ all_typed b T
end.

Lemma subterm_channels_typed : forall E t result chs, fillCtx E t result -> channels_typed result chs ->
                                        channels_typed t chs.
Proof.
  induction E; intros; inversion H; subst; eauto; simpl in H0; destruct H0; eauto.
Qed.

Theorem cfg_preservation : forall c,
    match c with
    | Config chs thrds => match thrds with
                         | [] => True
                         | h :: t => forall h' T chs' t', empty ⊢ h ∈ T -> ~ value h ->
                                                   channels_typed h chs ->
                                                   cfg_step (Config chs (h :: t)) (Config chs' (h' :: t')) ->
                                                   empty ⊢ h' ∈ T
                         end
    end.
Proof.
  intros [chs thrds].
  destruct thrds as [|h t]; trivial.
  intros.
  remember (Config chs (h :: t)). remember (Config chs' (h' :: t')).
  generalize dependent T. generalize dependent h. generalize dependent h'. generalize dependent t. generalize dependent t'.
  induction H2; intros; inversion Heqc; inversion Heqc0; subst; intros; try (inversion H; subst; try inversion H3; subst; eauto; reflexivity).
  - simpl in H2. destruct H2 as (b & H2 & H4). assert (Some b = Some (h' :: t)).
    { rewrite <- H0. rewrite <- H2. reflexivity. }
    inversion H5. subst. simpl in H4. inversion H3; subst. inversion H8; subst.
    destruct H4. assumption.
  - eapply preservation; eauto.
  - assert (H5' := H5). eapply subterm_type in H5'; eauto. destruct H5'.
    assert (H6' := H6). eapply IHcfg_step in H6'; eauto. eapply ctx_preservation. eapply H6.
    eapply H6'. eapply H0. assumption. assumption. eapply subterm_channels_typed; eauto.
  - contradiction.
Qed.
