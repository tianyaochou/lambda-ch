From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From CHSTLC Require Import Maps.

Inductive ty : Type :=
| Ty_Unit : ty
| Ty_Arrow : ty -> ty -> ty
| Ty_Ch : ty -> ty
.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_abs : string -> ty -> tm -> tm
| tm_unit : tm
| tm_app : tm -> tm -> tm
| tm_let : string -> tm -> tm -> tm
| tm_fork : tm -> tm
| tm_give : tm -> tm -> tm
| tm_take : tm -> tm
| tm_mkch : ty -> tm
.

Declare Custom Entry chstlc.
Notation "<{ e }>" := e (e custom chstlc at level 99).
Notation "( x )" := x (in custom chstlc at level 99).
Notation "x" := x (in custom chstlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom chstlc at level 50, right associativity).
Notation "'Ch' T" := (Ty_Ch T) (in custom chstlc at level 55).
Notation "x y" := (tm_app x y) (in custom chstlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom chstlc at level 90, x at level 99,
                     t custom chstlc at level 99,
                     y custom chstlc at level 99,
                     left associativity).
Notation "'newCh' T" := (tm_mkch T) (in custom chstlc at level 91,
                                        T custom chstlc at level 99).
Notation "'take' c" := (tm_take c) (in custom chstlc at level 91,
                                       c custom chstlc at level 99).
Notation "'give' c v" := (tm_give c v) (in custom chstlc at level 91,
                                           c custom chstlc at level 99,
                                           v custom chstlc at level 99).
Notation "'fork' f" := (tm_fork f) (in custom chstlc at level 91,
                                       f custom chstlc at level 99).
Coercion tm_var : string >-> tm.
Notation "'Unit'" := Ty_Unit (in custom chstlc at level 0).
Notation "'let' x = t 'in' y" :=
  (tm_let x t y) (in custom chstlc at level 89,
                    x custom chstlc at level 99,
                    t custom chstlc at level 99,
                    y custom chstlc at level 99,
                    left associativity).
Notation "'unit'" := tm_unit (in custom chstlc at level 0).

Inductive value : tm -> Prop :=
| v_unit : value <{unit}>
| v_abs : forall x T y, value <{\x : T, y}>
(* | v_var : forall x, value (tm_var x) *)
.

Global Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom chstlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb x y then s else t
  | <{\y:T, t1}> =>
      if eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      tm_app <{[x:=s]t1}> <{[x:=s]t2}>
  | <{unit}> => <{unit}>
  (* let *)
  | <{let y=t1 in t2}> =>
    if eqb x y then <{let y=[x:=s]t1 in t2 }>
    else <{let y=[x:=s]t1 in [x:=s]t2}>
  | <{ newCh T }> => t
  | <{ take c }> => <{ take [x:=s]c }>
  | tm_give c v => <{ give [x:=s]c [x:=s]v }>
  | <{ fork f }> => <{ fork [x:=s]f }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom chstlc).

Inductive ECtx : Type :=
| EC_Hole : ECtx
| EC_App1 : ECtx -> tm -> ECtx
| EC_App2 : tm -> ECtx -> ECtx
| EC_Let : string -> ECtx -> tm -> ECtx
| EC_Take : ECtx -> ECtx
| EC_Give1 : ECtx -> tm -> ECtx
| EC_Give2 : tm -> ECtx -> ECtx
| EC_Fork : ECtx -> ECtx
.

Inductive fillCtx : ECtx -> tm -> tm -> Prop :=
| Fill_Hole : forall t, fillCtx EC_Hole t t
| Fill_App1 : forall t E result t2, fillCtx E t result -> fillCtx (EC_App1 E t2) t (tm_app result t2)
| Fill_App2 : forall t E result v1, value v1 -> fillCtx E t result -> fillCtx (EC_App2 v1 E) t (tm_app v1 result)
| Fill_Let : forall s t E result t2, fillCtx E t result -> fillCtx (EC_Let s E t2) t (tm_let s result t2)
| Fill_Take : forall t E result, fillCtx E t result -> fillCtx (EC_Take E) t (tm_take result)
| Fill_Give1 : forall t E result t2, fillCtx E t result -> fillCtx (EC_Give1 E t2) t (tm_give result t2)
| Fill_Give2 : forall t E result v1, value v1 -> fillCtx E t result -> fillCtx (EC_Give2 v1 E) t (tm_give v1 result)
| Fill_Fork : forall t E result, fillCtx E t result -> fillCtx (EC_Fork E) t (tm_fork result)
.

Global Hint Constructors fillCtx : core.

Inductive step : tm -> tm -> Prop :=
| S_App : forall x T t1 v2, value v2 -> step <{(\x:T, t1) v2}> <{[x:=v2]t1}>
| S_Let : forall x v1 t2, value v1 -> step <{let x = v1 in t2}> <{[x:=v1]t2}>
| S_ECtx : forall t1 t2 C result1 result2, step t1 t2 -> fillCtx C t1 result1 -> fillCtx C t2 result2 -> step result1 result2
.

Global Hint Constructors step : core.

Definition x : string := "x".
Definition idUnit := <{ \x:Unit, x }>.
Definition idUU := <{ \x:Unit -> Unit, x }>.

Example step_example1 :
  step <{ idUU idUnit }> idUnit.
Proof.
  constructor. constructor.
Qed.

Example step_example2 :
  step (tm_app (tm_app idUU idUnit) (tm_app idUnit tm_unit))
       (tm_app idUnit (tm_app idUnit tm_unit)).
Proof.
  econstructor; econstructor; econstructor.
Qed.

Example step_example3 :
  step (tm_app idUnit (tm_app idUnit tm_unit)) (tm_app idUnit tm_unit).
Proof.
  econstructor; econstructor; econstructor.
Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '⊢' t '∈' T"
            (at level 101,
             t custom chstlc, T custom chstlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x T, Gamma x = Some T -> Gamma ⊢ x ∈ T
| T_Unit : forall Gamma, Gamma ⊢ unit ∈ Unit
| T_Abs : forall Gamma x T1 T2 t, (x |-> T1; Gamma) ⊢ t ∈ T2 -> Gamma ⊢ <{ \x: T1, t }> ∈ (Ty_Arrow T1 T2)
| T_App : forall Gamma t1 t2 T1 T2, Gamma ⊢ t1 ∈ (Ty_Arrow T1 T2) -> Gamma ⊢ t2 ∈ T1 -> Gamma ⊢ t1 t2 ∈ T2
| T_Let : forall Gamma x T1 T2 t1 t2, Gamma ⊢ t1 ∈ T1 -> (x |-> T1; Gamma) ⊢ t2 ∈ T2 -> Gamma ⊢ let x = t1 in t2 ∈ T2
| T_NewCh : forall Gamma T, Gamma ⊢ newCh T ∈ Ch T
| T_Take : forall Gamma c T, (Gamma ⊢ c ∈ Ch T) -> Gamma ⊢ take c ∈ T
| T_Give : forall Gamma c t T, (Gamma ⊢ c ∈ Ch T) -> (Gamma ⊢ t ∈ T) -> has_type Gamma (tm_give c t) Ty_Unit
| T_Fork : forall Gamma f T, has_type Gamma f (Ty_Arrow Ty_Unit T) -> Gamma ⊢ (fork f) ∈ Unit
where "Gamma '⊢' t '∈' T" := (has_type Gamma t T).

Global Hint Constructors has_type : core.

Lemma canonical_lambda : forall t T1 T2,
    empty ⊢ t ∈ (Ty_Arrow T1 T2) -> value t -> exists x t', t = <{ \x:T1, t' }>.
Proof.
  intros. inversion H0; subst.
  - inversion H.
  - exists x0, y. inversion H. reflexivity.
  (* - inversion H. inversion H3. *)
Qed.

Lemma unique_type : forall Gamma t T1 T2, Gamma ⊢ t ∈ T1 -> Gamma ⊢ t ∈ T2 -> T1 = T2.
Proof.
  intros. generalize dependent T2. induction H; intros.
  - inversion H0. subst. rewrite H in H3. inversion H3. reflexivity.
  - inversion H0. reflexivity.
  - inversion H0. subst. apply IHhas_type in H6. rewrite H6. reflexivity.
  - inversion H1; subst. inversion H1; subst. apply IHhas_type1 in H6. inversion H6; subst. reflexivity.
  - inversion H1; subst. apply IHhas_type1 in H7; subst. apply IHhas_type2 in H8. assumption.
  - inversion H0. reflexivity.
  - inversion H0; subst. apply IHhas_type in H3. inversion H3. reflexivity.
  - inversion H1. reflexivity.
  - inversion H0. reflexivity.
Qed.

Theorem progress : forall t T, empty ⊢ t ∈ T ->
                                  value t \/ (exists t', step t t')
                                                  \/ exists E, (exists T, fillCtx E (tm_mkch T) t) \/
                                                           (exists c, fillCtx E (tm_take c) t) \/
                                                           (exists c v, fillCtx E (tm_give c v) t) \/
                                                           (exists f, fillCtx E (tm_fork f) t)
.
Proof.
  intros. remember empty.
  induction H; subst.
  - inversion H.
  - eauto.
  - left. constructor.
  - right. destruct IHhas_type1; auto. destruct IHhas_type2; auto.
    + apply canonical_lambda in H; auto. destruct H as (x & t' & H). subst. eauto.
    + destruct H2.
      * destruct H2. eauto 20.
      * right. destruct H2. destruct H2 as [[] |[[] |[[] |[] ]]];  eexists; [left | right; left | right; right; left | right; right; right]; eauto.
        { destruct H2. eauto. }
    + destruct H1. destruct H1. left. eauto.
      destruct H1. right. destruct H1 as [[] |[[] |[[] |[] ]]]; eexists; [left | right; left | right; right; left | right; right; right]; eauto.
      { destruct H1. eauto. }
  - right. destruct IHhas_type1; auto.
    + left. eauto.
    +  destruct H1 as [[]|]. left. eauto. right. destruct H1. destruct H1 as [[] |[[] |[[] |[] ]]]; eexists; [left | right; left | right; right; left | right; right; right]; eauto.
       { destruct H1. eauto. }
  - right. right. eauto.
  - right. right. eauto.
  - right. right. eauto 20.
  - right. right. eauto 20.
Qed.

Theorem weakening : forall Gamma Gamma' t T, inclusion Gamma Gamma' -> Gamma ⊢ t ∈ T -> Gamma' ⊢ t ∈ T.
Proof.
  intros. generalize dependent Gamma'. induction H0; intros; eauto using inclusion_update.
Qed.

Theorem weakening_empty : forall Gamma t T, empty ⊢ t ∈ T -> Gamma ⊢ t ∈ T.
Proof. intros. eapply weakening; eauto. unfold inclusion. intros. inversion H0. Qed.

Theorem subst_preservation : forall Gamma x t1 t2 T1 T2, x |-> T1; Gamma ⊢ t2 ∈ T2 -> (empty ⊢ t1 ∈ T1) -> Gamma ⊢ [x:=t1]t2 ∈ T2.
Proof.
  intros. generalize dependent Gamma. generalize dependent T2. generalize dependent t1. induction t2; intros.
  - destruct (eqb_spec x0 s).
    + subst. simpl. rewrite eqb_refl. inversion H. subst. rewrite update_eq in H3. inversion H3. subst.
      apply weakening_empty. assumption.
    + simpl. inversion H. subst. rewrite update_neq in H3. rewrite <- eqb_neq in n. rewrite n. auto. auto.
  - simpl. destruct (eqb_spec x0 s).
    + subst. inversion H. subst. rewrite update_shadow in H6. eauto.
    + inversion H. subst. constructor. apply IHt2. assumption. rewrite update_permute; auto.
  - simpl. inversion H. auto.
  - inversion H. subst. eapply IHt2_1 in H4; eauto. eapply IHt2_2 in H6; eauto.
    simpl. eauto.
  - simpl. destruct (eqb_spec x0 s).
    + inversion H. subst. eapply IHt2_1 in H6; eauto. econstructor. eauto.
      rewrite update_shadow in H7. assumption.
    + inversion H. subst. eapply IHt2_1 in H6; eauto. econstructor. eauto. rewrite update_permute in H7.
      eapply IHt2_2 in H7; eauto. assumption.
  - inversion H. simpl. eauto.
  - inversion H. simpl. eauto.
  - inversion H. simpl. eauto.
  - inversion H. simpl. eauto.
Qed.

Theorem subterm_type : forall C Gamma t result T, fillCtx C t result -> Gamma ⊢ result ∈ T ->
                                             exists T', Gamma ⊢ t ∈ T'.
Proof.
  induction C; intros; inversion H; subst; inversion H0; subst; eauto.
Qed.

Theorem ctx_preservation :
  forall C Gamma t1 t2 result1 result2 T1 T2, Gamma ⊢ t1 ∈ T1 -> Gamma ⊢ t2 ∈ T1 ->
                                   fillCtx C t1 result1 -> fillCtx C t2 result2 ->
                                   Gamma ⊢ result1 ∈ T2 -> Gamma ⊢ result2 ∈ T2.
Proof.
  induction C; intros.
  - inversion H1; subst. inversion H2; subst. eapply unique_type in H; eauto. subst. assumption.
  - inversion H1; subst. inversion H3; subst. inversion H2; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
  - inversion H1; subst. inversion H2; subst. inversion H3; subst. eauto.
Qed.

Theorem preservation : forall t t' T, empty ⊢ t ∈ T -> step t t' -> empty ⊢ t' ∈ T.
Proof.
  intros. generalize dependent T. remember empty. induction H0; intros; subst.
  - inversion H0; subst. inversion H4; subst. eapply subst_preservation; eauto.
  - inversion H0; subst. eapply subst_preservation; eauto.
  - assert (H2' := H2). eapply subterm_type in H2; eauto. destruct H2. assert (H2'' := H2).
    apply IHstep in H2. eapply ctx_preservation in H2'. eapply H2'. eauto. eapply H2. eauto. eauto.
Qed.
