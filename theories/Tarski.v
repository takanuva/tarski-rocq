(******************************************************************************)
(*      Copyright (c) 2026 - Paulo Torrens <paulotorrens AT gnu DOT org>      *)
(******************************************************************************)

From Coq Require Import Lia.
From Coq Require Import Equality.
From Coq Require Import FunctionalExtensionality.
From Local Require Import InductionRecursion.

Set Primitive Projections.

Arguments projT1 {A} {P}.
Arguments projT2 {A} {P}.
Arguments exist {A} {P}.
Arguments existT {A} {P}.

Section Family.

  Variable A: Set.
  Variable B: A -> Set.

  Variant branch: Set :=
    | U_nat
    | U_pi
    | U_idx
    | U_lft.

  Definition TARSKI: @Sig Set :=
    sigma branch (fun b =>
      match b with
      | U_nat =>
        iota nat
      | U_pi =>
        delta unit (fun ElA: unit -> Set =>
          delta (ElA tt) (fun ElB: ElA tt -> Set =>
            iota (forall a: ElA tt, ElB a)))
      | U_idx =>
        iota A
      | U_lft =>
        sigma A (fun a: A =>
          iota (B a))
      end).

  Local Definition IND: Type :=
    E TARSKI (total (muE TARSKI)) projT1.

  Local Definition REC: IND -> Set :=
    F TARSKI (total (muE TARSKI)) projT1.

  Definition embed (x: IND): total (muE TARSKI) :=
    existT (REC x) (inE TARSKI (exist x eq_refl)).

  Definition NAT': IND :=
    existT U_nat tt.

  Definition PI' (a: IND) (b: REC a -> IND): IND :=
    existT U_pi
      (existT (fun _ => embed a)
        (existT (fun x => embed (b x))
          tt)).

  Definition IDX': IND :=
    existT U_idx tt.

  Definition LFT' (a: A): IND :=
    existT U_lft
      (existT a tt).

  Inductive canonical: IND -> Type :=
    | canonical_nat:
      canonical NAT'
    | canonical_pi:
      forall a: IND,
      forall b: REC a -> IND,
      forall ok_a: canonical a,
      forall ok_b: (forall x, canonical (b x)),
      canonical (PI' a b)
    | canonical_idx:
      canonical IDX'
    | canonical_lft:
      forall a: A,
      canonical (LFT' a).

  Unset Elimination Schemes.

  Inductive CODE: Set :=
    | squash (x: IND) (ok: canonical x).

  Set Elimination Schemes.

  Definition get_branch (c: CODE): branch :=
    let (x, ok) := c in projT1 x.

  Definition left_child:
    forall c: CODE,
    U_pi = get_branch c ->
    CODE.
  Proof.
    intros.
    destruct c.
    destruct ok.
    - exfalso.
      simpl in H.
      inversion H.
    - clear H.
      exact (squash a ok).
    - exfalso.
      simpl in H.
      inversion H.
    - exfalso.
      simpl in H.
      inversion H.
  Defined.

  Structure right_type (c: CODE) (T: Set): Type := witness {
    injectivity:
      forall a H, c = squash a H -> T = REC a
  }.

  Definition cast:
    forall a: IND,
    forall ok: canonical a,
    forall T: Set,
    forall H: right_type (squash a ok) T,
    forall x: T,
    REC a.
  Proof.
    intros.
    destruct H as (?H).
    specialize (H _ _ eq_refl).
    clear - H x.
    now subst.
  Defined.

  Arguments cast {a} {ok} {T}: simpl never.

  Lemma cast_simpl:
    forall a ok X x,
    @cast a ok (REC a) X x = x.
  Proof.
    intros.
    destruct X as (f).
    unfold cast; simpl.
    generalize (f a ok eq_refl) as H.
    dependent destruction H; simpl.
    reflexivity.
  Qed.

  Definition right_child:
    forall c: CODE,
    forall H: U_pi = get_branch c,
    forall T: Set,
    forall X: right_type (left_child c H) T,
    forall x: T, CODE.
  Proof.
    intros.
    destruct c.
    destruct ok; try easy.
    simpl in *.
    set (y := cast X x).
    exact (squash (b y) (ok_b y)).
  Defined.

  Definition get_inner:
    forall c: CODE,
    forall H: U_lft = get_branch c,
    A.
  Proof.
    intros.
    destruct c.
    now destruct ok.
  Defined.

  Inductive subterm: CODE -> CODE -> Prop :=
    | subterm_pi_left:
      forall c H,
      subterm (left_child c H) c
    | subterm_pi_right:
      forall c H T X x,
      subterm (right_child c H T X x) c.

  Lemma subterm_acc:
    forall c: CODE,
    Acc subterm c.
  Proof.
    intros.
    destruct c.
    induction ok.
    - constructor; intros.
      inversion H; easy.
    - constructor; intros.
      inversion_clear H0.
      + simpl.
        assumption.
      + simpl in X |- *.
        apply H.
    - constructor; intros.
      inversion H; easy.
    - constructor; intros.
      inversion H; easy.
  Defined.

  Lemma CODE_prim_rect:
    forall P: CODE -> Type,
    forall f1: P (squash NAT' canonical_nat),
    forall f2: (forall x: CODE,
                forall H: U_pi = get_branch x,
                P (left_child x H) ->
                (forall T X y, P (right_child x H T X y)) ->
                P x),
    forall f3: P (squash IDX' canonical_idx),
    forall f4: (forall a: A, P (squash (LFT' a) (canonical_lft a))),
    forall x: CODE,
    P x.
  Proof.
    intros.
    assert (Acc subterm x) by now apply subterm_acc.
    induction H; clear H.
    remember (get_branch x) as b.
    destruct b.
    - enough (x = squash NAT' canonical_nat).
      + rewrite H.
        apply f1.
      + destruct x.
        now destruct ok.
    - apply f2 with Heqb.
      + apply X.
        constructor.
      + intros.
        apply X.
        constructor.
    - enough (x = squash IDX' canonical_idx).
      + rewrite H.
        apply f3.
      + destruct x.
        now destruct ok.
    - set (a := get_inner x Heqb).
      enough (x = squash (LFT' a) (canonical_lft a)).
      + rewrite H.
        apply f4.
      + destruct x.
        now destruct ok.
  Qed.

  Local Notation GOAL c :=
    { x: IND & canonical x & forall a H, c = squash a H -> x = a }.

  Definition get_ind {c: CODE} (x: GOAL c): IND :=
    let (a, ok_a, H) := x in a.

  Definition get_canonical {c: CODE} (x: GOAL c): canonical (get_ind x) :=
    let (a, ok_a, H) return canonical (get_ind x) := x in ok_a.

  Definition rebuild:
    forall x: CODE,
    GOAL x.
  Proof.
    intros.
    induction x using CODE_prim_rect.
    - exists NAT'; intros.
      + constructor.
      + apply (f_equal get_branch) in H0; simpl in H0.
        now destruct H.
    - destruct IHx as (a, ok_a, ?H).
      set (H1 a H X := f_equal REC (H0 a H X)).
      set (H2 := witness (left_child x H) (REC a) H1).
      specialize (X (REC a) H2).
      exists (PI' a (fun y => get_ind (X y))); intros.
      + constructor; intros.
        * assumption.
        * apply get_canonical.
      + subst.
        destruct H3; try easy.
        simpl in *.
        assert (a = a0).
        * apply (H0 _ _ eq_refl).
        * subst; f_equal.
          extensionality y.
          destruct (X y) as (x, ok_x, ?H); simpl.
          rewrite cast_simpl in H4.
          now apply H4 with (ok_b y).
    - exists IDX'; intros.
      + constructor.
      + apply (f_equal get_branch) in H0; simpl in H0.
        now destruct H.
    - exists (LFT' a); intros.
      + constructor.
      + pose proof H0.
        apply (f_equal get_branch) in H0; simpl in H0.
        destruct H; try easy.
        now inversion H1.
  Qed.

  Definition T (c: CODE): Set :=
    REC (get_ind (rebuild c)).

  Lemma T_squash:
    forall a ok,
    T (squash a ok) = REC a.
  Proof.
    intros.
    unfold T.
    destruct rebuild; simpl.
    f_equal.
    now apply e with ok.
  Qed.

  Definition NAT: CODE :=
    squash NAT' canonical_nat.

  Lemma T_NAT:
    T NAT = nat.
  Proof.
    unfold T.
    destruct (rebuild NAT); simpl.
    specialize (e _ _ eq_refl); subst.
    reflexivity.
  Qed.

  Definition PI (a: CODE) (b: T a -> CODE): CODE :=
    let a' := rebuild a in
    let b' y := rebuild (b y) in
    squash (PI' (get_ind a') (fun y => get_ind (b' y)))
      (canonical_pi _ _ (get_canonical a') (fun y => get_canonical (b' y))).

  Lemma T_PI:
    forall a b,
    T (PI a b) = (forall x: T a, T (b x)).
  Proof.
    intros.
    unfold T.
    destruct (rebuild (PI a b)); simpl.
    specialize (e _ _ eq_refl); subst.
    reflexivity.
  Qed.

  Definition IDX: CODE :=
    squash IDX' canonical_idx.

  Lemma T_IDX:
    T IDX = A.
  Proof.
    unfold T.
    destruct (rebuild IDX); simpl.
    specialize (e _ _ eq_refl); subst.
    reflexivity.
  Qed.

  Definition LFT (a: A): CODE :=
    squash (LFT' a) (canonical_lft a).

  Lemma T_LFT:
    forall a,
    T (LFT a) = B a.
  Proof.
    intros.
    unfold T.
    destruct (rebuild (LFT a)); simpl.
    specialize (e _ _ eq_refl); subst.
    reflexivity.
  Qed.

End Family.

Arguments T {A} {B}.
Arguments NAT {A} {B}.
Arguments PI {A} {B}.
Arguments IDX {A} {B}.
Arguments LFT {A} {B}.

Structure universe: Type := universe_mk {
  uni_idx: Set;
  uni_lft: uni_idx -> Set;
  uni_code := CODE uni_idx uni_lft
}.

Coercion uni_code: universe >-> Sortclass.

Structure subuniverse (u: universe) (v: universe): Set := {
  SUB: v;
  EMB: u -> v;
  T_SUB: T SUB = u;
  T_EMB: forall x, T (EMB x) = T x
}.

Lemma subuniverse_trans:
  forall u v w,
  subuniverse u v -> subuniverse v w -> subuniverse u w.
Proof.
  intros.
  destruct H as (s1, e1, ?H, ?H).
  destruct H0 as (s2, e2, ?H, ?H).
  exists (e2 s1) (fun x => e2 (e1 x)); intros.
  - rewrite H2, H.
    reflexivity.
  - rewrite H2, H1.
    reflexivity.
Qed.

Fixpoint FAM (n: nat): { X: Set & X -> Set } :=
  match n with
  | 0 =>
    existT (False: Set) (False_rect Set)
  | S k =>
    existT (CODE (projT1 (FAM k)) (projT2 (FAM k))) T
  end.

Definition U (n: nat): universe :=
  universe_mk (projT1 (FAM n)) (projT2 (FAM n)).

Definition Uw: universe :=
  universe_mk { n: nat & U n } (fun p => T (projT2 p)).

Lemma hierarchy:
  forall {n m},
  n < m ->
  subuniverse (U n) (U m).
Proof.
  intros.
  remember (m - n - 1) as i.
  generalize dependent m.
  induction i; intros.
  - assert (m = 1 + n) by lia; subst.
    exists IDX LFT; intros.
    + apply T_IDX.
    + apply T_LFT.
  - destruct m.
    + exfalso.
      lia.
    + specialize (IHi m ltac:(lia) ltac:(lia)).
      clear H Heqi.
      destruct IHi as (s, e, ?H, ?H).
      exists (LFT s) (fun x => LFT (e x)); intros.
      * rewrite T_LFT; simpl.
        assumption.
      * rewrite T_LFT; simpl.
        apply H0.
Qed.

Lemma largest:
  forall n,
  subuniverse (U n) Uw.
Proof.
  intros.
  eexists (LFT (existT (1 + n) IDX)) (fun x: U n => LFT (existT n x)).
  - rewrite T_LFT; simpl.
    rewrite T_IDX; simpl.
    reflexivity.
  - intros.
    rewrite T_LFT; simpl.
    reflexivity.
Qed.
