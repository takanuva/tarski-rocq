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

  (* We want to define, for an arbitrary family of sets A: Set and B: A -> Set,
     what would look like the following inductive-recursive type:

       Inductive CODE: Set :=
         | NAT: CODE
         | PI (a: CODE) (b: T x -> CODE): CODE
         | IDX: CODE
         | LFT (a: A): CODE

       with T: CODE -> Set :=
         T NAT := nat;
         T (PI a b) := forall x: T a, T (b x);
         T IDX := A;
         T (LFT a) := B a.

     We will first define something akin to this type, but by using small
     induction-recursion, such that the inductive part will be larger than the
     codomain of the recursive part (i.e., as we are producing sets, it will
     live in Type). We start with our constructors. *)

  Variant branch: Set :=
    | U_nat
    | U_pi
    | U_idx
    | U_lft.

  Definition TARSKI: Sig :=
    sigma branch (fun b: branch =>
      match b with
      (* NAT: CODE, returning nat. *)
      | U_nat =>
        iota nat
      (* PI (a: CODE) (b: T x -> CODE): CODE, returning (x: T a) -> T (b x). *)
      | U_pi =>
        delta unit (fun Ta: unit -> Set =>
          delta (Ta tt) (fun Tb: Ta tt -> Set =>
            iota (forall a: Ta tt, Tb a)))
      (* IDX: CODE, returning A. *)
      | U_idx =>
        iota A
      (* LFT (a: A): CODE, returning B a. *)
      | U_lft =>
        sigma A (fun a: A =>
          iota (B a))
      end).

  (* From the signature, and using the impredicative least fixpoint, we may
     construct the inductive and the recursive part of the definition. *)

  Local Definition IND: Type :=
    E TARSKI (total (muE TARSKI)) projT1.

  Local Definition REC: IND -> Set :=
    F TARSKI (total (muE TARSKI)) projT1.

  (* As the fixpoint is a functor of O -> Set, we need to pack the inductive
     type together with its resulting type when using it as a subterm; we use
     the definition of the initial algebra to do so. *)

  Definition embed (x: IND): total (muE TARSKI) :=
    existT (REC x) (inE TARSKI (exist x eq_refl)).

  (* Now we can easily define the four constructors for IND. *)

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

  (* Since we're relying on a Church-encoded fixpoint, we define a relevant
     predicate to keep track on how the terms are constructed, in order to
     derive an induction principle for IND (and REC). This is no different from
     how one would proceed to derive induction for, e.g., Church-encoded nat. *)

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

  (* The type of codes for the universe is a large inductive type in Set, so we
     rely on impredicativity for its existence (Rocq would reject this code if
     we do not run it with the -impredicative-set flag). Of course, elimination
     for large inductive types in Set is quite restricted: we can't ever remove
     this IND back from CODE once squashed. Turns out it doesn't matter. *)

  Unset Elimination Schemes.

  Inductive CODE: Set :=
    | shrink (x: IND) (ok: canonical x).

  Set Elimination Schemes.

  (* Although we can't eliminate from CODE directly into Set, IND or anything
     large, we can still eliminate into small types, so we can make a projection
     to get the constructor (the branch) used to build this code. *)

  Definition get_branch (c: CODE): branch :=
    let (x, ok) := c in projT1 x.

  (* We can also eliminate from CODE to CODE, as it is itself small, so if the
     branch for some code is U_pi, we extract the first subterm (i.e., the a in
     PI' a b), along with its proof of canonicity. *)

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
      exact (shrink a ok).
    - exfalso.
      simpl in H.
      inversion H.
    - exfalso.
      simpl in H.
      inversion H.
  Defined.

  (* Getting the second subterm is trickier, as, for PI a b, it's really a
     function T a -> CODE. Again, we can't eliminate from a code directly to get
     the type it produces, and there's even a bigger problem: we don't even have
     injectivity of constructors for codes! So, in order to make the proof go
     through, we make a relevant relation between codes and sets stating that we
     indeed have the right type. *)

  Structure right_type (c: CODE) (T: Set): Type := witness {
    injectivity:
      (* Note: this injectivity may NOT be true in general! *)
      forall a H, c = shrink a H -> T = REC a
  }.

  (* We also have a small transport function, cast, that says that if T is the
     right type for (shrink a ok), and we have a T, we also have a REC a, by
     properly specializing the injectivity assumption to reflexivity. *)

  Definition cast:
    forall a: IND,
    forall ok: canonical a,
    forall T: Set,
    forall H: right_type (shrink a ok) T,
    forall x: T, REC a.
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
    (* We rely on UIP here... *)
    dependent destruction H; simpl.
    reflexivity.
  Qed.

  (* We now have enough information to extract the second subterm of a pi type,
     as a function T -> CODE for any type T, as long as it's the right type in
     regard to the first subterm. *)

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
    exact (shrink (b y) (ok_b y)).
  Defined.

  (* Of course, we also need to eliminate from LFT' a to get back the element,
     but since it's small, there's no problem in that. *)

  Definition get_inner:
    forall c: CODE,
    forall H: U_lft = get_branch c,
    A.
  Proof.
    intros.
    destruct c.
    now destruct ok.
  Defined.

  (* Since we know we can eliminate from a code into its subterms, namely only
     used for pi types, we can define a subterm relation and prove through the
     accessibility predicate that it is indeed well-founded. Given how we may
     construct codes, there's never an infinite descending chain of subterms. *)

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
    (* We can eliminate from CODE to construct a mere proposition! *)
    destruct c.
    (* Which means we may perform induction on the proof of canonicity. *)
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

  (* We cannot yet define a constructor for pi types in CODE, as we cannot yet
     extract the recursive type from it. Indeed, this function would have type:

       PI: forall a: CODE, (??? -> CODE) -> CODE.

     How to get the type generated by a? Of course, we could use any T and check
     it's correct with right_type, but we'll do that later. For now, we rely on
     the fact that the accessibility predicate is a subsingleton proposition,
     thus capable of eliminating into any large types, to sketch a recursion
     principle for CODE. An ugly hack, but it works! *)

  Lemma CODE_prim_rect:
    forall P: CODE -> Type,
    forall f1: P (shrink NAT' canonical_nat),
    forall f2: (forall x: CODE,
                forall H: U_pi = get_branch x,
                P (left_child x H) ->
                (forall T X y, P (right_child x H T X y)) ->
                P x),
    forall f3: P (shrink IDX' canonical_idx),
    forall f4: (forall a: A, P (shrink (LFT' a) (canonical_lft a))),
    forall x: CODE,
    P x.
  Proof.
    intros.
    (* All subterms for x are accessible; do induction on them. *)
    assert (Acc subterm x) by now apply subterm_acc.
    induction H; clear H.
    (* We can't yet destruct x, but we may check it's code! *)
    remember (get_branch x) as b.
    destruct b.
    - (* This is a simple base case. *)
      enough (x = shrink NAT' canonical_nat).
      + rewrite H.
        apply f1.
      + destruct x.
        now destruct ok.
    - (* The somewhat tricky case, as we can't destruct x to produce a type P x,
         but we may keep going with our small projections. *)
      apply f2 with Heqb.
      + apply X.
        constructor.
      + intros.
        apply X.
        constructor.
    - (* Same as above. *)
      enough (x = shrink IDX' canonical_idx).
      + rewrite H.
        apply f3.
      + destruct x.
        now destruct ok.
    - (* Same as above, but with extra data. *)
      set (a := get_inner x Heqb).
      enough (x = shrink (LFT' a) (canonical_lft a)).
      + rewrite H.
        apply f4.
      + destruct x.
        now destruct ok.
  Qed.

  (* We are now ready to show that the squashing constructor, shrink, is indeed
     an isomorphism: our goal is not to extract the IND inside of it, we can't,
     but rather to reconstruct it almost exactly by checking the details that
     got leaked. *)

  Local Notation GOAL c :=
    (* For some code c, we produce:
       - x, an IND;
       - a proof that x is canonical;
       - a proof that c is injective and indeed contains x. *)
    { x: IND & canonical x & forall a H, c = shrink a H -> x = a }.

  (* From this goal, we can pick the inductive component of the type, along with
     its proof of canonicity. *)

  Definition get_ind {c: CODE} (x: GOAL c): IND :=
    let (a, ok_a, H) := x in a.

  Definition get_canonical {c: CODE} (x: GOAL c): canonical (get_ind x) :=
    let (a, ok_a, H) return canonical (get_ind x) := x in ok_a.

  (* The main component: from any code, we can rebuild its elements, while
     recursively also keeping track that the constructor is injective. *)

  Definition rebuild:
    forall x: CODE,
    GOAL x.
  Proof.
    intros.
    (* Follow our hacky recursion. *)
    induction x using CODE_prim_rect.
    - (* A base case, we can't possibly construct a code any other way. *)
      exists NAT'; intros.
      + constructor.
      + (* Again, shrink is not necessarily injective, but from it we may
           extract the branch taken, U_nat, in which case, a can't possibly be
           any different from NAT'. *)
        apply (f_equal get_branch) in H0; simpl in H0.
        now destruct H.
    - (* We have reconstructed our first subterm. *)
      destruct IHx as (a, ok_a, ?H).
      (* Which means we indeed know its right type, and the proof of injectivity
         was given by recursion as well. *)
      set (H1 a H X := f_equal REC (H0 a H X)).
      set (H2 := witness (left_child x H) (REC a) H1).
      (* Which means we can simplify the second subterm by feeding to it the
         correct type. *)
      specialize (X (REC a) H2).
      (* Great, now we can rebuild the code! *)
      exists (PI' a (fun y => get_ind (X y))); intros.
      + constructor; intros.
        * assumption.
        * apply get_canonical.
      + (* We have to show that if we have injectivity on the two subterms, we
           preserve it. Right, this is true, but we can't ever extract correctly
           the second subterm, which is a function. We can rebuild its results,
           so it's only equal pointwise... *)
        subst.
        destruct H3; try easy.
        simpl in *.
        assert (a = a0).
        * apply (H0 _ _ eq_refl).
        * subst; f_equal.
          (* ...thus we need to rely on functional extensionality to prove that
             the original and the reconstructed subterms are the same. *)
          extensionality y.
          destruct (X y) as (x, ok_x, ?H); simpl.
          rewrite cast_simpl in H4.
          now apply H4 with (ok_b y).
    - (* Just as above. *)
      exists IDX'; intros.
      + constructor.
      + apply (f_equal get_branch) in H0; simpl in H0.
        now destruct H.
    - (* Just as above. *)
      exists (LFT' a); intros.
      + constructor.
      + pose proof H0.
        apply (f_equal get_branch) in H0; simpl in H0.
        destruct H; try easy.
        now inversion H1.
  Qed.

  (* Finally, we can define the interpretation T for codes: we will rebuild the
     inductive part, and get the recursive part for it then. *)

  Definition T (c: CODE): Set :=
    REC (get_ind (rebuild c)).

  (* We may prove that this reconstruction works: we get the expected type. *)

  Lemma T_shrink:
    forall a ok,
    T (shrink a ok) = REC a.
  Proof.
    intros.
    unfold T.
    destruct rebuild; simpl.
    f_equal.
    now apply e with ok.
  Qed.

  (* We can now make the constructors for CODE itself: NAT, PI, IDX, and LFT,
     proving how they behave in regard to T. *)

  Definition NAT: CODE :=
    shrink NAT' canonical_nat.

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
    shrink (PI' (get_ind a') (fun y => get_ind (b' y)))
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
    shrink IDX' canonical_idx.

  Lemma T_IDX:
    T IDX = A.
  Proof.
    unfold T.
    destruct (rebuild IDX); simpl.
    specialize (e _ _ eq_refl); subst.
    reflexivity.
  Qed.

  Definition LFT (a: A): CODE :=
    shrink (LFT' a) (canonical_lft a).

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

(* All the required machinery is done! *)

Arguments T {A} {B}.
Arguments NAT {A} {B}.
Arguments PI {A} {B}.
Arguments IDX {A} {B}.
Arguments LFT {A} {B}.

(* An an example of application, following Dybjer and Palmgren, we'll define an
   internal, nat-indexed, hierarchy of universes following the type of codes
   constructed above. First, we define a universe as a family of sets, which we
   identify with the type of codes over this family (recall that IDX and LFT
   were parametrized to some abstract family earlier). *)

Structure universe: Type := universe_mk {
  uni_idx: Set;
  uni_lft: uni_idx -> Set;
  uni_code := CODE uni_idx uni_lft
}.

Coercion uni_code: universe >-> Sortclass.

(* We also say that a universe U is a subtype of a universe V if:
   - there's a code SUB in V such that T SUB = U;
   - for any code x in U, there's a code EMB x in V such that T (EMB x) = T x.

   Furthermore, this property is transitive. *)

Structure subuniverse (U: universe) (V: universe): Set := {
  SUB: V;
  EMB: U -> V;
  T_SUB: T SUB = U;
  T_EMB: forall x, T (EMB x) = T x
}.

Lemma subuniverse_trans:
  forall U V W,
  subuniverse U V -> subuniverse V W -> subuniverse U W.
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

(* We produce now a family of sets by induction over some number n, such that:

    A n: Set

      A 0       = False
      A (1 + n) = CODE (A n) (B n)

    B n: A n -> Set

      B 0       = False_rect Set
      B (1 + n) = T (A n) (B n) *)

Local Fixpoint FAM (n: nat): { A: Set & A -> Set } :=
  match n with
  | 0 =>
    existT (False: Set) (False_rect Set)
  | S k =>
    existT (CODE (projT1 (FAM k)) (projT2 (FAM k))) T
  end.

Local Definition A (n: nat): Set :=
  projT1 (FAM n).

Local Definition B (n: nat): A n -> Set :=
  projT2 (FAM n).

(* For every natural number n, there's a universe U n over the family (A n) and
   (B n). Also, there's a universe Uw that includes codes for any universe U n,
   for any n. Note that (U n: Set) = A (1 + n). *)

Definition U (n: nat): universe :=
  universe_mk (A n) (B n).

Definition Uw: universe :=
  universe_mk { n: nat & U n } (fun p => T (projT2 p)).

(* Just a small digression, we need recursion on the proof that n < m... *)

Lemma le_rec:
  forall n,
  forall P: nat -> Set,
  P n ->
  (forall m, n <= m -> P m -> P (S m)) ->
  forall m, n <= m -> P m.
Proof.
  intros.
  remember (m - n) as i.
  replace m with (i + n) by lia.
  clear H1 Heqi m.
  induction i; simpl.
  - assumption.
  - apply H0.
    + lia.
    + assumption.
Qed.

(* Ok, back on track; every universe U n is a subuniverse of U (1 + n). *)

Lemma next_level:
  forall n,
  subuniverse (U n) (U (1 + n)).
Proof.
  intros.
  (* In U (1 + n), IDX is a code for U n, and LFT embeds codes from U n. *)
  exists IDX LFT; intros.
  - apply T_IDX.
  - apply T_LFT.
Qed.

(* Cumulativity applies. For every n < m, U n is a subuniverse of U m. *)

Lemma cumulative:
  forall {n m},
  n < m ->
  subuniverse (U n) (U m).
Proof.
  induction 1.
  - apply next_level.
  - apply subuniverse_trans with (U m).
    + assumption.
    + apply next_level.
Qed.

(* Finally, of course, every U n is a subuniverse of Uw. *)

Lemma largest:
  forall n,
  subuniverse (U n) Uw.
Proof.
  intros.
  (* Note, to have a code for U n in Uw, we rely on the fact that it contains
     codes from subuniverses, and that there is a code for U n in U (1 + n). *)
  eexists (LFT (existT (1 + n) IDX)) (fun x: U n => LFT (existT n x)).
  - rewrite T_LFT; simpl.
    rewrite T_IDX; simpl.
    reflexivity.
  - intros.
    rewrite T_LFT; simpl.
    reflexivity.
Qed.
