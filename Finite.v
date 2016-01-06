Require Import Arith Bool List ListSet.
Require Import Omega.
Require Import ProofIrrelevance.
Require Import Program.
Require Import SetoidClass.
Set Implicit Arguments.

(* 単射 *)
Definition Injective (A B : Type) (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma injective_map_in :
 forall A B (f : A -> B),
 Injective f -> forall x xs, In x xs <-> In (f x) (map f xs).
Proof.
  intros A B f HInj.
  induction xs; split; simpl; auto; intuition.
  - subst; auto.
Qed.

Lemma injective_map_nodup :
 forall A B (f : A -> B),
 Injective f -> forall xs, NoDup xs -> NoDup (map f xs).
Proof.
  intros A B f HInj.
  induction xs.
  - constructor.
  - intro nodup.
    inversion nodup as [| ? ? Hnin Hnodup]; subst.
    simpl.
    specialize (IHxs Hnodup).
    apply NoDup_cons; try assumption.
    unfold not; intro.
    apply injective_map_in in H; auto.
Qed.

Class FiniteType (A : Type)  := 
 mkFiniteType{maxCard : nat;
              fEmbed : A -> nat;
              fInj : Injective fEmbed;
              fLim : forall x, fEmbed x < maxCard}.

Lemma eq_fintype_dec A (ft : FiniteType A) :
 forall x y : A, {x = y} + {x <> y}.
Proof.
  intros x y.
  case (eq_nat_dec (fEmbed x) (fEmbed y)); [ left | right ].
  - apply fInj; assumption.
  - congruence.
Qed.

Lemma finite_in :
 forall A (FT : FiniteType A) (x : A) xs,
 In x xs <-> In (fEmbed x) (map fEmbed xs).
Proof.
  intros A FT.
  intros x xs.
  split.
  - apply in_map.
  - induction xs.
    + simpl.
      trivial.
    + intro in_fx_faxs.
      inversion in_fx_faxs.
      * apply fInj in H.
        subst.
        apply in_eq.
      * apply in_cons.
        apply IHxs.
        assumption.
Qed.

Lemma finite_nodup :
 forall A (FT : FiniteType A) (xs : list A),
 NoDup xs <-> NoDup (map fEmbed xs).
Proof.
  intros A FT.
  induction xs.
  - split; intro; apply NoDup_nil.
  - simpl.
    split; intro nodup; apply NoDup_cons; inversion nodup; subst.
    + unfold not; intro; apply H1.
      rewrite finite_in.
      apply H.
    + apply IHxs; assumption.
    + rewrite finite_in.
      apply H1.
    + apply IHxs; assumption.
Qed.

Inductive ftype : nat -> Set :=
  | ft_n : forall n, ftype (S n)
  | ft_succ : forall n, ftype n -> ftype (S n).

Definition eq_ftype_dec : forall lim (x y : ftype lim), {x = y} + {x <> y}.
  intros lim x y.
  dependent induction x.
  - dependent destruction y.
    + left. reflexivity.
    + right. discriminate.
  - dependent destruction y.
    + right; discriminate.
    + case (IHx y); intro Hdec.
      * left; congruence.
      * right.
        intro Heq.
        inversion Heq.
        simpl_existT.
        contradiction.
Defined.

Fixpoint ftype_nat lim (x : ftype lim): nat :=
  match x with
  | ft_n n => n
  | ft_succ _ x' => ftype_nat x'
  end.

Lemma ftype_nat_limit : forall lim (x : ftype lim), ftype_nat x < lim.
Proof.
  dependent induction x.
  - constructor.
  - simpl.
    apply lt_trans with n; auto.
Qed.

Lemma ftype_nat_inj : forall lim, Injective (@ftype_nat lim).
Proof.
  unfold Injective.
  dependent induction x.
  - intros y Heq.
    dependent destruction y.
    + reflexivity.
    + exfalso.
      simpl in Heq.
      set (Hfny_lim := ftype_nat_limit y); clearbody Hfny_lim.
      rewrite Heq in *.
      apply (lt_irrefl _ Hfny_lim).
  - intros y Heq.
    dependent destruction y.
    + exfalso.
      simpl in Heq.
      set (Hfnx_lim := ftype_nat_limit x); clearbody Hfnx_lim.
      rewrite Heq in *.
      apply (lt_irrefl _ Hfnx_lim).
    + simpl in Heq.
      specialize (IHx y Heq).
      subst.
      reflexivity.
Qed.

Global Instance ftype_FT : (forall lim : nat, FiniteType (ftype lim))  :=
 {| maxCard := S lim; fEmbed := @ftype_nat lim; fInj := @ftype_nat_inj lim |}.
- intros.
  apply lt_trans with lim; auto.
  apply ftype_nat_limit.
Defined.
