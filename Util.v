Require Import Arith Bool List.
Require Import Omega.
Set Implicit Arguments.


Lemma seq_minimum : forall m n x, In x (seq n m) -> n <= x.
Proof.
  induction m.
  - simpl.
    intro; contradiction.
  - intros n x.
    simpl.
    intro.
    destruct H; try omega.
    apply IHm in H.
    omega.
Qed.

Lemma seq_nodup : forall m n, NoDup (seq n m).
Proof.
  induction m; intros; simpl; constructor.
  - unfold not; intro.
    apply seq_minimum in H.
    omega.
  - auto.
Qed.

Lemma count_occ_app A dec :
 forall (x : A) (ys zs : list A),
 count_occ dec (ys ++ zs) x = count_occ dec ys x + count_occ dec zs x.
Proof.
  induction ys; auto.
  intro zs.
  simpl.
  rewrite (IHys zs).
  destruct (dec a x); omega.
Qed.

Fixpoint scan_left (A B : Type) (f : A -> B -> A) (bs : list B) 
(a : A): list A :=
  match bs with
  | nil => a :: nil
  | b :: bs' => let a' := f a b in a :: scan_left f bs' a'
  end.

Lemma scanl_exist_tl A B :
 forall (f : A -> B -> A) bs a, exists as', scan_left f bs a = a :: as'.
Proof.
  intros.
  destruct bs.
  - simpl.
    exists nil.
    reflexivity.
  - simpl.
    exists (scan_left f bs (f a b)).
    reflexivity.
Qed.

Lemma foldl_scanl_last A B :
 forall f (bs : list B) (a : A) d,
 fold_left f bs a = last (scan_left f bs a) d.
Proof.
  induction bs as [| b bs' IHbs'].
  - intros a d.
    reflexivity.
  - intros.
    simpl fold_left.
    specialize (IHbs' (f a b) d).
    rewrite IHbs'.
    simpl scan_left.
    remember (scanl_exist_tl f bs' (f a b)) as Extl; clear HeqExtl.
    destruct Extl.
    rewrite H.
    reflexivity.
Qed.

Fixpoint rep A (a : A) (n : nat): list A :=
  match n with
  | O => nil
  | S n' => a :: rep a n'
  end.
Lemma rep_length A a n : length (@rep A a n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma rep_in A a n : forall x, In x (@rep A a n) -> a = x.
Proof.
  induction n; simpl; intuition.
Qed.

Lemma rep_count A dec a n : count_occ dec (@rep A a n) a = n.
Proof.
  induction n; auto.
  simpl.
  case (dec a a); intro; auto.
  exfalso; apply n0.
  reflexivity.
Qed.

Lemma rep_count_0 A dec a b n : a <> b -> count_occ dec (@rep A a n) b = 0.
Proof.
  intro a_ne_b.
  induction n; auto.
  simpl.
  case (dec a b); intro; try contradiction; auto.
Qed.
