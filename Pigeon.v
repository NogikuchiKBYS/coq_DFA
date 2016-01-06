Require Import Arith Bool List.
Require Import Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Require Import Finite.

Lemma PigeonHole_nat :
 forall (m : nat) (xs : list nat),
 m < length xs -> (forall x, In x xs -> x < m) -> ~ NoDup xs.
  induction m; intros xs Hlen Hlimit.
  {
    exfalso.
    destruct xs as [| x xs']; simpl in Hlen; try omega.
    refine (lt_n_0 x _).
    apply Hlimit.
    apply in_eq.
  } {
    case (in_dec eq_nat_dec m xs).
    - intro Hin.
      intro Hnodup_xs.
      apply in_split in Hin.
      destruct Hin as (l1, Hin).
      destruct Hin as (l2, Hin).
      subst.
      refine (IHm (l1 ++ l2) _ _ _).
      +  (* m < length (l1 ++ l2) *)
        rewrite app_length in *.
        simpl in Hlen.
        omega.
      +  (* forall x, In x (l1 ++ l2) -> x < m *)
        intros x Hin.
        cut (x < S m).
        * intro Hlt.
          inversion Hlt; subst; auto.
          exfalso.
          revert Hin.
          apply NoDup_remove_2.
          assumption.
        * apply Hlimit.
          rewrite in_app_iff in *.
          simpl.
          intuition.
      +  (* NoDup (l1 ++ l2) *)
        apply NoDup_remove_1 with m.
        assumption.
    - intro Hnotin.
      apply IHm.
      +  (* m < length xs *)
        omega.
      +  (* forall x, In x xs -> x < m *)
        intros x Hin.
        specialize (Hlimit _ Hin).
        inversion Hlimit; auto.
        subst.
        contradiction.
  }
Qed.


Theorem PigeonHole :
 forall A (FT : FiniteType A) (xs : list A),
 maxCard < length xs -> ~ NoDup xs.
Proof.
  intros A FT.
  simpl.
  intros xs size.
  rewrite finite_nodup.
  apply (@PigeonHole_nat maxCard).
  - rewrite map_length.
    assumption.
  - intros x in_x_mapped.
    apply in_map_iff in in_x_mapped.
    destruct in_x_mapped.
    destruct H as (eq, in_x0_xs).
    rewrite <- eq.
    apply fLim.
Qed.
