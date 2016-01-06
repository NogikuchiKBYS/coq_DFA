Require Import Arith Bool List.
Require Import Omega.

Require Import Util Pigeon Finite.

Set Implicit Arguments.


(* DFA (入力が有限集合であることを仮定しない) *)
Record DFA (dChType : Type)  := 
 mkDFA{dStType : Type;
       dStFinite : FiniteType dStType;
       dF : dStType -> bool;
       dDelta : dStType -> dChType -> dStType;
       dq0 : dStType}.

Definition runDFA (dChType : Type) (dfa : DFA dChType) 
  (cs : list dChType) := fold_left (dDelta dfa) cs (dq0 dfa).
Definition judgeDFA dChType (dfa : DFA dChType) (cs : list dChType) :=
  dF dfa (fold_left (dDelta dfa) cs (dq0 dfa)).
Definition AcceptDFA dChType (dfa : DFA dChType) (cs : list dChType) :=
  judgeDFA dfa cs = true.
Definition Regular dChType (p : list dChType -> Prop) :=
  exists dfa, forall cs, p cs <-> AcceptDFA dfa cs.
Definition ln2_0 : ftype 2 := ft_succ (ft_n 0).
Definition ln2_1 : ftype 2 := ft_n 1.

Fact ln2_0_1_neq : ln2_0 <> ln2_1.
Proof.
  intro C.
  inversion C.
Qed.

(* 0をn回繰り返したあと1をn回繰り返すような文字列からなる言語 *)
Inductive RepWord : list (ftype 2) -> Prop :=
    repword : forall n, RepWord (rep ln2_0 n ++ rep ln2_1 n).

Definition make_repword (n : nat) : {str | RepWord str}.
  refine (exist _ (rep ln2_0 n ++ rep ln2_1 n) _).
  constructor.
Defined.

Lemma repword_regular_different_state :
 forall dfa : DFA (ftype 2),
 (forall cs, RepWord cs <-> AcceptDFA dfa cs) ->
 forall n m : nat,
 n <> m -> runDFA dfa (rep ln2_0 n) <> runDFA dfa (rep ln2_0 m).
Proof.
  intros dfa reg n m n_ne_m.
  unfold not.
  intro eq_st.
  remember (rep ln2_0 n) as s0n.
  remember (rep ln2_1 n) as s1n.
  remember (rep ln2_0 m) as s0m.
  remember (rep ln2_1 m) as s1m.
  assert (RepWord (s0n ++ s1n)) as RWn; [ subst; constructor | idtac ].
  apply reg in RWn.
  unfold AcceptDFA in RWn.
  unfold judgeDFA in RWn.
  rewrite fold_left_app in RWn.
  unfold runDFA in eq_st.
  rewrite eq_st in RWn.
  rewrite <- fold_left_app in RWn.
  fold (judgeDFA dfa (s0m ++ s1n)) in RWn.
  fold (AcceptDFA dfa (s0m ++ s1n)) in RWn.
  apply reg in RWn.
  inversion RWn as (k, Hk).
  assert (count_occ (@eq_ftype_dec 2) (s0m ++ s1n) ln2_0 = m) as Cm.
  {rewrite count_occ_app.
    rewrite Heqs0m.
    rewrite (rep_count (@eq_ftype_dec 2) ln2_0 m).
    rewrite Heqs1n.
    rewrite (rep_count_0 (@eq_ftype_dec 2) n (not_eq_sym ln2_0_1_neq)).
    auto.
  }assert (count_occ (@eq_ftype_dec 2) (s0m ++ s1n) ln2_0 = k) as Ck.
  {rewrite <- Hk.
    rewrite count_occ_app.
    rewrite (rep_count (@eq_ftype_dec 2) ln2_0 k).
    rewrite (rep_count_0 (@eq_ftype_dec 2) k (not_eq_sym ln2_0_1_neq)).
    auto.
  }rewrite Ck in Cm; clear Ck.

  assert (count_occ (@eq_ftype_dec 2) (s0m ++ s1n) ln2_1 = n) as Cn.
  {rewrite count_occ_app.
    rewrite Heqs1n.
    rewrite (rep_count (@eq_ftype_dec 2) ln2_1 n).
    rewrite Heqs0m.
    rewrite (rep_count_0 (@eq_ftype_dec 2) m ln2_0_1_neq).
    auto.
  }assert (count_occ (@eq_ftype_dec 2) (s0m ++ s1n) ln2_1 = k) as Ck.
  {rewrite <- Hk.
    rewrite count_occ_app.
    rewrite (rep_count (@eq_ftype_dec 2) ln2_1 k).
    rewrite (rep_count_0 (@eq_ftype_dec 2) k ln2_0_1_neq).
    auto.
  }rewrite Ck in Cn; clear Ck.
  subst.
  apply eq_sym in Cn.
  contradiction.
Qed.


Lemma repword_regular_different_state_inv :
 forall dfa : DFA (ftype 2),
 (forall cs, RepWord cs <-> AcceptDFA dfa cs) ->
 forall n m : nat,
 runDFA dfa (rep ln2_0 n) = runDFA dfa (rep ln2_0 m) -> n = m.
Proof.
  intros dfa accept n m.
  intro e.
  case (eq_nat_dec n m); auto.
  intro.
  apply (repword_regular_different_state accept) in n0.
  contradiction.
Qed.

Fact repword_not_regular : ~ Regular RepWord.
Proof.
  unfold not; intro.
  inversion H as (dfa, accept).
  remember (dStType dfa) as stType.
  remember (dStFinite dfa) as stFinite.
  remember
   (map (fun n => runDFA dfa (rep ln2_0 n)) (seq 0 (S maxCard))) as ws.
  cut (NoDup ws).
  - apply (@PigeonHole _ _).
    rewrite Heqws.
    rewrite map_length.
    rewrite seq_length.
    apply lt_n_Sn.
  - rewrite Heqws.
    apply injective_map_nodup.
    + unfold Injective.
      apply (repword_regular_different_state_inv accept).
    + apply seq_nodup.
Qed.
