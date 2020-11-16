Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(*just so i remember proof*)
Lemma filter_app: forall (A: Type) (l1 l2: list A) (f: A -> bool),
  List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1.  destruct (f a) eqn : E; reflexivity.
Qed.


Check in_dec.

Section Whatever.

Variable l : list nat.
Variable Hnonneg: forall x, In x l -> 0 <= x.
Variable NoDups: forall i j, i < length l -> j < length l ->
  i <> j -> nth i l <> nth j l.

Fixpoint numLt(x: nat) :=
  match x with
  | O => O
  | S(n') => if (in_dec Nat.eq_dec n' l) then 1 + (numLt n')
    else (numLt n')
  end.

Definition numLt_alt (x: nat) := length(List.filter(fun y => y <? x) l).

(*need something like this*)
Lemma filter_split: forall (u: list nat) (b: nat),
  0 < b ->
  length(List.filter(fun y => y <? b) u) =
  length(List.filter(fun y => y <? b -1) u) +
  length(List.filter(fun y => y =? b - 1) u).
Proof.
  intros. induction u.
  - simpl. reflexivity.
  - simpl. destruct (a <? b) eqn : E.
    + rewrite Nat.ltb_lt in E.
      assert (a < b -1 \/ a = b-1) by lia.
      destruct H0.
      * destruct (a <? b -1) eqn : E'. 2 : { rewrite Nat.ltb_ge in E'. lia. }
        destruct (a =? b - 1) eqn : E''. rewrite Nat.eqb_eq in E''. lia.
        simpl. rewrite IHu. reflexivity.
      * destruct (a <? b - 1) eqn : E'. rewrite Nat.ltb_lt in E'. lia.
        destruct (a =? b - 1) eqn : E''. 2 : { rewrite Nat.eqb_neq in E''. lia. }
        simpl. rewrite IHu. lia.
    + rewrite Nat.ltb_ge in E. destruct (a <? b - 1) eqn : E'. rewrite Nat.ltb_lt in E'. lia.
      destruct (a =? b - 1) eqn : E''. rewrite Nat.eqb_eq in E''. lia. apply IHu.
Qed.
(*shouldnt be too hard in dafny - just a lot of cases and linear inequalities*)

(*proved in dafny*)
Lemma filter_empty: forall {A: Type} (u: list A) (f: A -> bool),
  (forall x, In x u -> f x = false) ->
  List.filter f u = nil.
Proof.
  intros. induction u.
  - reflexivity.
  - simpl. destruct (f a) eqn : E. rewrite H in E. inversion E. left. reflexivity.
    apply IHu. intros. apply H. right. assumption.
Qed. 

Lemma numLt_alt_zero: numLt_alt 0%nat = 0.
Proof.
  unfold numLt_alt. rewrite filter_empty. reflexivity. intros. apply Hnonneg in H. 
  rewrite Nat.ltb_ge. assumption.
Qed.

(*not surprisingly, also need this - why we need nodups*)
Lemma length_filter_eq: forall x,
  In x l ->
  length(List.filter(fun y => y =? x) l) = 1.
Proof.
Admitted.
(*did in dafny*)


Lemma numLt_numLt_alt_equiv: forall x, numLt x = numLt_alt x.
Proof.
  intros. induction x.
  - simpl. rewrite numLt_alt_zero. reflexivity.
  - simpl. destruct (in_dec Nat.eq_dec x l ).
    + unfold numLt_alt.  rewrite filter_split. 2 : lia.
      replace (S(x) - 1) with x by lia. 
      unfold numLt_alt in IHx. rewrite <- IHx. rewrite length_filter_eq. lia. assumption.
    + 

 r


