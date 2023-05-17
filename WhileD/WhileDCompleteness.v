Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.WhileDDenotations.
Require Import PV.HoareLogic.
Local Open Scope string.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Import Lang_While.
Import Lang_WhileD.
Import DntSem_WhileD.
Import HoareWhileD.
Import HoareWhileD_Admissible.

Definition wp (c:com) (Q:assertion) : assertion :=
  fun s => forall s', (eval_com c).(nrm) s s' -> Q s'.

Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  valid {{wp c Q}} c {{Q}}.
Proof.
  intros.
  unfold valid.
  intros s1 s2.
  unfold wp.
  intros.
  apply H.
  tauto.
Qed.

Theorem wp_is_weakest : forall c Q P',
    valid {{P'}} c {{Q}} ->
    P' |-- (wp c Q).
Proof.
  unfold valid.
  unfold derives.
  unfold wp.
  intros.
  specialize (H s s').
  apply H; tauto.
Qed.

Lemma wp_seq : forall P Q c1 c2,
    provable {{P}} c1 {{(wp c2 Q)}} -> 
    provable {{(wp c2 Q)}} c2 {{Q}} -> provable {{P}} (c1; c2) {{Q}}.
Proof.
  intros.
  eapply hoare_seq; [apply H|apply H0].
Qed.

Lemma wp_invariant : forall b c Q,
    valid {{ (wp (CWhile b c) Q) && (eb2assn b) }} c {{ wp (CWhile b c) Q }}.
Proof.
  unfold valid.
  unfold wp.
  unfold andp.
  simpl.
  intros.
  destruct H.
  specialize (H s').
  apply H.
  revert H1 H2 H0.
  simpl.
  unfold while_sem.
  unfold_RELS_tac.
  intros.
  destruct H1.
  exists (S x).
  simpl.  
  unfold_RELS_tac.
  left.
  exists s1.
  split.
  + unfold test_true.
    unfold_RELS_tac.
    split; [|tauto].
    revert H2.
    unfold eb2assn. tauto.
  + exists s2.
    tauto.
Qed.
(* 
Lemma concat_empty: 
  forall X,
  Rels.concat X Sets.empty = Sets.empty. *)

Theorem hoare_complete: forall P Q c,
   valid {{ P }} c {{ Q }} -> provable {{ P }} c {{ Q }}.
Proof.
  unfold valid.
  intros; revert P Q H.
  induction c; intros P Q HT. 
  + assert (P |-- Q).
    - intros.
      unfold derives.
      intros.
      specialize (HT s s).
      apply HT; auto.
      unfold eval_com.
      unfold skip_sem.
      unfold_RELS_tac.
      reflexivity.
    - eapply hoare_conseq_post; [|apply H].
      apply (hoare_skip P).
  + admit.
  + admit.
  + apply (hoare_seq P (fun s => exists x: state, P x /\ (eval_com c1).(nrm) x s) Q).
    - apply IHc1.
      intros.
      exists s1.
      tauto.
    - apply IHc2.
      intros.
      destruct H,H.
      specialize (HT x s2).
      apply HT; [tauto|].
      simpl.
      unfold seq_sem.
      unfold_RELS_tac.
      exists s1; tauto.
  + apply hoare_if.
    - specialize (IHc1 Assn(P && (eb2assn e)) Q).
      apply IHc1.
      intros.
      specialize (HT s1 s2); apply HT.
      * revert H. assn_unfold. tauto.
      * simpl.
        unfold if_sem.
        left.
        unfold test_true.
        unfold_RELS_tac.
        exists s1.
        split; auto.
        split; auto.
        revert H; assn_unfold; tauto.
    - specialize (IHc2 Assn(P && (eb2assn_not e)) Q).
      apply IHc2.
      intros.
      specialize (HT s1 s2); apply HT.
      * revert H. assn_unfold. tauto.
      * simpl.
        unfold if_sem.
        right.
        unfold test_false.
        unfold_RELS_tac.
        exists s1.
        split; auto.
        split; auto.
        revert H; assn_unfold.
        unfold eb2assn.
        simpl.
        unfold not_sem.
        intros.
        unfold negb in H; destruct H.
        unfold eb2assn_not in H1.
        destruct H1.
        destruct H1.
        assert(x = Integers.Int64.repr 0).
        ++  rewrite <- H2.
            pose proof Integers.Int64.repr_signed x.
            rewrite H3.
            reflexivity.
        ++  subst x.
            tauto. 
  + pose proof wp_invariant e c Q.
    specialize (IHc  Assn((wp (CWhile e c) Q) && (eb2assn e))  (wp (CWhile e c) Q)).
    unfold valid in H.
    apply IHc in H.
    apply hoare_while in H.
    eapply hoare_conseq; [apply H| |].
    - unfold derives.
      unfold wp.
      intros. 
      specialize (HT s s').
      tauto.
    - unfold derives.
      unfold wp.
      assn_unfold.
      intros.
      destruct H0.
      specialize (H0 s).
      apply H0.
      simpl.
      revert H1.
      unfold while_sem.
      unfold_RELS_tac.
      unfold eb2assn.
      unfold eb2assn_not.
      simpl.
      unfold not_sem.
      unfold negb.
      intros.
      exists (S O).
      unfold iter_nrm_lt_n.
      unfold Sets.union.
      simpl.
      right.
      unfold test_false.
      unfold_RELS_tac.
      split; [|tauto].
      destruct H1.
      destruct H1.
      assert(x = Integers.Int64.repr 0).
      ++  rewrite <- H2.
          pose proof Integers.Int64.repr_signed x.
          rewrite H3.
          reflexivity.
      ++  subst x.
          tauto.
Qed.
