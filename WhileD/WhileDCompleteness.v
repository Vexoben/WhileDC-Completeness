Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Require Import PV.WhileDDenotations.
Require Import PV.HoareLogic.
Local Open Scope string.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Import  Lang_WhileD
        DntSem_WhileD.

Definition wp (c:com) (Q:assertion) : assertion :=
  fun s => forall s', eval_com c s s' -> Q s'.

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
    provable {{(wp c2 Q)}} c2 {{Q}} -> provable {{P}} [[c1; c2]] {{Q}}.
Proof.
  intros.
  eapply hoare_seq; [apply H|apply H0].
Qed.

Lemma wp_invariant : forall b c Q,
    valid {{ (wp (CWhile b c) Q) && [[ b ]] }} c {{ wp (CWhile b c) Q }}.
Proof.
  unfold valid.
  unfold wp.
  assn_unfold.
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

Theorem hoare_complet: forall P Q c,
   valid {{ P }} c {{ Q }} -> provable {{ P }} c {{ Q }}.
Proof.
  unfold valid.
  intros; revert P Q H.
  induction c; intros P Q HT. 
  + assert (P |-- Q).
    - assn_unfold.
      intros.
      specialize (HT s s).
      apply HT; auto.
      unfold eval_com.
      unfold skip_sem.
      unfold_RELS_tac.
      reflexivity.
    - eapply hoare_conseq_post; [|apply H].
      apply (hoare_skip P).
  + pose proof (hoare_asgn_fwd P x e).
    apply (hoare_conseq_post _ _ _ _ H).
    assn_unfold; simpl.
    unfold const_sem.
    unfold_substs.
    unfold var_sem.
    unfold ei2exprZ.
    unfold exp.
    unfold exprZ_eq.
    intros.
    destruct H0 as [n [? ?] ].
    pose proof (HT (state_subst s x n) s).
    apply H2; auto.
    unfold eval_com.
    unfold asgn_sem.
    split; auto.
    intros.
    unfold state_subst.
    destruct (x =? Y)%string eqn : I; auto.
    apply String.eqb_eq in I.
    rewrite I in H3; contradiction.
  + apply (hoare_seq P (fun s => exists x: state, P x /\ eval_com c1 x s) Q).
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
    - specialize (IHc1 Assn(P && [[e]]) Q).
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
    - specialize (IHc2 Assn(P && [[!e]]) Q).
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
        destruct (eval_expr_bool e s1); auto.
  + pose proof wp_invariant e c Q.
    specialize (IHc  Assn((wp (CWhile e c) Q) && [[e]])  (wp (CWhile e c) Q)).
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
      simpl.
      unfold not_sem.
      unfold negb.
      intros.
      exists O. simpl.
      unfold test_false.
      unfold_RELS_tac.
      split; [|tauto].
      destruct (eval_expr_bool e s); auto.
Qed.
