Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.WhileDCDenotations.
Require Import PV.HoareLogic.
Local Open Scope string.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Import Lang_While.
Import Lang_WhileDC.
Import DntSem_WhileDC.
Import HoareWhileDC.
Import HoareWhileDC_Admissible.

Definition wp (c:com) (Q Q_brk Q_cnt:assertion) : assertion :=
  fun s => 
  ((eval_com c).(err) s -> False) /\
  (forall s', (eval_com c).(nrm) s s' -> Q s') /\ 
  (forall s', (eval_com c).(brk) s s' -> Q_brk s') /\ 
  (forall s', (eval_com c).(cnt) s s' -> Q_cnt s').

Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q Q_brk Q_cnt, 
  valid {{wp c Q Q_brk Q_cnt}} c {{Q, Q_brk, Q_cnt}}.
Proof.
  intros.
  unfold valid.
  intros s1.
  unfold wp.
  intros.
  destruct H as [? [? [? ?]]].
  split. {
    tauto.
  }
  split. {
    intros.
    apply H0.
    tauto.
  }
  split. {
    intros.
    apply H1.
    tauto.
  }
  intros.
  apply H2.
  tauto.
Qed.

Theorem wp_is_weakest : forall c Q Q_brk Q_cnt P',
    valid {{P'}} c {{Q, Q_brk, Q_cnt}} ->
    P' |-- (wp c Q Q_brk Q_cnt).
Proof.
  unfold valid.
  unfold derives.
  unfold wp.
  intros.
  specialize (H s H0).
  destruct H as [? [? [? ?]]].
  tauto.
Qed.

Lemma wp_seq : forall P Q Q_brk Q_cnt c1 c2,
    provable {{P}} c1 {{(wp c2 Q Q_brk Q_cnt), Q_brk, Q_cnt}} -> 
    provable {{(wp c2 Q Q_brk Q_cnt)}} c2 {{Q, Q_brk, Q_cnt}} ->
    provable {{P}} (c1; c2) {{Q, Q_brk, Q_cnt}}.
Proof.
  intros.
  pose proof hoare_seq P (wp c2 Q Q_brk Q_cnt) Q Q_brk Q_cnt c1 c2.
  apply H1; tauto.
Qed.

(* Lemma wp_invariant : forall e c Q Q_brk,
    valid {{ (wp (CWhile e c) Q Q_brk Q) && (eb2assn e) }}
     c 
     {{ (wp (CWhile e c) Q Q_brk Q), Q_brk, (wp (CWhile e c) Q Q_brk Q) }}. *)

Lemma wp_invariant : forall e c Q,
  valid {{ (wp (CWhile e c) Q asrt_false asrt_false) && (eb2assn e) }}
  c 
  {{ (wp (CWhile e c) Q asrt_false asrt_false), Q, (wp (CWhile e c) Q asrt_false asrt_false) }}.
Proof.
  unfold valid.
  unfold wp.
  unfold andp.
  simpl.
  intros.
  destruct H as [? [? [? ?]]].
  destruct H as [? [? ?]].
  destruct H3.
  clear H3 H4.
  split; intros. {
    revert H; unfold_RELS_tac; intros.
    apply H.
    exists (S O).
    simpl.
    unfold_RELS_tac.
    left.
    exists s1.
    split; auto.
    unfold test_true. unfold_RELS_tac.
    split; auto.
    exists x. tauto.
  }
  split. intros. {
    revert H H2.
    unfold_RELS_tac.
    simpl. intros.
    split.
    + intros.
      apply H.
      destruct H4 as [i ?].
      exists (S i).
      simpl.
      unfold_RELS_tac; simpl.
      left.
      exists s1.
      split.
      - unfold test_true; unfold_RELS_tac.
        split; auto.
        exists (x).
        tauto.
      - left.
        left.
        exists s2.
        tauto.
    + split.
      - intros.
        destruct H4 as [i ?].
        apply H2.
        exists (S i).
        simpl.
        unfold test_true.
        unfold_RELS_tac.
        left.
        exists s1.
        split.
        * split; auto.
          exists x.
          tauto.
        * left.
          left.
          exists s2.
          tauto.
      - split; tauto.
  }
  split; intros. {
    specialize (H2 s2).
    revert H2; unfold_RELS_tac; intros.
    apply H2.
    exists (S O).
    simpl.
    unfold_RELS_tac.
    left.
    exists s1.
    split. {
      unfold test_true; unfold_RELS_tac.
      split; auto.
      exists x; auto.
    }
    right.
    auto.
  }
  split; intros. {
    apply H.
    revert H4.
    unfold_RELS_tac.
    intros.
    destruct H4 as [i ?].
    exists (S i).
    simpl.
    unfold_RELS_tac.
    left.
    exists s1.
    split. {
      unfold test_true; unfold_RELS_tac.
      split; auto.
      exists x; auto.
    }
    left.
    right.
    exists s2.
    auto.
  }
  split; intros. {
    apply H2.
    revert H4.
    unfold_RELS_tac.
    intros.
    destruct H4 as [i ?].
    exists (S i).
    simpl.
    unfold_RELS_tac.
    left.
    exists s1.
    split. {
      unfold test_true; unfold_RELS_tac.
      split; auto.
      exists x; auto.
    } 
    left.
    right.
    exists s2.
    auto.
  }
  unfold_RELS_tac.
  split; intros; auto; contradiction.
Qed.

Lemma wp_inv_do_while_to_while:
  forall (e:expr)(c:com)(Q:assertion),
  valid (BuildHoareTriple (wp (CDoWhile c e) Q asrt_false asrt_false) 
  c 
  (wp (CWhile e c) Q asrt_false asrt_false) Q (wp (CWhile e c) Q asrt_false asrt_false)).
Proof.
  intros.
  unfold valid.
  unfold wp.
  intros.
  simpl in H.
  unfold_RELS_tac.
  intros.
  destruct H as [? [? [? ?]]].
  clear H1 H2.
  split. {
    intros.
    clear H0.
    apply H. left. auto. 
  }
  split. {
    split. {
      intros.
      apply H.
      unfold_RELS_tac.
      right.
      exists s2.
      split; auto.
    }
    split. {
      intros.
      apply H0.
      unfold_RELS_tac.
      right.
      exists s2.
      split; auto.
    }
    split. {
      intros.
      unfold asrt_false.
      simpl in H2.
      revert H2; unfold_RELS_tac; tauto.
    }
    intros.
    unfold asrt_false.
    simpl in H2.
    revert H2; unfold_RELS_tac; tauto.
  }
  split. {
    intros.
    apply H0.
    unfold_RELS_tac.
    left; auto.
  }
  split. {
    intros.
    simpl in H2.
    revert H2; unfold_RELS_tac; intros.
    destruct H2 as [i ?].
    apply H. 
    clear H H0.
    unfold_RELS_tac.
    right.
    exists s2.
    split; auto.
    exists i; auto.
  }
  split. {
    intros.
    simpl in H2.
    apply H0.
    revert H2.
    unfold_RELS_tac.
    intros.
    destruct H2 as [i ?].
    right.
    exists s2.
    split; auto.
    exists i. auto.
  }
  simpl.
  unfold_RELS_tac.
  auto.
Qed.
(* 
Lemma concat_empty: 
  forall X,
  Rels.concat X Sets.empty = Sets.empty. *)

Definition expr_equal_to(e : expr)(a : int64) : assertion :=
  fun s => (eval_r e).(nrm) s a.

Definition var_env_equal_to(x : var_name)(a : int64) : assertion :=
  fun s => s.(env) x = a.  

Definition exp_state(s : state)(a : int64)(P : assertion) : Prop :=
  exists v : val, P (state_subst s a v).

Definition exclude_mem(P : assertion)(a : int64) : assertion :=
  fun s => (s.(mem) a = None /\ (exp_state s a P)).

Definition one_mem_state(s:state)(a:int64) : state :=
  {|
    env := s.(env);
    mem := fun y => if (Int64.eq y a) then s.(mem) a else None;
  |}.
  
Definition exclude_one_mem_state(s:state)(a:int64) : state :=
  {|
    env := s.(env);
    mem := fun y => if (Int64.eq y a) then None else s.(mem) y;
  |}.

Lemma false_derives_all: forall Q,
  asrt_false |-- Q.
Proof.
  intros.
  unfold derives.
  unfold asrt_false.
  intros.
  tauto.
Qed.

Lemma for_P_to_R:
  forall (e:expr)(c1 c2 c3:com)(H:assertion),
    valid (BuildHoareTriple
      (wp (c1) (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false)
      c1
      (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false).
Proof.
  intros.
  pose proof wp_is_precondition.
  specialize (H0 c1 (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false).
  tauto.
Qed.

(* Lemma for_P_to_R:
  forall (e:expr)(c1 c2 c3:com)(H:assertion),
    valid (BuildHoareTriple
      (wp (CFor c1 e c2 c3) H asrt_false asrt_false)
      c1
      (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false).
Proof.
  simpl.
  unfold wp.
  unfold asrt_false.
  intros.
  (* assert(((eval_com) c1).(brk) = ∅). {
    pose proof wp_is_precondition (CFor c1 e c2 c3) H asrt_false asrt_false.
    simpl in H1.
    revert H1; unfold wp; unfold_RELS_tac; intros.

  }
  pose proof H0 as H00.
  pose proof H1 as H01.
  pose proof H2 as H02.
  pose proof H3 as H03.
  clear H0 H1 H2 H3.
  pose proof H4. clear H4. *)
  destruct H0 as [? [? [? ?]]].
  split. {
    intros.
    apply H0.
    simpl.
    unfold_RELS_tac.
    tauto.
  }
  split. {
    intros.
    split. {
      intros. apply H0.
      revert H5.
      simpl.
      unfold_RELS_tac.
      intros.
      destruct H5; try contradiction.
      destruct H5 as [s2' [? ?]]; subst s2'.
      destruct H6 as [i ?].
      right.
      exists s2.
      split; auto.
      exists i.
      tauto.
    }
    split. {
      intros.
      apply H1.
      revert H5; simpl; unfold_RELS_tac.
      intros.
      destruct H5 as [s2' [? ?]].
      subst s2'.
      exists s2.
      split; auto.
    }
    split. {
      intros.
      apply (H2 s').
      revert H5; simpl; unfold_RELS_tac.
      tauto.
    }
    intros.
    apply (H3 s').
    revert H5; simpl; unfold_RELS_tac.
    tauto.
  }
  split. {
    intros.
    apply (H2 s1).
    revert H4; simpl; unfold_RELS_tac.
    intros.
    rewrite H00 in H4.
    revert H4; unfold_RELS_tac; tauto.
  }
  intros.
  apply (H3 s1).
  revert H4; simpl; unfold_RELS_tac.
  intros.
  rewrite H01 in H4.
  revert H4; unfold_RELS_tac; tauto.
Qed. *)

Lemma for_R_to_Q:
  forall (e:expr)(c2 c3:com)(H:assertion),
    valid (BuildHoareTriple
      (andp (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) (eb2assn e))
      c3
      (wp c2 (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false)
      H
      (wp c2 (wp (CFor CSkip e c2 c3) H asrt_false asrt_false) asrt_false asrt_false)).
Proof.
  simpl.
  unfold wp, asrt_false, andp, eb2assn.
  intros.
  pose proof H0 as H1.
  pose proof H0 as H2.
  destruct H2 as [? ?].
  destruct H2 as [? [? [? ?]]].
  split. {
    intros. apply H2.
    simpl.
    unfold_RELS_tac.
    right.
    exists s1; split; auto.
    exists (S O).
    simpl.
    unfold test_true; unfold_RELS_tac.
    left.
    exists (s1).
    split; auto.
  }
  split. {
    intros.
    split. {
      intros.
      apply H2.
      simpl.
      unfold_RELS_tac.
      right.
      exists s1.
      split; auto.
      exists (S O).
      simpl.
      unfold test_true; unfold_RELS_tac.
      left.
      exists s1.
      split; auto.
      left; left; right.
      exists s2.
      split; auto.
    }
    split. {
      intros.
      split. {
        simpl.
        unfold_RELS_tac.
        intros.
        destruct H9; auto.
        destruct H9 as [s3 [? ?]].
        subst s'.
        apply H2.
        simpl.
        unfold_RELS_tac.
        right.
        exists s1.
        split; auto.
        destruct H10 as [i ?].
        exists (S i).
        simpl.
        unfold test_true.
        unfold_RELS_tac.
        left.
        exists s1.
        split; auto.
        left. left. left. left.
        exists s2; split; auto.
        exists s3; split; auto.
      }
      split. {
        intros.
        apply H4.
        revert H9; simpl; unfold_RELS_tac.
        intros.
        destruct H9 as [s3 [? ?]].
        subst s'.
        destruct H10 as [i ?].
        exists s1; split; auto.
        exists (S i).
        simpl; unfold test_true; unfold_RELS_tac.
        left.
        exists (s1).
        split; auto.
        left. left.
        exists s2. split; auto.
        exists s3; split; auto.
      }
      split. {
        intros.
        apply (H5 s').
        revert H9; simpl; unfold_RELS_tac.
        intros.
        tauto.
      }
      simpl.
      unfold_RELS_tac; tauto.
    }
    simpl in H5,H6.
    rewrite H0, H1.
    unfold_RELS_tac; tauto.
  }
  split. {
    intros.
    apply H4.
    simpl.
    unfold_RELS_tac.
    exists s1.
    split; auto.
    exists (S O).
    simpl. unfold test_true.
    unfold_RELS_tac.
    left.
    exists s1.
    split; auto.
  }
  split. {
    intros.
    apply H2.
    simpl.
    unfold_RELS_tac.
    right.
    exists s1.
    split; auto.
    exists (S O).
    simpl. unfold test_true.
    unfold_RELS_tac.
    left.
    exists s1.
    split; auto.
    left. right.
    exists s2. tauto.
  }
  split. {
    intros.
    split. {
      intros. apply H2.
      simpl.
      unfold_RELS_tac.
      right.
      exists s1.
      split; auto.
      simpl in H9.
      revert H9.
      unfold_RELS_tac; intros.
      destruct H9; try contradiction.
      destruct H9 as [s3 [? ?]].
      subst s'.
      destruct H10 as [i ?].
      exists (S i).
      simpl. unfold test_true.
      unfold_RELS_tac.
      left.
      exists s1.
      split; auto.
      left. left. left. right.
      exists s2; split; auto.
      exists s3. tauto.
    }
    split. {
      intros. apply H4.
      simpl.
      unfold_RELS_tac.
      exists s1.
      split; auto.
      simpl in H9.
      revert H9.
      unfold_RELS_tac; intros.
      destruct H9 as [s3 [? ?]].
      subst s'.
      destruct H10 as [i ?].
      exists (S i).
      simpl. unfold test_true.
      unfold_RELS_tac.
      left.
      exists s1.
      split; auto.
      left. right.
      exists s2; split; auto.
      exists s3. tauto.
    }
    split. {
      intros. apply (H5 s'0).
      simpl.
      unfold_RELS_tac.
      simpl in H9.
      revert H9.
      unfold_RELS_tac.
      tauto.
    }
    simpl. unfold_RELS_tac. tauto.
  }
  rewrite H0, H1.
  unfold_RELS_tac.
  tauto.
Qed.

Theorem hoare_complete: forall P Q Q_brk Q_cnt c,
   valid {{ P }} c {{ Q, Q_brk, Q_cnt }} -> provable {{ P }} c {{ Q, Q_brk, Q_cnt }}.
Proof.
  unfold valid.
  intros; revert P Q Q_brk Q_cnt H.
  induction c; intros P Q Q_brk Q_cnt HT. 
  + assert (P |-- Q).
    - intros.
      unfold derives.
      intros.
      specialize (HT s).
      apply HT; auto.
      unfold eval_com.
      unfold skip_sem.
      unfold_RELS_tac.
      reflexivity.
    - pose proof hoare_conseq_post P Q Q_brk Q_cnt P asrt_false asrt_false CSkip.
      apply H0.
      * apply hoare_skip.
      * apply H.
      * apply false_derives_all.
      * apply false_derives_all. 
  + assert(P |-- (exp64 (fun a:int64 => (andp P (var_env_equal_to x a))))). {
      unfold derives.
      unfold exp64.
      unfold var_env_equal_to.
      unfold andp.
      intros.
      exists (s.(env) x).
      tauto.
    }
    eapply hoare_conseq_pre; [|apply H].
    apply hoare_exist.
    intros.
    assert(P |-- (exp64 (fun b:int64 => (andp P (expr_equal_to e b))))). {
      unfold derives.
      unfold exp64.
      unfold expr_equal_to.
      unfold andp.
      intros.
      specialize (HT s H0).
      destruct HT.
      simpl in H1.
      revert H1; unfold_RELS_tac; intros.
      assert ((eval_r e).(err) s -> False). {
        intros.
        apply H1.
        left.
        right.
        apply H3.
      }
      pose proof eval_r_not_err _ _ H3.
      destruct H4.
      exists x0.
      tauto.
    }
    assert (Assn(P && (var_env_equal_to x a)) |-- exp64 (fun b : int64 => Assn (P && (var_env_equal_to x a) && (expr_equal_to e b)))). {
      revert H0.
      unfold derives, exp64, andp.
      intros.
      destruct H1.
      specialize (H0 s H1).
      destruct H0.
      exists x0.
      tauto.
    }
    eapply hoare_conseq_pre; [|apply H1].
    apply hoare_exist.
    intro a0.
    clear H H0 H1.
    pose proof hoare_asgn_var_fwd (Assn(P && (var_env_equal_to x a) && (expr_equal_to e a0))) (exclude_mem Assn(P && (var_env_equal_to x a) && (expr_equal_to e a0)) a).
    specialize (H e a a0 x).
    assert((forall s : state, Assn (P && (var_env_equal_to x a) && (expr_equal_to e a0)) s -> s.(env) x = a)). {
      clear H.
      intros.
      unfold andp in H.
      destruct H.
      destruct H.
      unfold var_env_equal_to in H1.
      apply H1.
    }
    assert((forall s : state, Assn (P && (var_env_equal_to x a) && (expr_equal_to e a0)) s -> (eval_r e).(nrm) s a0)). {
      clear H.
      intros.
      unfold andp in H.
      destruct H.
      destruct H.
      unfold expr_equal_to in H1.
      apply H1.
    }
    assert((Assn (P && (var_env_equal_to x a) && (expr_equal_to e a0)))
    |--  exp (fun u : val => (sepcon (store a u) (exclude_mem (Assn (P && (var_env_equal_to x a) && (expr_equal_to e a0))) a)))). {
      clear H H0 H1.
      unfold sepcon, andp, exp, expr_equal_to, var_env_equal_to, store, derives, exp_state, state_subst.
      intros.
      destruct H.
      destruct H.
      specialize (HT s H).
      destruct HT.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
      assert(asgn_deref_sem_err (fun (s : state) (i : int64) => s.(env) x = i) s -> False) by tauto.
      (* assert(asgn_deref_sem_err (eval_r e1).(nrm) s -> False) by tauto. *)
      clear H3.
      unfold asgn_deref_sem_err in H4.
      assert (exists u: val, s.(mem) a = Some u). {
        destruct (s.(mem) a) eqn : I.
        - exists v; tauto.
        - destruct H4.
          exists a.
          tauto.
      }
      destruct H3.
      exists x0.
      exists (one_mem_state s a), (exclude_one_mem_state s a).
      split.
      - simpl. 
        split.
        * destruct (Int64.eq a a) eqn : J.
          ++ tauto.
          ++ rewrite Int64.eq_true in J.
             discriminate.
        * intros.
          destruct (Int64.eq i a) eqn : J.
          ++ pose proof Int64.eq_false _ _ H5.
             rewrite J in H6; discriminate.
          ++ tauto.
      - split. {
        unfold exclude_mem.
        unfold exclude_one_mem_state.
        split.
        * simpl.
          destruct (Int64.eq a a) eqn : J.
          ++ tauto.
          ++ rewrite Int64.eq_true in J.
            discriminate.
        * unfold exp_state.
          unfold state_subst; simpl.
          exists x0.
          assert((  {|
          env := s.(env);
          mem := fun x1 : int64 =>
                 if Int64.eq x1 a
                 then Some x0
                 else if Int64.eq x1 a then None else s.(mem) x1 |}) = s). {
            assert((fun x1 : int64 =>
            if Int64.eq x1 a then Some x0 else if Int64.eq x1 a then None else s.(mem) x1) = s.(mem)). {
              apply functional_extensionality.
              intros.
              pose proof Int64.eq_spec x1 a.
              destruct (Int64.eq x1 a) eqn : K.
              ++ rewrite H5.
                 rewrite H3.
                 reflexivity.
              ++ reflexivity. 
            }
            rewrite H5.
            destruct s.
            simpl.
            reflexivity.
          }
          rewrite ! H5.
          tauto.
      }
      split. {
        unfold one_mem_state.
        simpl.
        reflexivity.
      }
      split. {
        unfold exclude_one_mem_state.
        simpl.
        reflexivity.
      }
      intros. simpl.
      pose proof Int64.eq_spec i a.
      destruct (Int64.eq i a) eqn : I.
      * left.
        rewrite H5.
        tauto.
      * right.
        tauto.
    }
    specialize (H H1 H0 H2).
    clear H0 H1 H2.
    apply (hoare_conseq_post _ _ _ _ _ _ _ _ H); [ | apply false_derives_all | apply false_derives_all].
    clear H.
    unfold derives, andp, exclude_mem, expr_equal_to, store, sepcon.
    intros.
    destruct H as [s1 [s2 [? [? [? [? ?]]]]]].
    destruct H.
    destruct H0.
    unfold exp_state in H5.
    destruct H5 as [v ?].
    destruct H5 as [[? ?] ?].
    specialize (HT (state_subst s2 a v) H5).
    destruct HT.
    destruct H9.
    apply H9.
    simpl.
    unfold asgn_deref_sem_nrm.
    exists a, a0.
    split; [auto | split; auto].
    split. {
      unfold state_subst; simpl.
      pose proof Int64.eq_spec a a.
      destruct (Int64.eq a a).
      + discriminate.
      + contradiction.
    }
    split. {
      specialize (H3 a).
      destruct H3.
      + destruct H3.
        rewrite H3, H.
        reflexivity.
      + destruct H3.
        rewrite H in H11.
        discriminate. 
    }
    split. {
      intros.
      unfold state_subst; simpl.
      rewrite H2.
      reflexivity.
    }
    intros.
    unfold state_subst; simpl.
    pose proof Int64.eq_spec p a.
    destruct (Int64.eq p a).
    - rewrite H12 in H11; contradiction.
    - specialize (H3 p).
      specialize (H4 p H12).
      destruct H3; destruct H3.
      * rewrite H4 in H3.
        rewrite H3.
        rewrite H13.
        reflexivity.
      * rewrite H3.
        reflexivity.
  + assert(P |-- (exp64 (fun a:int64 => (andp P (expr_equal_to e1 a))))). {
      unfold derives.
      unfold exp64.
      unfold expr_equal_to.
      unfold andp.
      intros.
      specialize (HT s H).
      destruct HT.
      simpl in H0.
      revert H0; unfold_RELS_tac; intros.
      assert ((eval_r e1).(err) s -> False) by tauto.
      pose proof eval_r_not_err _ _ H2.
      destruct H3.
      exists x.
      tauto.
    }  
    eapply hoare_conseq_pre; [|apply H].
    apply hoare_exist.
    intros.
    assert(P |-- (exp64 (fun b:int64 => (andp P (expr_equal_to e2 b))))). {
      unfold derives.
      unfold exp64.
      unfold expr_equal_to.
      unfold andp.
      intros.
      specialize (HT s H0).
      destruct HT.
      simpl in H1.
      revert H1; unfold_RELS_tac; intros.
      assert ((eval_r e2).(err) s -> False) by tauto.
      pose proof eval_r_not_err _ _ H3.
      destruct H4.
      exists x.
      tauto.
    }
    assert (Assn(P && (expr_equal_to e1 a)) |-- exp64 (fun b : int64 => Assn (P && (expr_equal_to e1 a) && (expr_equal_to e2 b)))). {
      revert H0.
      unfold derives, exp64, andp.
      intros.
      destruct H1.
      specialize (H0 s H1).
      destruct H0.
      exists x.
      tauto.
    }
    eapply hoare_conseq_pre; [|apply H1].
    apply hoare_exist.
    intro a0.
    clear H H0 H1.
    pose proof hoare_asgn_deref_fwd (Assn(P && (expr_equal_to e1 a) && (expr_equal_to e2 a0))) (exclude_mem Assn(P && (expr_equal_to e1 a) && (expr_equal_to e2 a0)) a).
    specialize (H e1 e2 a a0).
    assert((forall s : state, Assn (P && (expr_equal_to e1 a) && (expr_equal_to e2 a0)) s -> (eval_r e1).(nrm) s a)). {
      clear H.
      intros.
      unfold andp in H.
      destruct H.
      destruct H.
      unfold expr_equal_to in H1.
      apply H1.
    }
    assert((forall s : state, Assn (P && (expr_equal_to e1 a) && (expr_equal_to e2 a0)) s -> (eval_r e2).(nrm) s a0)). {
      clear H.
      intros.
      unfold andp in H.
      destruct H.
      destruct H.
      unfold expr_equal_to in H1.
      apply H1.
    }
    assert((Assn (P && (expr_equal_to e1 a) && (expr_equal_to e2 a0)))
    |--  exp (fun u : val => (sepcon (store a u) (exclude_mem (Assn (P && (expr_equal_to e1 a) && (expr_equal_to e2 a0))) a)))). {
      clear H H0 H1.
      unfold sepcon, andp, exp, expr_equal_to, store, derives, exp_state, state_subst.
      intros.
      destruct H.
      destruct H.
      specialize (HT s H).
      destruct HT.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
      assert(asgn_deref_sem_err (eval_r e1).(nrm) s -> False) by tauto.
      clear H2.
      unfold asgn_deref_sem_err in H4.
      assert (exists u: val, s.(mem) a = Some u). {
        destruct (s.(mem) a) eqn : I.
        - exists v; tauto.
        - destruct H4.
          exists a.
          tauto.
      }
      destruct H2.
      exists x.
      exists (one_mem_state s a), (exclude_one_mem_state s a).
      split.
      - simpl. 
        split.
        * destruct (Int64.eq a a) eqn : J.
          ++ tauto.
          ++ rewrite Int64.eq_true in J.
             discriminate.
        * intros.
          destruct (Int64.eq i a) eqn : J.
          ++ pose proof Int64.eq_false _ _ H5.
             rewrite J in H6; discriminate.
          ++ tauto.
      - split. {
        unfold exclude_mem.
        unfold exclude_one_mem_state.
        split.
        * simpl.
          destruct (Int64.eq a a) eqn : J.
          ++ tauto.
          ++ rewrite Int64.eq_true in J.
            discriminate.
        * unfold exp_state.
          unfold state_subst; simpl.
          exists x.
          assert((  {|
          env := s.(env);
          mem := fun x0 : int64 =>
                 if Int64.eq x0 a
                 then Some x
                 else if Int64.eq x0 a then None else s.(mem) x0 |}) = s). {
            assert((fun x0 : int64 =>
            if Int64.eq x0 a then Some x else if Int64.eq x0 a then None else s.(mem) x0) = s.(mem)). {
              apply functional_extensionality.
              intros.
              pose proof Int64.eq_spec x0 a.
              destruct (Int64.eq x0 a) eqn : K.
              ++ rewrite H5.
                 rewrite H2.
                 reflexivity.
              ++ reflexivity. 
            }
            rewrite H5.
            destruct s.
            simpl.
            reflexivity.
          }
          rewrite ! H5.
          tauto.
      }
      split. {
        unfold one_mem_state.
        simpl.
        reflexivity.
      }
      split. {
        unfold exclude_one_mem_state.
        simpl.
        reflexivity.
      }
      intros. simpl.
      pose proof Int64.eq_spec i a.
      destruct (Int64.eq i a) eqn : I.
      * left.
        rewrite H5.
        tauto.
      * right.
        tauto.
    }
    specialize (H H0 H1 H2).
    clear H0 H1 H2.
    apply (hoare_conseq_post _ _ _ _ _ _ _ _ H); [| apply false_derives_all| apply false_derives_all].
    clear H.
    unfold derives, andp, exclude_mem, expr_equal_to, store, sepcon.
    intros.
    destruct H as [s1 [s2 [? [? [? [? ?]]]]]].
    destruct H.
    destruct H0.
    unfold exp_state in H5.
    destruct H5 as [v ?].
    destruct H5 as [[? ?] ?].
    specialize (HT (state_subst s2 a v) H5).
    destruct HT.
    apply H9.
    simpl.
    unfold asgn_deref_sem_nrm.
    exists a, a0.
    split; [auto | split; auto].
    split. {
      unfold state_subst; simpl.
      pose proof Int64.eq_spec a a.
      destruct (Int64.eq a a).
      + discriminate.
      + contradiction.
    }
    split. {
      specialize (H3 a).
      destruct H3.
      + destruct H3.
        rewrite H3, H.
        reflexivity.
      + destruct H3.
        rewrite H in H10.
        discriminate. 
    }
    split. {
      intros.
      unfold state_subst; simpl.
      rewrite H2.
      reflexivity.
    }
    intros.
    unfold state_subst; simpl.
    pose proof Int64.eq_spec p a.
    destruct (Int64.eq p a).
    - rewrite H11 in H10; contradiction.
    - specialize (H3 p).
      specialize (H4 p H11).
      destruct H3; destruct H3.
      * rewrite H4 in H3.
        rewrite H3.
        rewrite H12.
        reflexivity.
      * rewrite H3.
        reflexivity.
  + apply (hoare_seq P (fun s => exists x: state, P x /\ (eval_com c1).(nrm) x s) Q).
    - apply IHc1.
      intros.
      split. {
        intros.
        specialize (HT s1 H).
        destruct HT.
        apply H1.
        simpl.
        unfold_RELS_tac.
        tauto.
      }
      split. {
        intros.
        exists s1.
        tauto.
      }
      split. {
        intros.
        specialize (HT s1 H).
        destruct HT as [? [? [? ?]]].
        apply (H3 s2).
        simpl.
        unfold_RELS_tac.
        tauto.
      }
      intros.
      specialize (HT s1 H).
      destruct HT as [? [? [? ?]]].
      apply (H4 s2).
      simpl.
      unfold_RELS_tac.
      tauto.
    - apply IHc2.
      intros.
      destruct H, H.
      specialize (HT x).
      split. {
        specialize (HT H); destruct HT.
        intros.
        apply H1.
        simpl; unfold_RELS_tac.
        right.
        exists s1.
        tauto.
      }
      split. {
        specialize (HT H).
        destruct HT.
        intros.
        destruct H2.
        apply H2.
        simpl.
        unfold_RELS_tac.
        exists s1; tauto.
      }
      split. {
        intros.
        specialize (HT H).
        destruct HT as [? [? [? ?]]].
        apply (H4 s2).
        simpl.
        unfold_RELS_tac.
        right.
        exists s1.
        tauto.
      }
      intros.
      specialize (HT H).
      destruct HT as [? [? [? ?]]].
      apply (H5 s2).
      simpl.
      unfold_RELS_tac.
      right.
      exists s1.
      tauto.
  + apply hoare_if.
    - specialize (IHc1 Assn(P && (eb2assn e)) Q).
      apply IHc1.
      intros.
      split. {
        specialize (HT s1).
        revert H. assn_unfold.
        intros.
        destruct H.
        specialize (HT H).
        destruct HT. apply H2.
        simpl.
        unfold_RELS_tac.
        left; right.
        exists s1.
        unfold eb2assn in H1.
        destruct H1.
        unfold test_true.
        unfold_RELS_tac.
        split.
        * split; auto.
          exists x; tauto.
        * tauto.
      }
      split. {
        specialize (HT s1).
        revert H. assn_unfold.
        intros.
        destruct H.
        specialize (HT H).
        destruct HT.
        destruct H3.
        apply H3.
        simpl.
        unfold_RELS_tac.
        left.
        exists s1.
        unfold eb2assn in H1.
        destruct H1.
        unfold test_true.
        unfold_RELS_tac.
        split.
        * split; auto.
          exists x; tauto.
        * tauto.
      }
      specialize (HT s1).
      revert H. assn_unfold.
      intros.
      destruct H.
      specialize (HT H).
      destruct HT as [? [? [? ?]]].
      split. {
        intros.
        apply H3.
        simpl.
        unfold_RELS_tac.
        left.
        exists s1.
        split; auto.
        unfold test_true; unfold_RELS_tac.
        split; auto.
      }
      intros.
      apply H4.
      simpl.
      unfold_RELS_tac.
      left.
      exists s1.
      split; auto.
      unfold test_true; unfold_RELS_tac.
      split; auto.
    - specialize (IHc2 Assn(P && (eb2assn_not e)) Q).
      apply IHc2.
      intros.
      split. {
        specialize (HT s1).
        revert H. assn_unfold.
        intros.
        destruct H.
        specialize (HT H).
        destruct HT; apply H2.
        simpl.
        unfold_RELS_tac.
        right.
        exists s1.
        unfold eb2assn_not in H1.
        destruct H1.
        unfold test_false.
        unfold_RELS_tac.
        split.
        * split; auto.
          destruct H1.
          rewrite <- H4.
          pose proof Int64.repr_signed x.
          rewrite H5.
          tauto.
        * tauto. 
      }
      specialize (HT s1).
      revert H. assn_unfold.
      intros.
      destruct H.
      specialize (HT H).
      destruct HT as [? [? [? ?]]].
      split. {
        intros.
        apply H2.
        simpl.
        unfold_RELS_tac.
        right.
        exists s1.
        unfold eb2assn_not in H0.
        destruct H0.
        unfold test_false.
        unfold_RELS_tac.
        split.
        * split; auto.
          destruct H0.
          rewrite <- H6.
          pose proof Int64.repr_signed x.
          rewrite H7.
          tauto.
        * tauto. 
      }
      split. {
        intros.
        apply H3.
        simpl.
        unfold_RELS_tac.
        right.
        exists s1.
        split; auto.
        unfold test_false; unfold_RELS_tac.
        split; auto.
        unfold eb2assn_not in H0.
        destruct H0 as [x [? ?]].
        rewrite <- H6.
        pose proof Int64.repr_signed x.
        rewrite H7.
        tauto.
      }
      intros.
      apply H4.
      simpl.
      unfold_RELS_tac.
      right.
      exists s1.
      split; auto.
      unfold test_false; unfold_RELS_tac.
      split; auto.
      unfold eb2assn_not in H0.
      destruct H0 as [x [? ?]].
      rewrite <- H6.
      pose proof Int64.repr_signed x.
      rewrite H7.
      tauto.
    - intros.
      specialize (HT s H).
      destruct HT. apply H1.
      simpl. unfold_RELS_tac. 
      tauto.
  + pose proof wp_invariant e c Q.
    specialize (IHc Assn((wp (CWhile e c) Q asrt_false asrt_false) && (eb2assn e))  (wp (CWhile e c) Q asrt_false asrt_false)).
    unfold valid in H.
    apply IHc in H.
    apply hoare_while in H. {
      apply (hoare_conseq _ _ _ _ _ _ _ _ _ H).
      + unfold derives.
        intros.
        unfold wp.
        specialize (HT _ H0).
        destruct HT as [? [? [? ?]]].
        tauto.
      + unfold derives, orp, wp, asrt_false, eb2assn_not, andp.
        intros.
        destruct H0; auto.
        destruct H0.
        destruct H0 as [? [? [? ?]]].
        destruct H1 as [i [? ?]].
        apply (H2 s).
        simpl.
        unfold_RELS_tac.
        exists (S O).
        simpl.
        unfold_RELS_tac.
        right.
        unfold test_false.
        unfold_RELS_tac.
        split; auto.
        rewrite <- H5.
        rewrite Int64.repr_signed.
        apply H1.
      + apply false_derives_all.
      + apply false_derives_all.  
    }
    intros.
    unfold wp in H0.
    destruct H0.
    apply H0.
    simpl.
    unfold_RELS_tac.
    exists (S O).
    simpl.
    unfold_RELS_tac.
    right.
    tauto.
  + pose proof hoare_for
    (wp (c1) (wp (CFor CSkip e c2 c3) Q asrt_false asrt_false) asrt_false asrt_false)
    (wp c2 (wp (CFor CSkip e c2 c3) Q asrt_false asrt_false) asrt_false asrt_false)
    (wp (CFor CSkip e c2 c3) Q asrt_false asrt_false)
    Q e c1 c2 c3.
    assert(    provable
    {{(wp c1 (wp (CFor CSkip e c2 c3) Q asrt_false asrt_false)
         asrt_false asrt_false)}} for {c1} e {c2}{c3}
    {{(orp
         (andp (wp (CFor CSkip e c2 c3) Q asrt_false
                  asrt_false) (eb2assn_not e)) Q),
    asrt_false, asrt_false}}). {
      apply H; clear H.
      + pose proof for_P_to_R e c1 c2 c3 Q.
        apply IHc1.
        unfold valid in H.
        tauto.
      + intros.
        unfold wp in H.
        destruct H as [? [? [? ?]]].
        apply H.
        simpl.
        unfold_RELS_tac.
        right.
        exists s. split; auto.
        exists (S O).
        simpl.
        unfold_RELS_tac; right; tauto.
      + apply IHc3.
        pose proof for_R_to_Q.

    }
  + pose proof hoare_do_while (wp (CDoWhile c e) Q asrt_false asrt_false) (wp (CWhile e c) Q asrt_false asrt_false) Q e c.
    assert(    provable
      {{(wp (CDoWhile c e) Q asrt_false asrt_false)}}
      do {c}while e
      {{(orp (andp (wp (CWhile e c) Q asrt_false asrt_false) (eb2assn_not e)) Q), asrt_false,
      asrt_false}}). {
      apply H.
      + pose proof wp_inv_do_while_to_while e c Q.
        unfold valid in H0.
        apply IHc, H0.
      + pose proof wp_invariant e c Q.
        unfold valid in H0.
        apply IHc, H0.
      + intros.
        clear IHc H HT.
        unfold wp in H0.
        destruct H0.
        clear H0.
        simpl in H.  
        revert H; unfold_RELS_tac; intros.
        apply H.
        clear H.
        exists (S O).
        simpl.
        unfold_RELS_tac.
        right.
        tauto.
    }
    apply (hoare_conseq _ _ _ _ _ _ _ _ _ H0).
    - apply wp_is_weakest.
      unfold valid.
      intros.
      specialize (HT s1 H1).
      destruct HT as [? [? [? ?]]].
      auto.
    - unfold orp.
      unfold derives.
      intros.
      destruct H1; auto.
      unfold andp in H1.
      destruct H1.
      unfold wp in H1.
      clear H0 H IHc.
      destruct H1 as [? [? [? ?]]].
      apply H0.
      simpl.
      unfold_RELS_tac.
      exists (S O).
      simpl.
      unfold_RELS_tac.
      right.
      revert H2. unfold eb2assn_not. unfold test_false. unfold_RELS_tac.
      split; auto.
      destruct H2 as [i [? ?]].
      assert (i = Int64.repr 0). {
        rewrite <- H4.
        pose proof Int64.repr_signed i.
        rewrite H5.
        reflexivity.
      }
      rewrite H5 in H2.
      apply H2.
    - apply false_derives_all.
    - apply false_derives_all. 
  + pose proof hoare_continue P.
    apply (hoare_conseq_post _ _ _ _ _ _ _ _ H); [apply false_derives_all | apply false_derives_all |].
    unfold derives.
    intros.
    specialize (HT s H0).
    destruct HT as [? [? [? ?]]].
    apply (H4).
    simpl.
    auto.
  + pose proof hoare_break P.
    apply (hoare_conseq_post _ _ _ _ _ _ _ _ H); [apply false_derives_all |  | apply false_derives_all].
    unfold derives.
    intros.
    specialize (HT s H0).
    destruct HT as [? [? [? ?]]].
    apply H3.
    simpl.
    auto.
Qed.
