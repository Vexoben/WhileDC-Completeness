Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
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
  fun s => forall s',
  ((eval_com c).(err) s -> False) /\
  ((eval_com c).(nrm) s s' -> Q s').

Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  valid {{wp c Q}} c {{Q}}.
Proof.
  intros.
  unfold valid.
  intros s1 s2.
  unfold wp.
  intros.
  split.
  + apply H.
  + intros.
    specialize (H s1).
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
  split; intros;
  apply H; tauto.
Qed.

Lemma wp_seq : forall P Q c1 c2,
    provable {{P}} c1 {{(wp c2 Q)}} -> 
    provable {{(wp c2 Q)}} c2 {{Q}} ->
    provable {{P}} (c1; c2) {{Q}}.
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
  split; intros.
  + specialize (H s').
    destruct H.
    split.
    - intros.
      apply H.
      revert H3; unfold_RELS_tac; intros.
      destruct H3 as [i ?].
      exists (S i).
      simpl.
      unfold_RELS_tac.
      left.
      exists s1.
      split. {
        unfold test_true.
        unfold eb2assn in H0.
        unfold_RELS_tac.
        tauto.
      }
      left.
      exists s2.
      tauto.
    - intros.
      apply H2.
      revert H3; unfold_RELS_tac; intros.
      destruct H3 as [i ?].
      exists (S i).
      simpl.
      unfold_RELS_tac.
      left.
      exists s1.
      split. {
        unfold test_true.
        unfold eb2assn in H0.
        unfold_RELS_tac.
        tauto.
      }
      exists s2.
      tauto.
  + specialize (H s1); destruct H.
    apply H.
    unfold_RELS_tac.
    exists (S O).
    simpl.
    unfold_RELS_tac.
    left.
    exists s1.
    split. {
      unfold test_true.
      unfold eb2assn in H0.
      unfold_RELS_tac.
      tauto.
    }
    right; tauto.
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
      specialize (HT s s H0).
      destruct HT.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
      assert ((eval_r e).(err) s -> False) by tauto.
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
      specialize (HT s s H).
      destruct HT.
      simpl in H3.
      revert H3; unfold_RELS_tac; intros.
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
    apply (hoare_conseq_post _ _ _ _ H).
    clear H.
    unfold derives, andp, exclude_mem, expr_equal_to, store, sepcon.
    intros.
    destruct H as [s1 [s2 [? [? [? [? ?]]]]]].
    destruct H.
    destruct H0.
    unfold exp_state in H5.
    destruct H5 as [v ?].
    destruct H5 as [[? ?] ?].
    specialize (HT (state_subst s2 a v) s H5).
    destruct HT.
    apply H8.
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
  + assert(P |-- (exp64 (fun a:int64 => (andp P (expr_equal_to e1 a))))). {
      unfold derives.
      unfold exp64.
      unfold expr_equal_to.
      unfold andp.
      intros.
      specialize (HT s s H).
      destruct HT.
      simpl in H1.
      revert H1; unfold_RELS_tac; intros.
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
      specialize (HT s s H0).
      destruct HT.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
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
      specialize (HT s s H).
      destruct HT.
      simpl in H3.
      revert H3; unfold_RELS_tac; intros.
      assert(asgn_deref_sem_err (eval_r e1).(nrm) s -> False) by tauto.
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
    specialize (H H0 H1 H2).
    clear H0 H1 H2.
    apply (hoare_conseq_post _ _ _ _ H).
    clear H.
    unfold derives, andp, exclude_mem, expr_equal_to, store, sepcon.
    intros.
    destruct H as [s1 [s2 [? [? [? [? ?]]]]]].
    destruct H.
    destruct H0.
    unfold exp_state in H5.
    destruct H5 as [v ?].
    destruct H5 as [[? ?] ?].
    specialize (HT (state_subst s2 a v) s H5).
    destruct HT.
    apply H8.
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
      split.
      * exists s1.
        tauto.
      * intros.
        specialize (HT s1 s1 H).
        destruct HT.
        apply H2.
        simpl.
        unfold_RELS_tac.
        tauto.
    - apply IHc2.
      intros.
      destruct H,H.
      specialize (HT x s2).
      split. {
        specialize (HT H).
        destruct HT.
        intros.
        apply H1.
        simpl.
        unfold_RELS_tac.
        exists s1; tauto.
      }
      specialize (HT H); destruct HT.
      intros.
      apply H2.
      simpl; unfold_RELS_tac.
      right.
      exists s1.
      tauto.
  + apply hoare_if.
    - specialize (IHc1 Assn(P && (eb2assn e)) Q).
      apply IHc1.
      intros.
      split. {
        specialize (HT s1 s2).
        revert H. assn_unfold.
        intros.
        destruct H.
        specialize (HT H).
        destruct HT; apply H2.
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
      specialize (HT s1 s2).
      revert H. assn_unfold.
      intros.
      destruct H.
      specialize (HT H).
      destruct HT; apply H3.
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
    - specialize (IHc2 Assn(P && (eb2assn_not e)) Q).
      apply IHc2.
      intros.
      split. {
        specialize (HT s1 s2).
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
      specialize (HT s1 s2).
      revert H. assn_unfold.
      intros.
      destruct H.
      specialize (HT H).
      destruct HT; apply H3.
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
    - intros.
      specialize (HT s s H).
      destruct HT; apply H2.
      simpl. unfold_RELS_tac. 
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
    - intros.
      unfold wp in H0.
      specialize (H0 s).
      destruct H0.
      apply H0.
      simpl.
      unfold_RELS_tac.
      exists (S O).
      simpl.
      unfold_RELS_tac.
      right; tauto.
Qed.
