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
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Module HoareWhileDC.
Import Lang_While.
Import  Lang_WhileDC
        DntSem_WhileDC.

(*
Notation "x < y" := (ELt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom expr_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom expr_entry at level 10).*)
Notation "x" := x
  (in custom expr_entry at level 0, x constr at level 0).
Notation "( x )" := x
  (in custom expr_entry at level 0, x custom expr_entry at level 0).
Notation "x = e" := (CAsgnVar x e)
  (in custom expr_entry at level 18, no associativity).
Notation "* e1 ::= e2" := (CAsgnDeref e1 e2)
  (in custom expr_entry at level 17, no associativity).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom expr_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom expr_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99,
   c2 custom expr_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99).
Notation "'do' '{' c1 '}' 'while' e" := (CDoWhile c1 e)
  (in custom expr_entry at level 19,
  e custom expr_entry at level 5,
  c1 custom expr_entry at level 99).
Notation "'for' '{' c0 '}' e '{' c1 '}' '{' c2 '}'" := (CFor c0 e c1 c2)
  (in custom expr_entry at level 19,
  e custom expr_entry at level 5,
  c0 custom expr_entry at level 99,
  c1 custom expr_entry at level 99,
  c2 custom expr_entry at level 99).

(** 首先定义断言。*)

Definition assertion: Type := state -> Prop.

(* (s.(mem) i = None /\ s1.(mem) i = None /\ s2.(mem) i = None) *)

Definition sepcon(P Q: assertion) : assertion :=
  fun s => (exists s1 s2 : state,
     P s1 /\ Q s2 /\ s.(env) = s1.(env) /\ s.(env) = s2.(env)
     /\ (forall i : int64, 
        (s.(mem) i = s1.(mem) i /\ s2.(mem) i = None) \/ (s.(mem) i = s2.(mem) i /\ s1.(mem) i = None))).

Definition store(a : int64)(b : val) : assertion := 
  fun s => (s.(mem) a = Some b /\ (forall i : int64, i <> a -> s.(mem) i = None)).

Definition derives (P Q: assertion): Prop :=
  forall s, P s -> Q s.

Definition logical_equiv (P Q: assertion): Prop :=
  forall s, P s <-> Q s.

Definition andp (P Q: assertion): assertion := fun s => P s /\ Q s.

Definition orp (P Q: assertion): assertion := fun s => P s \/ Q s.

Definition exp (P: val -> assertion): assertion := fun s => exists n, P n s.

(** 下面的Notation定义可以跳过*)

Declare Custom Entry assn_entry.

Notation "( x )" := x
  (in custom assn_entry, x custom assn_entry at level 99).
Notation "x" := x
  (in custom assn_entry at level 0, x constr at level 0).
Notation "'Assn' ( P )" := P
  (at level 2, P custom assn_entry at level 99).
Notation "f x" := (f x)
  (in custom assn_entry at level 1, only parsing,
   f custom assn_entry,
   x custom assn_entry at level 0).

Notation "x && y" := (andp x y)
  (in custom assn_entry at level 14, left associativity).

Notation "x * y" := (sepcon x y)
  (in custom assn_entry at level 14, left associativity).

Notation "'exists' x , P" := (exp (fun x: Z => P))
  (in custom assn_entry at level 20,
      x constr at level 0,
      P custom assn_entry).

Notation " P |-- Q " := (derives P Q)
  (at level 80, no associativity).

Notation " P --||-- Q " := (logical_equiv P Q)
  (at level 80, no associativity).

(** 下面定义霍尔三元组。*)

Inductive HoareTriple: Type :=
| BuildHoareTriple: assertion -> com -> assertion -> assertion -> assertion -> HoareTriple.

Notation "{{ P }}  c  {{ Q_nrm , Q_brk , Q_cnt }}" :=
  (BuildHoareTriple P c Q_nrm Q_brk Q_cnt) (at level 1,
                            P custom assn_entry at level 99,
                            Q_nrm custom assn_entry at level 99,
                            Q_brk custom assn_entry at level 99,
                            Q_cnt custom assn_entry at level 99,
                            c custom expr_entry at level 99).

(** 一个布尔表达式为真是一个断言：*)

Definition eb2assn (b: expr): assertion := 
  fun s => exists i, (eval_r b).(nrm) s i /\ Int64.signed i <> 0.

Definition eb2assn_not (b: expr): assertion := 
  fun s => exists i, (eval_r b).(nrm) s i /\ Int64.signed i = 0.

Notation "[[ e ]]" := (eb2assn e)
  (in custom assn_entry at level 0,
      e custom expr_entry at level 99,
      only printing).

(** 断言中描述整数的逻辑表达式（区分于程序表达式）：*)

(*
Definition exprZ: Type := state -> Z.
*)

Definition exprVal: Type := state -> option val.
(* 
(** 一个程序中的整数类型可以用作逻辑表达式：*)

Definition ei2exprZ (e: expr_int): exprZ :=
  eval_expr_int e.

(** 断言中的等号：*)

Definition exprZ_eq (e1 e2: exprZ): assertion :=
  fun s => e1 s = e2 s.

(** 程序状态中的替换：*)

Definition state_subst (s: state) (x: var_name) (v: Z): state :=
  fun y =>
    if String.eqb x y
    then v
    else s y.

(** 断言中的替换：*)

Definition assn_subst (P: assertion) (x: var_name) (v: exprZ): assertion :=
  fun s =>
    P (state_subst s x (v s)).

Definition exprZ_subst (u: exprZ) (x: var_name) (v: exprZ): exprZ :=
  fun s =>
    u (state_subst s x (v s)). *)

(** 下面的Notation定义可以跳过*)
(* 

Notation "[[ e ]]" := (ei2exprZ e)
  (in custom assn_entry at level 0,
      e custom expr_entry at level 99,
      only printing). *)
(* 
Ltac any_expr e :=
  match goal with
  | |- assertion => exact (eb2assn e)
  | |- exprZ => exact (ei2exprZ e)
  | _ => match type of e with
         | expr_bool => exact (eb2assn e)
         | expr_int => exact (ei2exprZ e)
         end
  end.

Notation "[[ e ]]" := (ltac:(any_expr e))
  (in custom assn_entry,
      e custom expr_entry at level 99,
      only parsing).

Notation "u == v" := (exprZ_eq u v)
  (in custom assn_entry at level 10,
      u custom assn_entry,
      v custom assn_entry,
      no associativity).

Tactic Notation "unfold_substs" :=
  unfold exprZ_subst, assn_subst.

Tactic Notation "unfold_substs" "in" ident(H) :=
  unfold exprZ_subst, assn_subst in H.

Notation "'exprZ_subst' u x v" := (exprZ_subst u x v)
  (in custom assn_entry at level 1,
      u custom assn_entry at level 0,
      x custom assn_entry at level 0,
      v custom assn_entry at level 0).

Notation "'assn_subst' P x v" := (assn_subst P x v)
  (in custom assn_entry at level 1,
      P custom assn_entry at level 0,
      x custom assn_entry at level 0,
      v custom assn_entry at level 0). *)

(** 下面定义有效：*)

Definition valid: HoareTriple -> Prop :=
  fun ht =>
  match ht with
  | BuildHoareTriple P c Q_nrm Q_brk Q_cnt =>
      forall s1,
        (P s1) -> (
          ((eval_com c).(err) s1 -> False)
          /\ (forall s2, ((eval_com c).(nrm) s1 s2 -> Q_nrm s2))
          /\ (forall s2, ((eval_com c).(brk) s1 s2 -> Q_brk s2))
          /\ (forall s2, ((eval_com c).(cnt) s1 s2 -> Q_cnt s2))
        )
  end.

Definition asrt_false : assertion :=
  fun s => False.

Lemma hoare_skip_sound:
  forall P: assertion,
    valid {{ P }} skip {{ P , asrt_false, asrt_false }}.
Proof.
  simpl.
  intros.
  split. {
    unfold_RELS_tac.
    tauto.
  }
  split. {
    intros.
    subst s2.
    tauto.
  }
  split. {
    unfold_RELS_tac.
    intros.
    contradiction.
  }
  unfold_RELS_tac.
  intros.
  contradiction.
Qed.

Lemma hoare_break_sound:
  forall P: assertion,
    valid {{ P }} CBreak {{ asrt_false, P, asrt_false }}.
Proof.
  simpl.
  intros.
  split. {
    unfold_RELS_tac.
    tauto.
  }
  split. {
    unfold_RELS_tac.
    intros.
    contradiction.
  }
  split. {
  intros.
    subst s2.
    tauto.
  }
  unfold_RELS_tac.
  intros.
  contradiction.
Qed.

Lemma hoare_continue_sound:
  forall P: assertion,
    valid {{ P }} CContinue {{ asrt_false, asrt_false, P }}.
Proof.
  simpl.
  intros.
  split. {
    unfold_RELS_tac.
    tauto.
  }
  split. {
    unfold_RELS_tac.
    intros.
    contradiction.
  }
  split. {
    unfold_RELS_tac.
    intros.
    contradiction.
  }
  intros.
  subst s2.
  tauto.
Qed.

Lemma hoare_seq_sound:
  forall (P Q R R_brk R_cnt: assertion) (c1 c2: com),
    valid (BuildHoareTriple P c1 Q R_brk R_cnt) ->
    valid (BuildHoareTriple Q c2 R R_brk R_cnt) ->
    valid (BuildHoareTriple P (CSeq c1 c2) R R_brk R_cnt).
Proof.
  simpl.
  unfold_RELS_tac.
  intros.
  split. {
    intros.
    destruct H2.
    - specialize (H s1 H1).
      destruct H.
      tauto.
    - destruct H2 as [s1' [? ?]].
      specialize (H s1 H1).
      destruct H as [? [? [? ?]]].
      specialize (H4 s1' H2).
      specialize (H0 s1' H4).
      destruct H0 as [? [? [? ?]]].
      tauto.
  }
  split. {
    intros.
    destruct H2 as [s1' [? ?]].
    specialize (H _ H1).
    destruct H as [? [? [? ?]]].
    specialize (H4 _ H2).
    specialize (H0 s1' H4).
    destruct H0 as [? [? [? ?]]].
    apply (H7 s2 H3).
  }
  split. {
    intros.
    destruct H2.
    + specialize (H s1 H1).
      destruct H as [? [? [? ?]]].
      apply (H4 _ H2).
    + specialize (H s1 H1).
      destruct H as [? [? [? ?]]].
      destruct H2 as [s1' [? ?]].
      specialize (H3 _ H2).
      specialize (H0 _ H3).
      destruct H0 as [? [? [? ?]]].
      apply (H8 _ H6).
  }
  intros.
  destruct H2.
  + specialize (H s1 H1).
    destruct H as [? [? [? ?]]].
    apply (H5 _ H2).
  + specialize (H s1 H1).
    destruct H as [? [? [? ?]]].
    destruct H2 as [s1' [? ?]].
    specialize (H3 _ H2).
    specialize (H0 _ H3).
    destruct H0 as [? [? [? ?]]].
    apply (H9 _ H6).
Qed.

(** 习题：*)
Lemma hoare_if_sound:
  forall (P Q Q_brk Q_cnt: assertion) (e: expr) (c1 c2: com),
    valid (BuildHoareTriple (andp P (eb2assn e)) c1 Q Q_brk Q_cnt) ->
    valid (BuildHoareTriple (andp P (eb2assn_not e)) c2 Q Q_brk Q_cnt) ->
    (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
    valid (BuildHoareTriple P (CIf e c1 c2) Q Q_brk Q_cnt).
Proof.
  simpl.
  unfold if_sem.
  unfold andp, eb2assn, eb2assn_not.
  unfold_RELS_tac.
  simpl.
  unfold not_sem.
  intros.
  split. {
    intros.
    destruct H3; [ destruct H3 |].
    + apply (H1 _ H2 H3).
    + destruct H3 as [s1' [? ?]].
      unfold test_true in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H s1).
      assert((eval_com c1).(err) s1 -> False) by tauto.
      tauto.
    + destruct H3 as [s1' [? ?]].
      unfold test_false in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H0 s1).
      assert((exists i : int64, (eval_r e).(nrm) s1 i /\ Int64.signed i = 0)). {
        exists (Int64.repr 0).
        rewrite Int64.signed_repr.
        tauto.
        pose proof Int64.max_signed_pos.
        pose proof Int64.min_signed_neg.
        lia.
      }
      assert((eval_com c2).(err) s1 -> False) by tauto.
      tauto.
  }
  split. {
    intros.
    destruct H3.
    + destruct H3 as [s1' [? ?]].
      unfold test_true in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H s1).
      assert(forall s2 : state, (eval_com c1).(nrm) s1 s2 -> Q s2) by tauto.
      apply (H5 _ H4).
    + destruct H3 as [s1' [? ?]].
      unfold test_false in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H0 s1).
      assert((exists i : int64, (eval_r e).(nrm) s1 i /\ Int64.signed i = 0)). {
        exists (Int64.repr 0).
        rewrite Int64.signed_repr.
        tauto.
        pose proof Int64.max_signed_pos.
        pose proof Int64.min_signed_neg.
        lia.
      }
      assert(forall s2 : state, (eval_com c2).(nrm) s1 s2 -> Q s2) by tauto.
      apply (H6 _ H4).
  }
  split. {
    intros.
    destruct H3.
    + destruct H3 as [s1' [? ?]].
      unfold test_true in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H s1).
      assert(forall s2 : state, (eval_com c1).(brk) s1 s2 -> Q_brk s2) by tauto.
      apply (H5 _ H4).
    + destruct H3 as [s1' [? ?]].
      unfold test_false in H3.
      revert H3; unfold_RELS_tac; intros.
      destruct H3; subst s1'.
      specialize (H0 s1).
      assert((exists i : int64, (eval_r e).(nrm) s1 i /\ Int64.signed i = 0)). {
        exists (Int64.repr 0).
        rewrite Int64.signed_repr.
        tauto.
        pose proof Int64.max_signed_pos.
        pose proof Int64.min_signed_neg.
        lia.
      }
      assert(forall s2 : state, (eval_com c2).(brk) s1 s2 -> Q_brk s2) by tauto.
      apply (H6 _ H4).
  }
  intros.
  destruct H3.
  + destruct H3 as [s1' [? ?]].
    unfold test_true in H3.
    revert H3; unfold_RELS_tac; intros.
    destruct H3; subst s1'.
    specialize (H s1).
    assert(forall s2 : state, (eval_com c1).(cnt) s1 s2 -> Q_cnt s2) by tauto.
    apply (H5 _ H4).
  + destruct H3 as [s1' [? ?]].
    unfold test_false in H3.
    revert H3; unfold_RELS_tac; intros.
    destruct H3; subst s1'.
    specialize (H0 s1).
    assert((exists i : int64, (eval_r e).(nrm) s1 i /\ Int64.signed i = 0)). {
      exists (Int64.repr 0).
      rewrite Int64.signed_repr.
      tauto.
      pose proof Int64.max_signed_pos.
      pose proof Int64.min_signed_neg.
      lia.
    }
    assert(forall s2 : state, (eval_com c2).(cnt) s1 s2 -> Q_cnt s2) by tauto.
    apply (H6 _ H4).
Qed.

(** 习题：*)
Lemma hoare_while_sound:
  forall (P P_brk: assertion) (e: expr) (c: com),
    valid (BuildHoareTriple (andp P (eb2assn e)) c P P_brk P) ->
    (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
    valid (BuildHoareTriple P (CWhile e c) (orp (andp P (eb2assn_not e)) P_brk) asrt_false asrt_false).
Proof.
  simpl.
  unfold while_sem.
  unfold andp, eb2assn, eb2assn_not.
  unfold_RELS_tac.
  simpl.
  unfold not_sem.
  intros.
  split. {
    intros.
    destruct H2 as [i ?].
    revert s1 H1 H2.
    induction i.
    + intros.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
      tauto.
    + intros.
      simpl in H2.
      revert H2; unfold_RELS_tac; intros.
      destruct H2.
      - destruct H2 as [s1' ?].
        destruct H2.
        revert H2; unfold test_true; unfold_RELS_tac; intros.
        destruct H2; subst s1'.
        destruct H3; [destruct H3 |].
        * destruct H3 as [s2 [? ?]].
          specialize (H s1).
          assert(forall s2 : state, (eval_com c).(nrm) s1 s2 -> P s2) by tauto.
          specialize (H5 s2 H3).
          apply (IHi _ H5 H4).
        * destruct H3 as [s2 [? ?]].
          specialize (H s1).
          assert(forall s2 : state, (eval_com c).(cnt) s1 s2 -> P s2) by tauto.
          specialize (H5 s2 H3).
          apply (IHi _ H5 H4).
        * specialize (H s1).
          assert((eval_com c).(err) s1 -> False) by tauto.
          tauto.
      - apply (H0 _ H1 H2).
  }
  split. {
    intros.
    destruct H2 as [i ?].
    unfold orp.
    revert s1 H1 H2.
    induction i; simpl; intros.
    + revert H2; unfold_RELS_tac; intros; tauto.
    + revert H2; unfold_RELS_tac; intros.
      destruct H2.
      - destruct H2 as [s1' [? ?]].
        revert H2; unfold test_true; unfold_RELS_tac; simpl; intros.
        destruct H2; subst s1'.
        specialize (H s1).
        destruct H3; [destruct H3 |].
        * assert(forall s2 : state, (eval_com c).(nrm) s1 s2 -> P s2) by tauto.
          destruct H3 as [s3 [? ?]].
          specialize (H4 s3 H3).
          specialize (IHi _ H4 H5).
          tauto.
        * assert(forall s2 : state, (eval_com c).(cnt) s1 s2 -> P s2) by tauto.
          destruct H3 as [s3 [? ?]].
          specialize (H4 s3 H3).
          specialize (IHi _ H4 H5).
          tauto.
        * right.
          assert(forall s2 : state, (eval_com c).(brk) s1 s2 -> P_brk s2) by tauto.
          apply (H4 _ H3).
      - unfold test_false in H2.
        revert H2; unfold_RELS_tac; intros.
        destruct H2; subst s2.
        left.
        split; auto.
        exists (Int64.repr 0).
        split; auto.
  }
  split. {
    intros. contradiction.
  }
  intros. contradiction.
Qed.

Lemma hoare_do_while_sound:
  forall (P R R_brk: assertion) (e: expr) (c: com),
  valid (BuildHoareTriple P c R R_brk R) ->
  valid (BuildHoareTriple (andp R (eb2assn e)) c R R_brk R) ->
  (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
  valid (BuildHoareTriple P (CDoWhile c e) (orp (andp R (eb2assn_not e)) R_brk) asrt_false asrt_false).
Proof.
  simpl.
  unfold_RELS_tac.
  unfold asrt_false.
  intros.
  specialize (H s1 H2).
  destruct H as [? [? [? ?]]].
  split. {
    intros.
    destruct H6; auto.
    destruct H6 as [s2 ?].
    destruct H6.
    destruct H7 as [i ?].
    destruct H6.
    + specialize (H3 s2 H6).
      clear H H4 H5 H2 H6.
      revert s2 H3 H7.
      induction i; simpl; intros.
      - simpl in H7.
        revert H7.
        unfold_RELS_tac; 
        tauto.
      - simpl in H7.
        revert H7.
        unfold_RELS_tac.
        intros.
        destruct H7.
        * specialize (H0 s2).
          destruct H as [s2' [? ?]].
          revert H; unfold test_true; unfold_RELS_tac; intros.
          destruct H; subst s2'.
          assert(((andp R (eb2assn e))) s2). {
            unfold andp, eb2assn.
            auto.
          }
          specialize (H0 H4). clear H4.
          destruct H0 as [? [? [? ?]]].
          destruct H2; [destruct H2 |].
          ++ destruct H2 as [s3 [? ?]].
             specialize (H4 s3 H2).
             apply (IHi s3); tauto.
          ++ destruct H2 as [s3 [? ?]].
             specialize (H6 s3 H2).
             apply (IHi s3); tauto.
          ++ tauto. 
        * specialize (H1 s2 H3).
          tauto.
    + specialize (H5 s2 H6).
      clear H H4 H3 H2 H6.
      revert s2 H5 H7.
      induction i; simpl; intros.
      - simpl in H7.
        revert H7.
        unfold_RELS_tac; 
        tauto.
      - simpl in H7.
        revert H7.
        unfold_RELS_tac.
        intros.
        destruct H7.
        * specialize (H0 s2).
          destruct H as [s2' [? ?]].
          revert H; unfold test_true; unfold_RELS_tac; intros.
          destruct H; subst s2'.
          assert(((andp R (eb2assn e))) s2). {
            unfold andp, eb2assn.
            auto.
          }
          specialize (H0 H3). clear H3.
          destruct H0 as [? [? [? ?]]].
          destruct H2; [destruct H2 |].
          ++ destruct H2 as [s3 [? ?]].
            specialize (H3 s3 H2).
            apply (IHi s3); tauto.
          ++ destruct H2 as [s3 [? ?]].
            specialize (H6 s3 H2).
            apply (IHi s3); tauto.
          ++ tauto. 
        * specialize (H1 s2 H5).
          tauto. 
  }
  split. {
    intros.
    destruct H6. {
      specialize (H4 s2 H6).
      unfold orp, andp, eb2assn_not.
      right. auto.
    }
    destruct H6 as [s3 [? ?]].
    unfold orp, andp, eb2assn_not.
    destruct H7 as [i ?].
    assert (R s3). {
      specialize (H3 s3).
      specialize (H5 s3).
      destruct H6; tauto.
    }
    clear H6 H2 H H3 H4 H5.
    revert s3 H8 H7.
    induction i.
    + simpl.
      unfold_RELS_tac; tauto.
    + simpl.
      unfold_RELS_tac.
      intros.
      destruct H7.
      - destruct H as [s3' [? ?]].
        revert H; unfold test_true; unfold_RELS_tac; intros.
        destruct H; subst s3'.
        assert ((andp R (eb2assn e)) s3). {
          unfold andp, eb2assn.
          tauto.
        }
        specialize (H0 s3 H3).
        destruct H0 as [? [? [? ?]]].
        destruct H2; [destruct H2 |].
        * destruct H2 as [s4 [? ?]].
          specialize (H4 s4 H2).
          specialize (IHi s4 H4 H7).
          tauto.
        * destruct H2 as [s4 [? ?]].
          specialize (H6 s4 H2).
          specialize (IHi s4 H6 H7).
          tauto.
        * specialize (H5 s2).
          right; tauto.
      - unfold test_false in H.
        revert H; unfold_RELS_tac; intros.
        destruct H; subst s3.
        left.
        split; auto.
        exists (Int64.repr 0).
        auto. 
  }
  auto.
Qed.

Lemma hoare_for_sound:
  forall (P Q R R_brk: assertion) (e: expr) (c1 c2 c3: com),  
  valid (BuildHoareTriple P c1 R asrt_false asrt_false) ->
  (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
  valid (BuildHoareTriple (andp R (eb2assn e)) c3 Q R_brk Q) ->
  valid (BuildHoareTriple Q c2 R asrt_false asrt_false) ->
  ((eval_com) c1).(brk) = ∅ -> ((eval_com) c1).(cnt) = ∅ ->
  ((eval_com) c2).(brk) = ∅ -> ((eval_com) c2).(cnt) = ∅ ->
  valid (BuildHoareTriple P (CFor c1 e c2 c3) (orp (andp R (eb2assn_not e)) R_brk) asrt_false asrt_false).
Proof.
  simpl.
  unfold_RELS_tac.
  unfold asrt_false.
  intros.
  clear H3 H4 H5 H6.
  pose proof H7. clear H7.
  specialize (H s1 H3).
  destruct H as [? [? [? ?]]].
  split. {
    intros.
    destruct H7.
    + apply H, H7.
    + destruct H7 as [s2 [? ?]].
      specialize (H4 s2 H7).
      destruct H8 as [i ?].
      clear H5 H6 H7 H3 H.
      revert s2 H4 H8.
      induction i; simpl; intros.
      - revert H8; unfold_RELS_tac; tauto.
      - revert H8; unfold_RELS_tac.
        intros.
        destruct H8. {
          destruct H as [s2' [? ?]].
          revert H; unfold test_true; unfold_RELS_tac; intros.
          destruct H. subst s2'.
          destruct H3; [destruct H3|].
          + destruct H3; [destruct H3|]. {
              destruct H3 as [s3 [? ?]].
              destruct H5 as [s4 [? ?]].
              assert((andp R (eb2assn e)) s2). {
                unfold eb2assn, andp.
                split; auto.
              }
              specialize (H1 s2 H7).
              destruct H1 as [? [? [? ?]]].
              specialize (H8 s3 H3).
              specialize (H2 s3 H8).
              destruct H2 as [? [? [? ?]]].
              specialize (H11 s4 H5).
              apply (IHi s4 H11 H6).
            }
            {
              destruct H3 as [s3 [? ?]].
              destruct H5 as [s4 [? ?]].
              assert((andp R (eb2assn e)) s2). {
                unfold eb2assn, andp.
                split; auto.
              }
              specialize (H1 s2 H7).
              destruct H1 as [? [? [? ?]]].
              specialize (H10 s3 H3).
              specialize (H2 s3 H10).
              destruct H2 as [? [? [? ?]]].
              specialize (H11 s4 H5).
              apply (IHi s4 H11 H6).
            }
            destruct H3 as [s3 [? ?]].
            assert((andp R (eb2assn e)) s2). {
              unfold eb2assn, andp.
              split; auto.
            }
            specialize (H1 s2 H6).
            destruct H1 as [? [? [? ?]]].
            specialize (H7 s3 H3).
            specialize (H2 s3 H7).
            destruct H2 as [? [? [? ?]]].
            tauto.
          + destruct H3 as [s3 [? ?]].
            assert((andp R (eb2assn e)) s2). {
              unfold eb2assn, andp.
              split; auto.
            }
            specialize (H1 s2 H6).
            destruct H1 as [? [? [? ?]]].
            specialize (H9 s3 H3).
            specialize (H2 s3 H9).
            destruct H2 as [? [? [? ?]]].
            tauto.
          + assert((andp R (eb2assn e)) s2). {
              unfold eb2assn, andp.
              split; auto.
            }
            specialize (H1 s2 H5).
            destruct H1 as [? [? [? ?]]].
            tauto.
        }
        apply (H0 s2 H4 H).
  }
  split. {
    intros.
    destruct H7 as [s3 [? ?]].
    destruct H8 as [i ?].
    unfold orp.
    specialize (H4 s3 H7).
    clear H7 H5 H6 H.
    revert s2 s3 H4 H8.
    induction i; simpl; intros.
    + revert H8; unfold_RELS_tac; tauto.
    + revert H8; unfold_RELS_tac; intros.
      destruct H8. {
        destruct H as [s3' [? ?]].
        revert H; unfold test_true; unfold_RELS_tac; intros.
        destruct H; subst s3'.
        destruct H5; [destruct H5 |].
        + destruct H5 as [s4 [? ?]].
          destruct H6 as [s5 [? ?]].
          assert((andp R (eb2assn e)) s3). {
            unfold eb2assn, andp.
            split; auto.
          }
          specialize (H1 s3 H8).
          destruct H1 as [? [? [? ?]]].
          specialize (H9 s4 H5).
          specialize (H2 _ H9).
          destruct H2 as [? [? [? ?]]].
          specialize (H12 s5 H6).
          specialize (IHi s2 s5 H12 H7).
          apply IHi.
        + destruct H5 as [s4 [? ?]].
          destruct H6 as [s5 [? ?]].
          assert((andp R (eb2assn e)) s3). {
            unfold eb2assn, andp.
            split; auto.
          }
          specialize (H1 s3 H8).
          destruct H1 as [? [? [? ?]]].
          specialize (H11 s4 H5).
          specialize (H2 _ H11).
          destruct H2 as [? [? [? ?]]].
          specialize (H12 s5 H6).
          specialize (IHi s2 s5 H12 H7).
          apply IHi.
        + assert((andp R (eb2assn e)) s3). {
            unfold eb2assn, andp.
            split; auto.
          }
          specialize (H1 s3 H6).
          destruct H1 as [? [? [? ?]]].
          right.
          apply (H8 s2 H5).
      }
      left.
      unfold andp.
      revert H; unfold test_false; unfold eb2assn_not; unfold_RELS_tac; intros.
      destruct H; subst s3.
      split; auto.
      exists (Int64.repr 0).
      auto.
  }
  tauto.
Qed.

Definition state_subst(s: state)(p:int64)(a:val) : state :=
  {|
    env := s.(env);
    mem := fun x => if (Int64.eq x p) then (Some a) else s.(mem) x;
  |}.  

Definition assn_subst (P: assertion) (x: var_name) (v: val): assertion :=
  fun s =>
    P (state_subst s (s.(env) x) v).

Lemma hoare_asgn_deref_fwd_sound:
  forall (P Q : assertion) (e1 e2 : expr) (a b: int64),
    (forall (s:state), P s -> ((eval_r e1).(nrm) s a)) ->
    (forall (s:state), P s -> ((eval_r e2).(nrm) s b)) ->
    derives P (exp (fun u => (sepcon (store a u) Q) )) ->
    valid ( {{P}} ( * (e1) ::= e2 ) {{(store a (Vint b)) * Q, asrt_false, asrt_false}} ).
Proof.
  simpl.
  unfold asgn_deref_sem_nrm.
  intros.
  unfold exp in H1.
  split; intros. {
    unfold derives in H1.
    specialize (H s1).
    specialize (H0 s1).
    specialize (H1 s1).
    pose proof H2.
    pose proof H2.
    pose proof H2.
    apply H in H4.
    apply H0 in H5.
    apply H1 in H6.
    clear H H0 H1.
    destruct H6.
    revert H3; unfold_RELS_tac; intros.
    destruct H3; [destruct H0 |].
    + apply (eval_r_both_err_and_nrm _ _ _ H4 H0).
    + apply (eval_r_both_err_and_nrm _ _ _ H5 H0).
    + unfold asgn_deref_sem_err in H0.
      destruct H0 as [v [? ?]].
      pose proof eval_r_sem_inj _ _ _ _ H0 H4.
      subst v.
      clear H0.
      unfold sepcon in H.
      destruct H as [s3 [s4 [? [? [? [? ?]]]]]].
      unfold store in H.
      destruct H.
      specialize (H7 a).
      destruct H7; destruct H7.
      - rewrite H7 in H1.
        rewrite H in H1.
        discriminate.
      - rewrite H in H9.
        discriminate.
  }
  split; intros. {
    destruct H3 as [i1 [i2 [? [ ? [? ? ]]]]].
    destruct H6 as [? [? ?]].
    unfold derives in H1.
    specialize (H s1).
    specialize (H0 s1).
    specialize (H1 s1).
    pose proof H2.
    pose proof H2.
    pose proof H2.
    apply H in H9.
    apply H0 in H10.
    apply H1 in H11.
    clear H H0 H1.
    destruct H11.
    unfold eval_r in H3. fold eval_r in H3.
    pose proof eval_r_sem_inj i1 a e1 s1.
    assert (i1 = a) by tauto.
    pose proof eval_r_sem_inj i2 b e2 s1.
    assert (i2 = b) by tauto.
    subst i1 i2.
    clear H0 H11 H9 H10.
    unfold sepcon.
    unfold sepcon in H.
    destruct H as [s11 [s12 ?]].
    exists (state_subst s11 a (Vint b)), s12.
    destruct H as [? [? [? [? ?]]]].
    split.
    + unfold store.
      split. 
      - simpl.
        destruct (Int64.eq a a) eqn : I; auto.
        pose proof Int64.eq_true a.
        rewrite H11 in I.
        discriminate.
      - intros.
        unfold store in H.
        simpl.
        destruct (Int64.eq i a) eqn : I.
        * pose proof Int64.eq_false i a.
          apply H12 in H11.
          rewrite H11 in I.
          discriminate.
        * destruct H.
          specialize (H12 i).
          auto.
    + split; auto.
      split.
      - simpl.
        rewrite <- H1.
        apply functional_extensionality.
        intros.
        specialize (H7 x0).
        rewrite H7.
        tauto.
      - split.
        * rewrite <- H9.
          apply functional_extensionality.
          intros.
          specialize (H7 x0).
          rewrite H7.
          tauto.
        * intros.
          simpl.
          pose proof Int64.eq_spec i a.
          destruct (Int64.eq i a) eqn : I.
          ++  left.
              pose proof Int64.same_if_eq i a.
              apply H12 in I; clear H11.
              subst i.
              specialize (H10 a).
              unfold store in H.
              destruct H.
              destruct H10; try tauto.
              destruct H10.
              rewrite H in H13.
              discriminate.
          ++  specialize (H10 i).
              destruct H10.
              --  left.
                  specialize (H8 i).
                  pose proof not_eq_sym H11.
                  apply H8 in H12.
                  rewrite <- H12.
                  tauto.
              --  right. 
                  specialize (H8 i).
                  pose proof not_eq_sym H11.
                  apply H8 in H12.
                  rewrite <- H12.
                  tauto.  
  }
  split; intros. {
    revert H3; unfold_RELS_tac; intros; tauto.
  }
  revert H3; unfold_RELS_tac; intros; tauto.
Qed.

Lemma hoare_asgn_var_fwd_sound:
  forall (P Q: assertion) (e: expr) (a b: int64) (x : var_name),
  (forall (s:state), P s -> ((eval_r e).(nrm) s b)) ->
  (forall (s:state), P s -> s.(env) x = a) ->
  derives P (exp (fun u => (sepcon (store a u) Q) )) ->
  valid ( {{P}} ( (x = e) ) {{(store a (Vint b)) * Q, asrt_false, asrt_false}}).
Proof.
  simpl.
  unfold asgn_deref_sem_nrm.
  intros.
  split; intros. {
    unfold derives in H1.
    specialize (H s1).
    specialize (H0 s1).
    specialize (H1 s1).
    pose proof H2.
    pose proof H2.
    pose proof H2.
    apply H in H4.
    apply H0 in H5.
    apply H1 in H6.
    clear H H0 H1.
    revert H3; unfold_RELS_tac; intros.
    destruct H3; [destruct H |].
    + tauto.
    + apply (eval_r_both_err_and_nrm _ _ _ H4 H).
    + unfold asgn_deref_sem_err in H.
      destruct H as [v [? ?]].
      rewrite H5 in H.
      subst v.
      unfold sepcon in H6.
      unfold exp in H6.
      destruct H6 as [n [s3 [s4 [? [? [? [? ?]]]]]]].
      unfold store in H.
      destruct H.
      specialize (H7 a).
      destruct H7; destruct H7.
      - rewrite H7 in H0.
        rewrite H in H0.
        discriminate.
      - rewrite H in H9.
        discriminate.
  }
  split; intros. {
    destruct H3 as [xp [xv [? [? [? [? [? ?]]]]]]].
    unfold derives in H1.
    specialize (H s1).
    specialize (H0 s1).
    specialize (H1 s1).
    pose proof H2.
    pose proof H2.
    pose proof H2.
    apply H in H9.
    apply H0 in H10.
    apply H1 in H11.
    clear H H0 H1.
    unfold exp in H11.
    destruct H11.
    pose proof eval_r_sem_inj b xv e s1.
    assert(b = xv) by tauto.
    subst xv.
    rewrite H3 in H10.
    subst xp.
    clear H0 H4.
    unfold sepcon.
    unfold sepcon in H.
    destruct H as [s11 [s12 ?]].
    exists (state_subst s11 a (Vint b)), s12.
    destruct H as [? [? [? [? ?]]]].
    split.
    + unfold store.
      split.
      - simpl.
        destruct (Int64.eq a a) eqn : I; auto.
        pose proof Int64.eq_true a.
        rewrite H11 in I.
        discriminate.
      - intros.
        unfold store in H.
        simpl.
        destruct (Int64.eq i a) eqn : I.
        * pose proof Int64.eq_false i a.
          apply H12 in H11.
          rewrite H11 in I.
          discriminate.
        * destruct H.
          specialize (H12 i).
          auto.
    + split; auto.
      split.
      - simpl.
        rewrite <- H1.
        apply functional_extensionality.
        intros.
        specialize (H7 x1).
        rewrite H7.
        tauto.
      - split.
        * rewrite <- H3.
          apply functional_extensionality.
          intros.
          specialize (H7 x1).
          rewrite H7.
          tauto.
        * intros.
          simpl.
          pose proof Int64.eq_spec i a.
          destruct (Int64.eq i a) eqn : I.
          ++  left.
              pose proof Int64.same_if_eq i a.
              apply H12 in I; clear H11.
              subst i.
              specialize (H4 a).
              unfold store in H.
              destruct H.
              subst a.
              destruct H4; try tauto.
              destruct H4.
              rewrite H in H10.
              discriminate.
          ++  specialize (H4 i).
              destruct H4.
              --  left.
                  specialize (H8 i).
                  pose proof not_eq_sym H11.
                  subst a.
                  apply H8 in H12.
                  rewrite <- H12.
                  tauto.
              --  right. 
                  specialize (H8 i).
                  pose proof not_eq_sym H11.
                  subst a.
                  apply H8 in H12.
                  rewrite <- H12.
                  tauto.
  }
  split; intros. {
    revert H3; unfold_RELS_tac; intros; tauto.
  }
  revert H3; unfold_RELS_tac; intros; tauto.
Qed.  

Definition exp64 (P: int64 -> assertion): assertion := fun s => exists n:int64, P n s.

Lemma hoare_exist_sound:
  forall (P : int64 -> assertion) (Q Q_brk Q_cnt: assertion) (c : com),
  (forall (a : int64), valid ({{P a}} c {{ Q, Q_brk, Q_cnt}} )) ->
  (valid ( {{ exp64 P }} c {{ Q, Q_brk, Q_cnt}}  )).
Proof.
  simpl.
  unfold exp64.
  intros.
  destruct H0 as [n ?].
  specialize (H n s1 H0).
  tauto.
Qed.

Lemma hoare_conseq_sound:
  forall (P P' Q Q_brk Q_cnt Q' Q'_brk Q'_cnt: assertion) (c: com),
    valid (BuildHoareTriple P' c Q' Q'_brk Q'_cnt) ->
    derives P P' ->
    derives Q' Q ->
    derives Q'_brk Q_brk ->
    derives Q'_cnt Q_cnt ->
    valid (BuildHoareTriple P c Q Q_brk Q_cnt).
Proof.
  simpl.
  unfold derives.
  intros.
  specialize (H0 _ H4).
  specialize (H _ H0).
  destruct H as [? [? [? ?]]].
  split. {
    tauto.
  }
  split. {
    intros.
    specialize (H5 _ H8).
    apply (H1 _ H5).
  }
  split. {
    intros.
    specialize (H6 _ H8).
    apply (H2 _ H6).
  }
  intros.
  specialize (H7 _ H8).
  apply (H3 _ H7).
Qed.

(** 下面定义可证：*)

Inductive provable: HoareTriple -> Prop :=
| hoare_skip:
    forall P: assertion,
      provable  {{ P }} skip {{ P , asrt_false, asrt_false }}
| hoare_break:
    forall P: assertion,
      provable {{ P }} CBreak {{ asrt_false, P, asrt_false }}
| hoare_continue:
    forall P: assertion,
      provable {{ P }} CContinue {{ asrt_false, asrt_false, P }}
| hoare_seq:
    forall (P Q R R_brk R_cnt: assertion) (c1 c2: com),
      provable (BuildHoareTriple P c1 Q R_brk R_cnt) ->
      provable (BuildHoareTriple Q c2 R R_brk R_cnt) ->
      provable (BuildHoareTriple P (CSeq c1 c2) R R_brk R_cnt)
| hoare_if:
    forall (P Q Q_brk Q_cnt: assertion) (e: expr) (c1 c2: com),
      provable (BuildHoareTriple (andp P (eb2assn e)) c1 Q Q_brk Q_cnt) ->
      provable (BuildHoareTriple (andp P (eb2assn_not e)) c2 Q Q_brk Q_cnt) ->
      (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
      provable (BuildHoareTriple P (CIf e c1 c2) Q Q_brk Q_cnt)
| hoare_while:
    forall (P P_brk: assertion) (e: expr) (c: com),
      provable (BuildHoareTriple (andp P (eb2assn e)) c P P_brk P) ->
      (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
      provable (BuildHoareTriple P (CWhile e c) (orp (andp P (eb2assn_not e)) P_brk) asrt_false asrt_false)
| hoare_do_while:
    forall (P R R_brk: assertion) (e: expr) (c: com),
      provable (BuildHoareTriple P c R R_brk R) ->
      provable (BuildHoareTriple (andp R (eb2assn e)) c R R_brk R) ->
      (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
      provable (BuildHoareTriple P (CDoWhile c e) (orp (andp R (eb2assn_not e)) R_brk) asrt_false asrt_false)
| hoare_for:
    forall (P Q R R_brk: assertion) (e: expr) (c1 c2 c3: com),
      provable (BuildHoareTriple P c1 R asrt_false asrt_false) ->
      (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
      provable (BuildHoareTriple (andp R (eb2assn e)) c3 Q R_brk Q) ->
      provable (BuildHoareTriple Q c2 R asrt_false asrt_false) ->
      ((eval_com) c1).(brk) = ∅ -> ((eval_com) c1).(cnt) = ∅ ->
      ((eval_com) c2).(brk) = ∅ -> ((eval_com) c2).(cnt) = ∅ ->    
      provable (BuildHoareTriple P (CFor c1 e c2 c3) (orp (andp R (eb2assn_not e)) R_brk) asrt_false asrt_false)    
| hoare_asgn_deref_fwd:
    forall (P Q : assertion) (e1 e2 : expr) (a b: int64),
    (forall (s:state), P s -> ((eval_r e1).(nrm) s a)) ->
    (forall (s:state), P s -> ((eval_r e2).(nrm) s b)) ->
      derives P (exp (fun u => (sepcon (store a u) Q) )) ->
      provable ( {{P}} ( * (e1) ::= e2 ) {{(store a (Vint b)) * Q, asrt_false, asrt_false}} )
| hoare_asgn_var_fwd:
    forall (P Q: assertion) (e: expr) (a b: int64) (x : var_name),
    (forall (s:state), P s -> ((eval_r e).(nrm) s b)) ->
    (forall (s:state), P s -> s.(env) x = a) ->
      derives P (exp (fun u => (sepcon (store a u) Q) )) ->
      provable ( {{P}} ( (x = e) ) {{(store a (Vint b)) * Q, asrt_false, asrt_false}})
| hoare_conseq:
    forall (P P' Q Q_brk Q_cnt Q' Q'_brk Q'_cnt: assertion) (c: com),
      provable (BuildHoareTriple P' c Q' Q'_brk Q'_cnt) ->
      derives P P' ->
      derives Q' Q ->
      derives Q'_brk Q_brk ->
      derives Q'_cnt Q_cnt ->
      provable (BuildHoareTriple P c Q Q_brk Q_cnt)
| hoare_exist:
    forall (P : int64 -> assertion) (Q Q_brk Q_cnt: assertion) (c : com),
      (forall (a : int64), provable ({{P a}} c {{ Q, Q_brk, Q_cnt}} )) ->
      (provable ( {{ exp64 P }} c {{ Q, Q_brk, Q_cnt}}  )).

(** 将前面证明的结论连接起来，即可证明霍尔逻辑的可靠性。*)

Theorem hoare_sound: forall ht,
  provable ht -> valid ht.
Proof.
  intros.
  induction H.
  + apply hoare_skip_sound.
  + apply hoare_break_sound.
  + apply hoare_continue_sound.
  + apply (hoare_seq_sound _ Q); tauto.
  + apply hoare_if_sound; tauto.
  + apply hoare_while_sound; tauto.
  + apply hoare_do_while_sound; tauto.
  + apply (hoare_for_sound _ Q _ _ _ _ _); tauto.
  + apply hoare_asgn_deref_fwd_sound; tauto.
  + apply hoare_asgn_var_fwd_sound; tauto.
  + apply (hoare_conseq_sound P P' Q Q_brk Q_cnt Q' Q'_brk Q'_cnt); tauto.
  + apply (hoare_exist_sound P Q Q_brk Q_cnt c); tauto.
Qed.

End HoareWhileDC.

Module HoareWhileDC_Admissible.

Import Lang_While.
Import Lang_WhileDC.
Import DntSem_WhileDC.
Import HoareWhileDC.


Lemma hoare_conseq_pre_sound:
  forall (P P' Q Q_brk Q_cnt: assertion) (c: com),
    valid {{ P' }} c {{ Q, Q_brk, Q_cnt}} ->
    P |-- P' ->
    valid {{ P }} c {{ Q, Q_brk, Q_cnt}}.
Proof.
  simpl.
  unfold derives.
  intros.
  apply H0 in H1.
  apply (H s1); tauto.
Qed.

Lemma hoare_conseq_post_sound:
  forall (P Q Q_brk Q_cnt Q' Q'_brk Q'_cnt: assertion) (c: com),
    valid {{ P }} c {{ Q', Q'_brk, Q'_cnt }} ->
    Q' |-- Q ->
    Q'_brk |-- Q_brk ->
    Q'_cnt |-- Q_cnt ->
    valid {{ P }} c {{ Q, Q_brk, Q_cnt }}.
Proof.
  simpl.
  unfold derives.
  intros.
  specialize (H _ H3).
  destruct H as [? [? [? ?]]].
  split. {
    tauto.
  }
  split. {
    intros.
    apply H0.
    apply (H4 _ H7).
  }
  split. {
    intros.
    apply H1.
    apply (H5 _ H7).
  }
  intros.
  apply H2.
  apply (H6 _ H7).
Qed.

Lemma hoare_conseq_pre:
  forall (P P' Q Q_brk Q_cnt: assertion) (c: com),
    provable {{ P' }} c {{ Q, Q_brk, Q_cnt}} ->
    P |-- P' ->
    provable {{ P }} c {{ Q, Q_brk, Q_cnt}}.
(** 下面的证明即是导出证明。*)
Proof.
  intros.
  apply (hoare_conseq P P' _ _ _ _ _ _ _ H H0).
  all: unfold derives.
  all: intros; tauto.
Qed.

Ltac assn_unfold :=
  unfold derives, andp.

Ltac assn_tauto_lift H :=
  match H with
  | ?H1 -> ?H2 =>
      let F := assn_tauto_lift H2 in
      constr:(fun X0 (X1: H1) => (F (fun s => (X0 s) (X1 s))): H2)
  | _ =>
      constr:(fun X: H => X)
  end.  

Tactic Notation "assn_tauto" constr_list(Hs) :=
  revert Hs;
  assn_unfold;
  match goal with
  | |- ?P => let F := assn_tauto_lift P in refine (F _); intro s; tauto
  end.

Lemma hoare_conseq_post:
  forall (P Q Q_brk Q_cnt Q' Q'_brk Q'_cnt: assertion) (c: com),
    provable {{ P }} c {{ Q', Q'_brk, Q'_cnt }} ->
    Q' |-- Q ->
    Q'_brk |-- Q_brk ->
    Q'_cnt |-- Q_cnt ->
    provable {{ P }} c {{ Q, Q_brk, Q_cnt }}.
Proof.
  intros.
  assert(P |-- P). {
    unfold derives.
    intros.
    tauto.
  }
  apply (hoare_conseq _ _ _ _ _ _ _ _ _ H H3 H0 H1 H2).
Qed.

End HoareWhileDC_Admissible.