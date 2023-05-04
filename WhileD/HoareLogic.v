Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.WhileDDenotations.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Module HoareWhileD.
Import  Lang_WhileD
        DntSem_WhileD.

Notation "x < y" := (ELt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom expr_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom expr_entry at level 10).
Notation "x = e" := (CAsgn x e)
  (in custom expr_entry at level 18, no associativity).
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

(** 首先定义断言。*)

Definition assertion: Type := state -> Prop.

Definition derives (P Q: assertion): Prop :=
  forall s, P s -> Q s.

Definition logical_equiv (P Q: assertion): Prop :=
  forall s, P s <-> Q s.

Definition andp (P Q: assertion): assertion := fun s => P s /\ Q s.

Definition exp (P: Z -> assertion): assertion := fun s => exists n, P n s.

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
| BuildHoareTriple: assertion -> com -> assertion -> HoareTriple.

Notation "{{ P }}  c  {{ Q }}" :=
  (BuildHoareTriple P c Q) (at level 1,
                            P custom assn_entry at level 99,
                            Q custom assn_entry at level 99,
                            c custom expr_entry at level 99).

(** 一个布尔表达式为真是一个断言：*)

Definition eb2assn (b: expr_bool): assertion := fun s => eval_expr_bool b s = true.

(** 断言中描述整数的逻辑表达式（区分于程序表达式）：*)

Definition exprZ: Type := state -> Z.

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
    u (state_subst s x (v s)).

(** 下面的Notation定义可以跳过*)

Notation "[[ e ]]" := (eb2assn e)
  (in custom assn_entry at level 0,
      e custom expr_entry at level 99,
      only printing).

Notation "[[ e ]]" := (ei2exprZ e)
  (in custom assn_entry at level 0,
      e custom expr_entry at level 99,
      only printing).

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
      v custom assn_entry at level 0).

(** 下面定义有效：*)

Definition valid: HoareTriple -> Prop :=
  fun ht =>
  match ht with
  | BuildHoareTriple P c Q =>
      forall s1 s2,
        P s1 ->
        eval_com c s1 s2 ->
        Q s2
  end.

Lemma hoare_skip_sound:
  forall P: assertion,
    valid {{ P }} skip {{ P }}.
Proof.
  simpl.
  unfold skip_sem.
  unfold_RELS_tac.
  intros.
  rewrite <- H0; tauto.
Qed.

Lemma hoare_seq_sound:
  forall (P Q R: assertion) (c1 c2: com),
    valid {{ P }} c1 {{ Q }} ->
    valid {{ Q }} c2 {{ R }} ->
    valid {{ P }} c1; c2 {{ R }}.
Proof.
  simpl.
  unfold seq_sem.
  unfold_RELS_tac.
  intros.
  destruct H2 as [s1' [? ?] ].
  specialize (H _ _ H1 H2).
  specialize (H0 _ _ H H3).
  apply H0.
Qed.

(** 习题：*)
Lemma hoare_if_sound:
  forall (P Q: assertion) (e: expr_bool) (c1 c2: com),
    valid {{ P && [[ e ]] }} c1 {{ Q }} ->
    valid {{ P && [[! e ]] }} c2 {{ Q }} ->
    valid {{ P }} if (e) then { c1 } else { c2 } {{ Q }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  simpl.
  unfold if_sem.
  unfold andp, eb2assn.
  unfold_RELS_tac.
  simpl.
  unfold not_sem.
  intros.
  destruct H2 as [H2 | H2];
    destruct H2 as [s1' [? ?] ].
  + unfold test_true in H2.
    revert H2; unfold_RELS_tac; intros.
    destruct H2 as [H2 ?]; subst s1'.
    apply (H s1 s2); tauto.
  + unfold test_false in H2.
    revert H2; unfold_RELS_tac; intros.
    destruct H2 as [H2 ?]; subst s1'.
    apply (H0 s1 s2).
    - rewrite H2; tauto.
    - tauto.
Qed.

(** 习题：*)
Lemma hoare_while_sound:
  forall (P: assertion) (e: expr_bool) (c: com),
    valid {{ P && [[ e ]] }} c {{ P }} ->
    valid {{ P }} while (e) do { c } {{ P && [[! e ]] }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  simpl.
  unfold while_sem.
  unfold andp, eb2assn.
  unfold_RELS_tac.
  simpl.
  unfold not_sem.
  intros.
  destruct H1 as [n ?].
  revert s1 s2 H0 H1; induction n; intros.
  + simpl in H1.
    unfold test_false in H1.
    revert H1; unfold_RELS_tac; intros.
    destruct H1 as [H1 ?]; subst s2.
    rewrite H1; tauto.
  + simpl in H1.
    unfold test_true in H1.
    revert H1; unfold_RELS_tac; intros.
    destruct H1 as [s1' [ [? ?] [s1'' [? ?] ] ] ].
    subst s1'.
    apply (IHn s1''); [| tauto].
    apply (H s1); tauto.
Qed.

Lemma state_subst_fact:
  forall (s1 s2: state) (x: var_name),
    (forall y, x <> y -> s2 y = s1 y) ->
      state_subst s2 x (s1 x) = s1.
Proof.
  intros. 
  apply functional_extensionality.
  intros y.
  unfold state_subst.
  destruct (String.eqb x y) eqn:EQ.
  + apply String.eqb_eq in EQ.
    rewrite EQ.
    reflexivity.
  + apply String.eqb_neq in EQ.
    apply H; tauto.
Qed.

(** 习题：*)
Lemma hoare_asgn_fwd_sound:
  forall P x e,
    valid {{ P }} x = e {{ exists x', exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] && assn_subst P x [[ x' ]] }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  simpl.
  unfold asgn_sem.
  unfold andp, exp, exprZ_eq, const_sem, var_sem, ei2exprZ.
  unfold_substs.
  intros.
  destruct H0.
  exists (s1 x).
  rewrite state_subst_fact by tauto.
  rewrite H0; tauto.
Qed.

(** 习题：*)
Lemma hoare_conseq_sound:
  forall (P P' Q Q': assertion) (c: com),
    valid {{ P' }} c {{ Q' }} ->
    derives P P' ->
    derives Q' Q ->
    valid {{ P }} c {{ Q }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  simpl.
  unfold derives.
  intros.
  apply H0 in H2.
  specialize (H _ _ H2 H3).
  apply H1; tauto.
Qed.

(** 下面定义可证：*)

Inductive provable: HoareTriple -> Prop :=
| hoare_skip:
    forall P: assertion,
      provable {{ P }} skip {{ P }}
| hoare_seq:
    forall (P Q R: assertion) (c1 c2: com),
      provable {{ P }} c1 {{ Q }} ->
      provable {{ Q }} c2 {{ R }} ->
      provable {{ P }} c1; c2 {{ R }}
| hoare_if:
    forall (P Q: assertion) (e: expr_bool) (c1 c2: com),
      provable {{ P && [[ e ]] }} c1 {{ Q }} ->
      provable {{ P && [[! e ]] }} c2 {{ Q }} ->
      provable {{ P }} if (e) then { c1 } else { c2 } {{ Q }}
| hoare_while:
    forall (P: assertion) (e: expr_bool) (c: com),
      provable {{ P && [[ e ]] }} c {{ P }} ->
      provable {{ P }} while (e) do { c } {{ P && [[! e ]] }}
| hoare_asgn_fwd:
    forall P x e,
      provable {{ P }} x = e {{ exists x', exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] && assn_subst P x [[ x' ]] }}
| hoare_conseq:
    forall (P P' Q Q': assertion) (c: com),
      provable {{ P' }} c {{ Q' }} ->
      P |-- P' ->
      Q' |-- Q ->
      provable {{ P }} c {{ Q }}.

(** 将前面证明的结论连接起来，即可证明霍尔逻辑的可靠性。*)

Theorem hoare_sound: forall ht,
  provable ht -> valid ht.
Proof.
  intros.
  induction H.
  + apply hoare_skip_sound.
  + apply (hoare_seq_sound _ Q); tauto.
  + apply hoare_if_sound; tauto.
  + apply hoare_while_sound; tauto.
  + apply hoare_asgn_fwd_sound; tauto.
  + apply (hoare_conseq_sound P P' Q Q'); tauto.
Qed.


End HoareSimpleWhile.

(** * Coq中归纳定义命题 *)

Module Permutation.
Import ListNotations.


(** 列表之间的置换关系在Coq中是一个归纳定义的命题。*)

Inductive Permutation {A: Type}: list A -> list A -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip: forall x (l l': list A), Permutation l l' ->
    Permutation (x :: l) (x :: l')
| perm_swap: forall x y (l: list A),
    Permutation (x :: y :: l) (y :: x :: l)
| perm_trans: forall l1 l2 l3: list A,
    Permutation l1 l2 ->
    Permutation l2 l3 ->
    Permutation l1 l3.

(** 在证明中，归纳定义命题的每个分支可以简单的用作引理或定义。下面这个例子演示了
    如何证明一个归纳定义的命题。*)

Example perm_fact1: Permutation [1 ; 3; 5] [3; 5; 1].
Proof.
  intros.
  apply (perm_trans _ [3; 1; 5]). 
  + apply perm_swap.
  + apply perm_skip.
    apply perm_swap.
Qed.


(** 利用类似的方法，可以证明上面定义的置换关系有自反性。*)

(** 习题：*)
Lemma perm_refl: forall {A: Type} (l: list A),
  Permutation l l.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  induction l.
  + apply perm_nil.
  + apply perm_skip; tauto.
Qed.

(** 当归纳定义的命题在前提中时，可以对其做证明树归纳。*)

Lemma perm_symm: forall {A: Type} (l1 l2: list A),
  Permutation l1 l2 ->
  Permutation l2 l1.
Proof.
  intros.
  induction H.
  + apply perm_nil.
  + apply perm_skip; tauto.
  + apply perm_swap.
  + apply (perm_trans _ l2); tauto.
Qed.





End Permutation.

(** * 导出规则 *)

Module HoareSimpleWhile_Derived.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       HoareSimpleWhile.


(** 除了上述霍尔逻辑规则之外，其实也可以在保持逻辑可靠性的基础上增加一些其他的规
    则。例如，我们可以增加单侧的Consequence规则。*)

Lemma hoare_conseq_pre_sound:
  forall (P P' Q: assertion) (c: com),
    valid {{ P' }} c {{ Q }} ->
    P |-- P' ->
    valid {{ P }} c {{ Q }}.
Proof.
  simpl.
  unfold derives.
  intros.
  apply H0 in H1.
  apply (H s1); tauto.
Qed.

Lemma hoare_conseq_post_sound:
  forall (P Q Q': assertion) (c: com),
    valid {{ P }} c {{ Q' }} ->
    Q' |-- Q ->
    valid {{ P }} c {{ Q }}.
Proof.
  simpl.
  unfold derives.
  intros.
  apply H0.
  apply (H s1); tauto.
Qed.

(** 然而，我们并不需要将其添加到霍尔逻辑的原始规则（primitive rules）集合中去。
    因为，这一规则可以由双侧的Consequence规则导出。*)

Lemma hoare_conseq_pre:
  forall (P P' Q: assertion) (c: com),
    provable {{ P' }} c {{ Q }} ->
    P |-- P' ->
    provable {{ P }} c {{ Q }}.
(** 下面的证明即是导出证明。*)
Proof.
  intros.
  apply (hoare_conseq P P' Q Q).
  + tauto.
  + tauto.
  + unfold derives.
    intros; tauto.
Qed.

(** 上面证明中用到了_[Q |-- Q]_这一性质。之后的证明中还会用到许多关于断言推导的
    命题逻辑性质。证明中可以使用_[assn_tauto]_指令用于证明。具体而言，
    _[assn_tauto H1 H2 ... Hn]_表示在将_[H1]_等前提考虑在内的情况下使用命题逻辑
    证明。*)

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
  forall (P Q Q': assertion) (c: com),
    provable {{ P }} c {{ Q' }} ->
    Q' |-- Q ->
    provable {{ P }} c {{ Q }}.
Proof.
  intros.
  apply (hoare_conseq P P Q Q').
  + tauto.
  + assn_tauto.
  + assn_tauto H0.
Qed.

(** 类似的，可以用变量赋值规则（正向）与顺序执行规则导出下面规则。在Coq证明中，
    _[eapply]_表示使用_[apply]_但是相关参数暂时空缺。*)

Lemma forward_symbolic_exe:
  forall P x e c Q,
    provable {{ exists x',
                  exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] &&
                  assn_subst P x [[ x' ]] }} c {{ Q }} ->
    provable {{ P }} x = e; c {{ Q }}.
Proof.
  intros.
  eapply hoare_seq.
  + apply hoare_asgn_fwd.
  + apply H.
Qed.


End HoareSimpleWhile_Derived.

(** * 证明树归纳 *)

Module HoareSimpleWhile_Admissible.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       HoareSimpleWhile
       HoareSimpleWhile_Derived.

Lemma hoare_seq_inv: forall P R c1 c2,
  provable {{ P }} c1 ; c2 {{ R }} ->
  exists Q: assertion,
    provable {{ P }} c1 {{ Q }} /\
    provable {{ Q }} c2 {{ R }}.
Proof.
  intros.
  remember ( {{P}} c1; c2 {{R}} ) as ht eqn:EQ.
  revert P R EQ; induction H; intros.
  + discriminate EQ.
  + clear IHprovable1 IHprovable2.
    injection EQ as ? ? ? ?.
    subst P0 c0 c3 R0.
    exists Q.
    tauto.
  + discriminate EQ.
  + discriminate EQ.
  + discriminate EQ.
  + injection EQ as ? ? ?.
    subst P0 c Q.
    rename Q' into R'.
    specialize (IHprovable _ _ eq_refl).
    destruct IHprovable as [Q [? ?] ].
    exists Q.
    split.
    - apply (hoare_conseq_pre _ P'); tauto.
    - apply (hoare_conseq_post _ _ R'); tauto.
Qed.

Lemma hoare_seq_assoc: forall P Q c1 c2 c3,
  provable {{ P }} c1 ; (c2; c3) {{ Q }} <->
  provable {{ P }} (c1 ; c2); c3 {{ Q }}.
Proof.
  intros.
  split; intros.
  + apply hoare_seq_inv in H.
    destruct H as [M1 [H1 H23] ].
    apply hoare_seq_inv in H23.
    destruct H23 as [M2 [H2 H3] ].
    apply (hoare_seq _ M2); [| tauto].
    apply (hoare_seq _ M1); tauto.
  + apply hoare_seq_inv in H.
    destruct H as [M2 [H12 H3] ].
    apply hoare_seq_inv in H12.
    destruct H12 as [M1 [H1 H2] ].
    apply (hoare_seq _ M1); [tauto |].
    apply (hoare_seq _ M2); tauto.
Qed.

Lemma hoare_asgn_fwd_inv: forall P Q x e,
  provable {{ P }} x = e {{ Q }} ->
  Assn (exists x',
           exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] &&
           assn_subst P x [[ x' ]]) |-- Q.
Proof.
  intros.
  remember ( {{ P }} x = e {{ Q }} ) as ht eqn:EQ.
  revert P Q EQ; induction H; intros.
  + discriminate EQ.
  + discriminate EQ.
  + discriminate EQ.
  + discriminate EQ.
  + injection EQ as ? ? ?.
    subst P0 Q e0 x0.
    unfold derives; intros; tauto.
  + injection EQ as ? ? ?.
    subst P0 c Q0.
    specialize (IHprovable _ _ eq_refl).
    revert IHprovable.
    unfold derives, exp, andp, ei2exprZ, exprZ_eq.
    unfold_substs.
    intros.
    apply H1.
    apply (IHprovable s); clear IHprovable.
    destruct H2 as [x' [? ?] ].
    exists x'.
    split; [| apply H0]; tauto.
Qed.

(** 习题：*)

Lemma hoare_if_inv: forall P Q e c1 c2,
  provable {{ P }} if (e) then { c1 } else { c2 } {{ Q }} ->
  provable {{ P && [[ e ]] }} c1 {{ Q }} /\
  provable {{ P && [[ ! e ]] }} c2 {{ Q }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  remember ( {{ P }} if (e) then { c1 } else { c2 } {{ Q }} ) as ht eqn:EQ.
  revert P Q EQ; induction H; intros.
  + discriminate EQ.
  + discriminate EQ.
  + clear IHprovable1 IHprovable2.
    injection EQ as ? ? ? ? ?.
    subst P0 e0 c0 c3 Q0.
    tauto.
  + discriminate EQ.
  + discriminate EQ.
  + injection EQ as ? ? ?.
    subst P0 c Q0.
    specialize (IHprovable _ _ eq_refl).
    destruct IHprovable.
    split.
    - eapply hoare_conseq; [eauto | | eauto].
      assn_tauto H0.
    - eapply hoare_conseq; [eauto | | eauto].
      assn_tauto H0.
Qed.

(** 习题：*)

Lemma hoare_if_seq1: forall P Q e c1 c2 c3,
  provable {{ P }} if (e) then { c1 } else { c2 }; c3 {{ Q }} ->
  provable {{ P }} if (e) then { c1; c3 } else { c2; c3 } {{ Q }}.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  apply hoare_seq_inv in H.
  destruct H as [M [? ?] ].
  apply hoare_if.
  + apply hoare_if_inv in H.
    destruct H.
    apply (hoare_seq _ M); tauto.
  + apply hoare_if_inv in H.
    destruct H.
    apply (hoare_seq _ M); tauto.
Qed.



End HoareSimpleWhile_Admissible.
