Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 简单表达式的指称语义 *)

Module DntSem_SimpleWhile1.
Import Lang_SimpleWhile.



(** 指称语义是一种定义程序行为的方式。在极简的SimpleWhile语言中，整数类型表达式
    中只有整数常量、变量、加法、减法与乘法运算。*)

(** 我们约定其中整数变量的值、整数运算的结果都是没有范围限制的。基于这一约定，我
    们可以如下定义表达式_[e]_在程序状态_[st]_上的值。

    首先定义程序状态集合：*)

Definition state: Type := var_name -> Z.

(** 下面使用Coq递归函数定义整数类型表达式的行为。*)

Fixpoint eval_expr_int (e: expr_int) (s: state) : Z :=
  match e with
  | EConst n => n
  | EVar X => s X
  | EAdd e1 e2 => eval_expr_int e1 s + eval_expr_int e2 s
  | ESub e1 e2 => eval_expr_int e1 s - eval_expr_int e2 s
  | EMul e1 e2 => eval_expr_int e1 s * eval_expr_int e2 s
  end.

(** 下面是两个具体的例子。*)

Example eval_example1: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  eval_expr_int [["x" + "y"]] s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Example eval_example2: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  eval_expr_int [["x" * "y" + 1]] s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

(** * 行为等价 *)

(** 基于整数类型表达式的语义定义_[eval_expr_int]_，我们可以定义整数类型表达式之
    间的行为等价（亦称语义等价）：两个表达式_[e1]_与_[e2]_是等价的当且仅当它们在
    任何程序状态上的求值结果都相同。*)

Definition expr_int_equiv (e1 e2: expr_int): Prop :=
  forall st, eval_expr_int e1 st = eval_expr_int e2 st.

Notation "e1 '~=~' e2" := (expr_int_equiv e1 e2)
  (at level 69, no associativity).

(** 下面是一些表达式语义等价的例子。 *)

Example expr_int_equiv_sample:
  [["x" + "x"]] ~=~ [["x" * 2]].
Proof.
  intros.
  unfold expr_int_equiv.
  (** 上面的_[unfold]_指令表示展开一项定义，一般用于非递归的定义。*)
  intros.
  simpl.
  lia.
Qed.

Lemma zero_plus_equiv: forall (a: expr_int),
  [[0 + a]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: expr_int),
  [[a + 0]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: expr_int),
  [[a - 0]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: expr_int),
  [[0 * a]] ~=~ 0.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: expr_int),
  [[a * 0]] ~=~ 0.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  [[EConst n + EConst m]] ~=~ EConst (n + m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_minus_const: forall n m: Z,
  [[EConst n - EConst m]] ~=~ EConst (n - m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_mult_const: forall n m: Z,
  [[EConst n * EConst m]] ~=~ EConst (n * m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

(** 下面定义一种简单的语法变换---常量折叠---并证明其保持语义等价性。所谓常量折叠
    指的是将只包含常量而不包含变量的表达式替换成为这个表达式的值。*)

Fixpoint fold_constants (e : expr_int) : expr_int :=
  match e with
  | EConst n    => EConst n
  | EVar x      => EVar x
  | EAdd e1 e2  =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 + n2)
      | _, _ => EAdd (fold_constants e1) (fold_constants e2)
      end
  | ESub e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 - n2)
      | _, _ => ESub (fold_constants e1) (fold_constants e2)
    end
  | EMul e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 * n2)
      | _, _ => EMul (fold_constants e1) (fold_constants e2)
    end
  end.

(** 这里我们可以看到，Coq中_[match]_的使用是非常灵活的。(1) 我们不仅可以对一个变
    量的值做分类讨论，还可以对一个复杂的Coq式子的取值做分类讨论；(2) 我们可以对
    多个值同时做分类讨论；(3) 我们可以用下划线表示_[match]_的缺省情况。下面是两
    个例子：*)

Example fold_constants_ex1:
    fold_constants [[(1 + 2) * "k"]] = [[3 * "k"]].
Proof. intros. reflexivity. Qed.

(** 注意，根据我们的定义，_[fold_constants]_并不会将_[0 + "y"]_中的_[0]_消去。*)

Example fold_expr_int_ex2 :
  fold_constants [["x" - ((0 * 6) + "y")]] = [["x" - (0 + "y")]].
Proof. intros. reflexivity. Qed.

(** 下面我们在Coq中证明，_[fold_constants]_保持表达式行为不变。 *)

Theorem fold_constants_sound : forall a,
  fold_constants a ~=~ a.
Proof.
  unfold expr_int_equiv. intros.
  induction a.
  (** 常量的情况 *)
  + simpl.
    reflexivity.
  (** 变量的情况 *)
  + simpl.
    reflexivity.
  (** 加号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  (** 减号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  (** 乘号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
Qed.

End DntSem_SimpleWhile1.

(** * 利用高阶函数定义指称语义 *)

Module DntSem_SimpleWhile2.
Import Lang_SimpleWhile.

Definition state: Type := var_name -> Z.

Definition add_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s + D2 s.

Definition sub_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s - D2 s.

Definition mul_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s * D2 s.

(** 下面是用于类型查询的_[Check]_指令。*)

Check add_sem.

(** 可以看到_[add_sem]_的类型是_[(state -> Z) -> (state -> Z) -> state -> Z]_，
    这既可以被看做一个三元函数，也可以被看做一个二元函数，即函数之间的二元函数。*)

(** 基于上面高阶函数，可以重新定义表达式的指称语义。*)

Definition const_sem (n: Z) (s: state): Z := n.
Definition var_sem (X: var_name) (s: state): Z := s X.

Fixpoint eval_expr_int (e: expr_int) : state -> Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

End DntSem_SimpleWhile2.

(** * 更多高阶函数的例子 *)

(** 在Coq中，一个函数可以以函数作为参数，也可以以以函数作为返回值，这样的函数称
    为高阶函数。下面是一个典型的例子。*)

Definition doit3times {X: Type} (f: X -> X) (n: X): X :=
  f (f (f n)).

(** 这里，_[f]_这个参数本身也是一个函数（从_[X]_到_[X]_的函数）而_[doit3times]_
    则把_[f]_在_[n]_上作用了3次。*)

Definition minustwo (x: Z): Z := x - 2.

(** 还可以在Coq中检验下面这些结果。 *)
Example fact_doit3times_1:
  doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example fact_doit3times_2:
  doit3times minustwo (doit3times minustwo 9) = -3.
Proof. reflexivity. Qed.

Example fact_doit3times_3:
  doit3times (doit3times minustwo) 9 = -9.
Proof. reflexivity. Qed.

Example fact_doit3times_4:
  doit3times doit3times minustwo 9 = -45.
Proof. reflexivity. Qed.

(** Coq中允许用户使用_[fun]_关键字表示匿名函数，例如：*)

Example fact_doit3times_anon1:
  doit3times (fun x => x - 2) 9 = 3.
Proof. reflexivity. Qed.

Example fact_doit3times_anon2:
  doit3times (fun x => x * x) 2 = 256.
Proof. reflexivity. Qed.

(** 这里_[fun x => x - 2]_与之前定义的_[minustwo]_是相同的，而_[fun x => x * x]_
    则表示了平方这样一个函数。*)

(** 还可以在Coq中检验下面这些结果。 *)

Example fact_doit3times_anon3:
  doit3times (fun x => - x) 5 = -5.
Proof. reflexivity. Qed.

Example fact_doit3times_anon4:
  doit3times (fun f x y => f y x) (fun x y => x - y) 1 2 = 1.
Proof. reflexivity. Qed.

Definition Func_add {A: Type}: (A -> Z) -> (A -> Z) -> (A -> Z) :=
  fun f g x => f x + g x.

Example fact_doit3times_anon5: forall x,
  doit3times (Func_add minustwo) (fun x => x * x) x = x * x + x * 3 - 6.
Proof. intros. unfold doit3times, Func_add, minustwo. lia. Qed.

Example fact_doit3times_anon6:
  doit3times ((fun x y => y * y - x * y + x * x) 1) 1 = 1.
Proof. reflexivity. Qed.





(** * 布尔表达式语义 *)

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile DntSem_SimpleWhile2.

(** 在Coq中可以如下定义：*)

Definition true_sem (s: state): bool := true.

Definition false_sem (s: state): bool := false.

Definition lt_sem (D1 D2: state -> Z) s: bool :=
  Z.ltb (D1 s) (D2 s).

Definition and_sem (D1 D2: state -> bool) s: bool :=
  andb (D1 s) (D2 s).

Definition not_sem (D: state -> bool) s: bool :=
  negb (D s).

Fixpoint eval_expr_bool (e: expr_bool): state -> bool :=
  match e with
  | ETrue =>
      true_sem
  | EFalse =>
      false_sem
  | ELt e1 e2 =>
      lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 =>
      and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 =>
      not_sem (eval_expr_bool e1)
  end.

End DntSem_SimpleWhile3.

(** * Coq中的集合与关系 *)


(** 本课程提供的SetsClass库中提供了有关集合的一系列定义。例如：

    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 一列集合的并：用_[⋃]_表示，定义为_[Sets.omega_union]_；

    - 一列集合的交：用_[⋂]_表示，定义为_[Sets.omega_intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_；

    - 二元关系的连接：用_[∘]_表示，定义为_[Rels.concat]_；

    - 等同关系：定义为_[Rels.id]_；

    - 测试关系：定义为_[Rels.test]_。

    在CoqIDE中，你可以利用CoqIDE对于unicode的支持打出特殊字符：

    - 首先，在打出特殊字符的latex表示法；

    - 再按shift+空格键；

    - latex表示法就自动转化为了相应的特殊字符。

    例如，如果你需要打出符号_[∈]_，请先在输入框中输入_[\in]_，当光标紧跟在_[n]_
    这个字符之后的时候，按shift+空格键即可。例如，下面是两个关于集合的命题：*)

Check forall A (X: A -> Prop), X ∪ ∅ == X.

Check forall A B (X Y: A -> B -> Prop), X ∪ Y ⊆ X.

(** 由于集合以及集合间的运算是基于Coq中的命题进行定义的，集合相关性质的证明也可
    以规约为与命题有关的逻辑证明。例如，我们想要证明，交集运算具有交换律：*)

Lemma Sets_intersect_comm: forall A (X Y: A -> Prop),
  X ∩ Y == Y ∩ X.
Proof.
  intros.
  (** 下面一条命令_[sets_unfold]_是SetsClass库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : A, X a /\ Y a <-> Y a /\ X a]_
      其中_[forall]_就是逻辑中『任意』的意思；_[/\]_之前我们已经了解，它表示『并
      且』的意思；_[<->]_表示『当且仅当』的意思；_[X a]_可以念做性质_[X]_对于
      _[a]_成立，也可以理解为_[a]_是集合_[X]_的元素。

      我们稍后再来完成相关性质的证明。在Coq中，要放弃当前的证明，可以用下面的
      _[Abort]_指令。*)
Abort.

(** 下面是一条关于并集运算的性质。*)

Lemma Sets_included_union1: forall A (X Y: A -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : A, X a -> X a \/ Y a]_。这里，
      _[\/]_表示『或者』；_[->]_表示推出，也可以念做『如果...那么...』。*)
Abort.

(** 下面是一条关于二元运算的性质。*)

Lemma Rels_concat_assoc: forall A (X Y Z: A -> A -> Prop),
  (X ∘ Y) ∘ Z == X ∘ (Y ∘ Z).
Proof.
  intros.
  unfold_RELS_tac.
  (** 关于二元关系的性质，要使用_[unfold_RELS_tac]_展开成为基于逻辑的定义。*)
Abort.

(** SetsClass库中提供了一系列有关集合运算的性质的证明。未来大家在证明中既可以使
    用_[sets_unfold]_与_[unfold_RELS_tac]_将关于集合运算的命题转化为关于逻辑的命
    题，也可以直接使用下面这些性质完成证明。*)

(**
  Sets_equiv_Sets_included:
    forall x y, x == y <-> x ⊆ y /\ y ⊆ x;
  Sets_empty_included:
    forall x, ∅ ⊆ x;
  Sets_included_full:
    forall x, x ⊆ Sets.full;
  Sets_intersect_included1:
    forall x y, x ∩ y ⊆ x;
  Sets_intersect_included2:
    forall x y, x ∩ y ⊆ y;
  Sets_included_intersect:
    forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z;
  Sets_included_union1:
    forall x y, x ⊆ x ∪ y;
  Sets_included_union2:
    forall x y, y ⊆ x ∪ y;
  Sets_union_included_strong2:
    forall x y z u,
       x ∩ u ⊆ z -> y ∩ u ⊆ z -> (x ∪ y) ∩ u ⊆ z;
*)
(**
  Sets_included_omega_union:
    forall xs n, xs n ⊆ ⋃ xs;
  Sets_omega_union_included:
    forall xs y, (forall n, xs n ⊆ y) -> ⋃ xs ⊆ y;
  Sets_omega_intersect_included:
    forall xs n, ⋂ xs ⊆ xs n;
  Sets_included_omega_intersect:
    forall xs y, (forall n : nat, y ⊆ xs n) -> y ⊆ ⋂ xs;
*)
(**
  Rels_concat_union_distr_r:
    forall x1 x2 y,
      (x1 ∪ x2) ∘ y == (x1 ∘ y) ∪ (x2 ∘ y);
  Rels_concat_union_distr_l:
    forall x y1 y2,
      x ∘ (y1 ∪ y2) == (x ∘ y1) ∪ (x ∘ y2);
  Rels_concat_mono:
    forall x1 x2,
      x1 ⊆ x2 ->
      forall y1 y2,
        y1 ⊆ y2 ->
        x1 ∘ y1 ⊆ x2 ∘ y2;
  Rels_concat_assoc:
    forall x y z,
      (x ∘ y) ∘ z == x ∘ (y ∘ z);
*)


(** * Coq中关于逻辑的证明 *)

(** 在Coq中可以用与、或、非、如果-那么、存在以及任意来描述复杂的命题，并且证明相
    关性质。*)

(** ** 逻辑命题『真』的证明 *)

(** 我们不需要任何前提就可以推出_[True]_。在Coq标准库中，_[I]_是_[True]_的一个证
    明，我们可以用_[exact I]_来证明_[True]_。*)

Example proving_True_1: 1 < 2 -> True.
Proof.
  intros.
  exact I.
Qed.

Example proving_True_2: 1 > 2 -> True.
Proof.
  intros.
  exact I.
Qed.

(** ** 关于『并且』的证明 *)

(** 要证明『某命题并且某命题』成立，可以在Coq中使用_[split]_证明指令进行证明。该
    指令会将当前的证明目标拆成两个子目标。*)

Lemma True2: True /\ True.
Proof.
  split.
  + exact I.
  + exact I.
Qed.

(** 下面证明一个关于_[/\]_的一般性结论：*)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  (** 下面的_[apply]_指令表示在证明中使用一条前提，或者使用一条已经经过证明的定
      理或引理。*)
  + apply HA.
  + apply HB.
Qed.

(** 习题：*)
Example and_exercise :
  forall n m : Z, n + 2*m = 10 -> 2*n + m = 5 -> n = 0 /\ True.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  split.
  + lia.
  + exact I.
Qed.

(** 如果当前一条前提假设具有『某命题并且某命题』的形式，我们可以在Coq中使用
    _[destruct]_指令将其拆分成为两个前提。 *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  destruct H as [HP HQ].
  apply HP.
Qed.

(** _[destruct]_指令也可以不指名拆分后的前提的名字，Coq会自动命名。*)

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

(** 当前提与结论中，都有_[/\]_的时候，我们就既需要使用_[split]_指令，又需要使用
    _[destruct]_指令。*)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(** 习题：*)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
  + split.
    - apply H.
    - apply H0.
  + apply H1.
Qed.

(** ** 关于『或』的证明 *)

(** 『或』是另一个重要的逻辑连接词。如果『或』出现在前提中，我们可以用Coq中的
    _[destruct]_指令进行分类讨论。*)

Lemma or_example :
  forall n m : Z, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros.
  destruct H as [H | H].
  + rewrite H.
    lia.
  + rewrite H.
    lia.
Qed.

(** 在上面的例子中，我们对于形如_[A \/ B]_的前提进行分类讨论。要证明_[A \/ B]_能
    推出原结论，就需要证明_[A]_与_[B]_中的任意一个都可以推出原结论。下面是一个一
    般性的结论. *)

Lemma or_example2 :
  forall P Q R: Prop, (P -> R) -> (Q -> R) -> (P \/ Q -> R).
Proof.
  intros.
  destruct H1 as [HP | HQ].
  + apply H.
    (** 注意，_[apply]_指令不一定要前提与结论完全吻合才能使用。此处，只要_[H]_中
        推导的结果与待证明的结论一致，就可以使用_[apply H]_。*)
    apply HP.
  + apply H0 in HQ.
    (** _[apply]_指令还可以在前提中做推导，不过这时需要使用_[apply ... in]_这一
        语法。*)
    apply HQ.
Qed.

(** 相反的，如果要证明一条形如_[A \/ B]_的结论整理，我们就只需要证明_[A]_与_[B]_
    两者之一成立就可以了。在Coq中的指令是：_[left]_与_[right]_。例如，下面是选择
    左侧命题的例子。*)

Lemma or_introl : forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  left.
  apply H.
Qed.

(** 下面是选择右侧命题的例子。*)

Lemma or_intror : forall A B : Prop, B -> A \/ B.
Proof.
  intros.
  right.
  apply H.
Qed.

(** 下面性质请各位自行证明。*)

(** 习题：*)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  destruct H as [HP | HQ].
  + right.
    apply HP.
  + left.
    apply HQ.
Qed.

(** ** 关于『如果...那么...』的证明 *)

(** 事实上，在之前的例子中，我们已经多次证明有关_[->]_的结论了。下面我们在看几个
    例子，并额外介绍几条Coq证明指令。

    下面的证明中，_[pose proof]_表示推导出一个新的结论，并将其用作之后证明中的前
    提。*)

Theorem modus_ponens: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  (** 将_[H0: P -> Q]_作用在_[H: P]_上，我们就可以得出一个新结论：_[Q]_。*)
  pose proof H0 H.
  apply H1.
Qed.

(** 下面我们换一种方法证明。_[revert]_证明指令可以看做_[intros]_的反操作。 *)

Theorem modus_ponens_alter1: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  (** 下面_[revert]_指令将前提中的_[P]_又放回了『结论中的前提』中去。*)
  revert H.
  apply H0.
Qed.

(** 下面我们再换一种方式证明，_[specialize]_指令与_[apply ... in]_指令的效果稍有
    不同。*)

Theorem modus_ponens_alter2: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  specialize (H0 H).
  apply H0.
Qed.

(** 另外，我们可以直接使用_[exact]_指令，这个指令的效果像是_[pose proof]_或者
    _[specialize]_与_[apply]_的组合。*)

Theorem modus_ponens_alter3: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  exact (H0 H).
Qed.

(** ** 关于『否定』与『假』的证明 *)

(** 在Coq中[~]表示否定，_[False]_表示假。如果前提为假，那么，矛盾推出一切。在Coq
    中，这可以用_[contradiction]_指令或_[destruct]_指令完成证明。*)

Theorem ex_falso_quodlibet : forall (P: Prop),
  False -> P.
Proof.
  intros.
  contradiction.
Qed.

Theorem ex_falso_quodlibet_alter : forall (P: Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

(** _[contradiction]_也可以用于_[P]_与_[~ P]_同时出现在前提中的情况： *)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros.
  destruct H.
  contradiction.
Qed.

(** 除了_[P]_与_[~ P]_不能同时为真之外，他们也不能同时为假，或者说，他们中至少有
    一个要为真。这是Coq标准库中的_[classic]_。 *)

Check classic.

(** 它说的是：_[forall P : Prop, P \/ ~ P]_。下面我们利用它做一些证明。 *)

Theorem double_neg_elim : forall P : Prop,
  ~ ~ P -> P.
Proof.
  intros.
  pose proof classic P.
  destruct H0.
  + apply H0.
  + contradiction.
Qed.

(** 习题：*)
Theorem not_False :
  ~ False.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  pose proof classic False.
  destruct H.
  + contradiction.
  + apply H.
Qed.

(** 习题：*)
Theorem double_neg_intro : forall P : Prop,
  P -> ~ ~ P.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  pose proof classic (~ P).
  destruct H0.
  + contradiction.
  + apply H0.
Qed.

(** ** 关于『当且仅当』的证明 *)

(** 在Coq中，_[<->]_符号对应的定义是_[iff]_，其将_[P <-> Q]_定义为
          _[(P -> Q) /\ (Q -> P)]_
    因此，要证明关于『当且仅当』的性质，首先可以使用其定义进行证明。*)

Theorem iff_refl: forall P: Prop, P <-> P.
Proof.
  intros.
  unfold iff.
  split.
  + intros.
    apply H.
  + intros.
    apply H.
Qed.

Theorem iff_imply: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros P Q H.
  unfold iff in H.
  destruct H.
  exact H.
Qed.

(** 当某前提假设具有形式_[P <-> Q]_，那我们也可以使用_[apply]_指令进行证明。*)

Theorem iff_imply_alter: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros.
  apply H.
  apply H0.
Qed.

(** 另外，_[rewrite]_指令也可以使用形如_[P <-> Q]_的等价性前提。*)

Theorem iff_imply_alter2: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros.
  rewrite <- H.
  apply H0.
Qed.

(** ** 关于『存在』的证明 *)

(** 当待证明结论形为：存在一个_[x]_使得...，那么可以用_[exists]_指明究竟哪个
    _[x]_使得该性质成立。*)

Lemma four_is_even : exists n, 4 = n + n.
Proof.
  exists 2.
  lia.
Qed.

Lemma six_is_not_prime: exists n, 2 <= n < 6 /\ exists q, n * q = 6.
Proof.
  exists 2.
  split.
  + lia.
  + exists 3.
    lia.
Qed.

(** 当某前提形为：存在一个_[x]_使得...，那么可以使用Coq中的_[destruct]_指令进行
    证明。这一证明指令相当于数学证明中的：任意给定一个这样的_[x]_。 *)

Theorem exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros.
  destruct H as [m H].
  exists (2 + m).
  lia.
Qed.

(** 习题：*)
Theorem dist_exists_and : forall (X: Type) (P Q: X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  destruct H as [x [HP HQ]].
  split.
  + exists x.
    apply HP.
  + exists x.
    apply HQ.
Qed.

(** 习题：*)
Theorem exists_exists : forall (X Y: Type) (P: X -> Y -> Prop),
  (exists x y, P x y) <-> (exists y x, P x y).
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  split; intros.
  + destruct H as [x [y ?]].
    exists y, x.
    exact H.
  + destruct H as [y [x ?]].
    exists x, y.
    exact H.
Qed.

(** ** 关于『任意』的证明 *)

(** 关于『任意』的证明与关于『如果...那么...』的证明是类似的，我们可以灵活使用
    _[pose proof]_, _[specialize]_, _[apply]_, _[revert]_等指令进行证明。下面是
    一个简单的例子。*)

Theorem forall_forall : forall (X Y: Type) (P: X -> Y -> Prop),
  (forall x y, P x y) -> (forall y x, P x y).
Proof.
  intros X Y P H.
  intros y x.
  specialize (H x y).
  apply H.
Qed.

(** ** 关于命题逻辑的自动证明 *)

(** 除了上述证明指令之外，Coq还提供了_[tauto]_这一自动证明指令。如果当且结论可以
    完全通过命题逻辑完成证明，那么_[tauto]_就可以自动构造这样的证明。例如：*)

Lemma or_reduce: forall (P Q R: Prop),
  (P /\ R) \/ (Q /\ ~ R) -> P \/ Q.
Proof.
  intros.
  tauto.
Qed.

(** 这里，所谓完全通过命题逻辑完成证明，指的是通过对于『并且』、『或』、『非』、
    『如果...那么...』、『当且仅当』、『真』与『假』的推理完成证明（注：除此之
    外，_[tauto]_也会将形如_[a = a]_的命题看做_[True]_）。下面例子所描述的命题很
    符合直觉，但是它就不能仅仅使用命题逻辑完成推理，因为他的推理过程中用到了
    _[forall]_的性质。*)

Lemma forall_and: forall (A: Type) (P Q: A -> Prop),
  (forall a: A, P a /\ Q a) <-> (forall a: A, P a) /\ (forall a: A, Q a).
Proof.
  intros.
  (** 注意，此处不能使用_[tauto]_直接完成证明。*)
  split.
  + intros.
    split.
    - intros a.
      specialize (H a).
      (** 此时可以用_[tauto]_完成剩余证明了，另外两个分支也是类似。*)
      tauto.
    - intros a.
      specialize (H a).
      tauto.
  + intros.
    destruct H.
    specialize (H a).
    specialize (H0 a).
    tauto.
Qed.

(** * 在Coq中定义程序语句的语义 *)

Module DntSem_SimpleWhile4.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3.

(** 下面在Coq中写出程序语句的指称语义。*)

Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition asgn_sem
             (X: var_name)
             (D: state -> Z)
             (st1 st2: state): Prop :=
  st2 X = D st1 /\
  forall Y, X <> Y -> st2 Y = st1 Y.

Definition seq_sem
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun st => D st = true).

Definition test_false
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun st => D st = false).

Definition if_sem
             (D0: state -> bool)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint iter_n
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | S n0 => test_true D0 ∘ D1 ∘ iter_n D0 D1 n0
  end.

Module WhileSem1.

Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iter_n D0 D1).

End WhileSem1.

Fixpoint iter_lt_n
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ iter_lt_n D0 D1 n0) ∪
      (test_false D0)
  end.

Module WhileSem2.

Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iter_lt_n D0 D1).

End WhileSem2.

(** 我们选择第一种定义。*)

Export WhileSem1.

(** 下面是程序语句指称语义的递归定义。*)

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  end.





End DntSem_SimpleWhile4.
