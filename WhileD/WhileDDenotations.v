Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PV.Syntax.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module DntSem_WhileD.
Import Lang_While.
Import Lang_WhileD.

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

(** 由于表达式中存在取地址操作，我们无法继续沿用原先定义的表达式指称。*)

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

Definition arith_compute1_nrm
  (Zfun: Z -> Z -> Z)
  (i1 i2 i: int64): Prop :=
let res := Zfun (Int64.signed i1) (Int64.signed i2) in
i = Int64.repr res /\
Int64.min_signed <= res <= Int64.max_signed.

Definition arith_compute1_err
  (Zfun: Z -> Z -> Z)
  (i1 i2: int64): Prop :=
let res := Zfun (Int64.signed i1) (Int64.signed i2) in
res < Int64.min_signed \/ res > Int64.max_signed.

Definition arith_compute2_nrm
             (int64fun: int64 -> int64 -> int64)
             (i1 i2 i: int64): Prop :=
  i = int64fun i1 i2 /\
  Int64.signed i2 <> 0 /\
  (Int64.signed i1 <> Int64.min_signed \/
   Int64.signed i2 <> - 1).

Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
   Int64.signed i2 = - 1).

Definition cmp_compute_nrm
   (c: comparison)
   (i1 i2 i: int64): Prop :=
      i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.


Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_compute_nrm (i1 i: int64): Prop :=
   i = Int64.neg i1 /\
   Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
   Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
   Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
   i1 = Int64.repr 0 /\ i = Int64.repr 1.  

Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.


Definition SC_and_compute_nrm (i1 i: int64): Prop :=
   i1 = Int64.repr 0 /\ i = Int64.repr 0.
 
Definition SC_or_compute_nrm (i1 i: int64): Prop :=
   Int64.signed i1 <> 0 /\ i = Int64.repr 1.
 
Definition NonSC_and (i1: int64): Prop :=
   Int64.signed i1 <> 0.
 
Definition NonSC_or (i1: int64): Prop :=
   i1 = Int64.repr 0.
 
Definition NonSC_compute_nrm (i2 i: int64): Prop :=
   i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
   Int64.signed i2 <> 0 /\ i = Int64.repr 1.
 

Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

(** 『解引用』表达式既可以用作右值也可以用作左值。其作为右值是的语义就是原先我们
    定义的『解引用』语义。*)

Definition deref_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Some (Vint i).

Definition deref_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

(** 当程序表达式为单个变量时，它也可以同时用作左值或右值。下面先定义其作为左值时
    的存储地址。*)

Definition var_sem_l (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(env) X = i;
    err := ∅;
  |}.

(** 基于此，可以又定义它作为右值时的值。*)

Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).

(** 最后，我们可以用互递归函数（mutually recursive function）在Coq中定义表达式的
    语义。需注意，解引用表达式_[* e]_作为左值时的存储地址就是_[e]_作为右值时的
    值，而取地址表达式_[& e]_作为右值时的值就是_[e]_作为左值时的存储地址。这都不
    需要在额外定义。同时，常量、一元运算、二元运算、取地址表达式这些都不能用作左
    值表达式。*)

Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r e1) (eval_r e2)
  | EUnop op e1 =>
      unop_sem op (eval_r e1)
  | EDeref e1 =>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 =>
      eval_l e1
  end
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

Fixpoint rank (e:expr): nat :=
  match e with
  | EConst n =>
      O
  | EVar X =>
      O
  | EBinop op e1 e2 =>
      S(rank e1 + rank e2)
  | EUnop op e1 =>
      S(rank e1)
  | EDeref e1 =>
      S(rank e1)
  | EAddrOf e1 =>
      S(rank e1)
  end.

Lemma eval_r_sem_inj_pre:
  forall (n: nat)(a b: int64)(e: expr)(s: state),
  (eval_r e).(nrm) s a ->
  (eval_r e).(nrm) s b ->
  le (rank e) n ->
  a = b.
Proof.
  induction n; simpl; intros; pose proof H1 as HH; clear H1.
  + destruct e; simpl; intros.
    all: simpl in HH.
    all: try lia.
    - simpl in H, H0.
      destruct H, H0.
      subst a b.
      tauto.
    - simpl in H, H0.
      destruct H, H0.
      destruct H, H0.
      subst x0 x1.
      rewrite H2 in H1.
      injection H1.
      auto.
  + destruct e; simpl; intros; simpl in H, H0.
    - destruct H, H0.
      rewrite H, H0.
      tauto.
    - unfold deref_sem_nrm in H, H0.
      destruct H as [a0 [? ?]].
      destruct H0 as [b0 [? ?]].
      rewrite H0 in H.
      subst a0.
      rewrite H1 in H2.
      injection H2.
      tauto.
    - unfold binop_sem in H, H0.
      destruct op.
      * unfold or_sem in H, H0. 
        simpl in H, H0.
        unfold or_sem_nrm in H, H0. 
        destruct H as [i1 [? ?]].
        destruct H0 as [i2 [? ?]].
        specialize (IHn i1 i2).
        assert (i1 = i2) by auto.
        subst i2.
        unfold SC_or_compute_nrm in H1, H2.
        unfold NonSC_or in H1, H2.
        unfold NonSC_compute_nrm in H1, H2.
        destruct (Int64.signed i1) eqn : I1.
        * destruct H1; destruct H1; try contradiction.
          destruct H2; destruct H2; try contradiction.
          destruct H3 as [i2 [? ?]].
          destruct H4 as [i2' [? ?]].
          specialize (IHe2 i2 i2').
          assert (i2 = i2') by auto.
          subst i2'.
          destruct (Int64.signed i2) eqn : I2.
          ++  destruct H5; destruct H5; try contradiction.
              destruct H6; destruct H6; try contradiction.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
        * destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          subst a b; auto.
        * destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          subst a b; auto.
      - unfold and_sem in H, H0. 
        simpl in H, H0.
        unfold and_sem_nrm in H, H0. 
        destruct H as [i1 [? ?]].
        destruct H0 as [i2 [? ?]].
        specialize (IHe1 i1 i2).
        assert (i1 = i2) by auto.
        subst i2.
        unfold SC_and_compute_nrm in H1, H2.
        unfold NonSC_and in H1, H2.
        unfold NonSC_compute_nrm in H1, H2.
        destruct (Int64.signed i1) eqn : I1.
        * destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try contradiction.
          subst a b; auto.
        * destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          destruct H3 as [i2 [? ?]].
          destruct H4 as [i2' [? ?]].
          specialize (IHe2 i2 i2').
          assert (i2 = i2') by auto.
          subst i2'.
          destruct (Int64.signed i2) eqn : I2.
          ++  destruct H5; destruct H5; try contradiction.
              destruct H6; destruct H6; try contradiction.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
        * destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          destruct H3 as [i2 [? ?]].
          destruct H4 as [i2' [? ?]].
          specialize (IHe2 i2 i2').
          assert (i2 = i2') by auto.
          subst i2'.
          destruct (Int64.signed i2) eqn : I2.
          ++  destruct H5; destruct H5; try contradiction.
              destruct H6; destruct H6; try contradiction.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
          ++  destruct H5; destruct H5;
              destruct H6; destruct H6. 
              all: try rewrite H5 in I2.
              all: try rewrite H6 in I2.
              all: try discriminate.
              rewrite H7, H8.
              tauto.
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.      
      - unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.      
      - unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        destruct H2, H4.
        subst i1' i2' a b; auto.
      - unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        destruct H2, H4.
        subst i1' i2' a b; auto.
      - unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        destruct H2, H4.
        subst i1' i2' a b; auto.          
      - unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        destruct H2, H4.
        subst i1' i2' a b; auto.     
      - unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        specialize (IHe1 i1 i1').
        specialize (IHe2 i2 i2').
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        destruct H2, H4.
        subst i1' i2' a b; auto.
      
      



  + destruct H, H0.
    rewrite H, H0.
    tauto.
  + unfold deref_sem_nrm in H, H0.
    destruct H as [a0 [? ?]].
    destruct H0 as [b0 [? ?]].
    rewrite H0 in H.
    subst a0.
    rewrite H1 in H2.
    injection H2.
    tauto.
  + unfold binop_sem in H, H0.
    destruct op.
    - unfold or_sem in H, H0. 
      simpl in H, H0.
      unfold or_sem_nrm in H, H0. 
      destruct H as [i1 [? ?]].
      destruct H0 as [i2 [? ?]].
      specialize (IHe1 i1 i2).
      assert (i1 = i2) by auto.
      subst i2.
      unfold SC_or_compute_nrm in H1, H2.
      unfold NonSC_or in H1, H2.
      unfold NonSC_compute_nrm in H1, H2.
      destruct (Int64.signed i1) eqn : I1.
      * destruct H1; destruct H1; try contradiction.
        destruct H2; destruct H2; try contradiction.
        destruct H3 as [i2 [? ?]].
        destruct H4 as [i2' [? ?]].
        specialize (IHe2 i2 i2').
        assert (i2 = i2') by auto.
        subst i2'.
        destruct (Int64.signed i2) eqn : I2.
        ++  destruct H5; destruct H5; try contradiction.
            destruct H6; destruct H6; try contradiction.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
      * destruct H1; destruct H1;
        destruct H2; destruct H2.
        all: try rewrite H1 in I1.
        all: try rewrite H2 in I1.
        all: try discriminate.
        subst a b; auto.
      * destruct H1; destruct H1;
        destruct H2; destruct H2.
        all: try rewrite H1 in I1.
        all: try rewrite H2 in I1.
        all: try discriminate.
        subst a b; auto.
    - unfold and_sem in H, H0. 
      simpl in H, H0.
      unfold and_sem_nrm in H, H0. 
      destruct H as [i1 [? ?]].
      destruct H0 as [i2 [? ?]].
      specialize (IHe1 i1 i2).
      assert (i1 = i2) by auto.
      subst i2.
      unfold SC_and_compute_nrm in H1, H2.
      unfold NonSC_and in H1, H2.
      unfold NonSC_compute_nrm in H1, H2.
      destruct (Int64.signed i1) eqn : I1.
      * destruct H1; destruct H1;
        destruct H2; destruct H2.
        all: try contradiction.
        subst a b; auto.
      * destruct H1; destruct H1;
        destruct H2; destruct H2.
        all: try rewrite H1 in I1.
        all: try rewrite H2 in I1.
        all: try discriminate.
        destruct H3 as [i2 [? ?]].
        destruct H4 as [i2' [? ?]].
        specialize (IHe2 i2 i2').
        assert (i2 = i2') by auto.
        subst i2'.
        destruct (Int64.signed i2) eqn : I2.
        ++  destruct H5; destruct H5; try contradiction.
            destruct H6; destruct H6; try contradiction.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
      * destruct H1; destruct H1;
        destruct H2; destruct H2.
        all: try rewrite H1 in I1.
        all: try rewrite H2 in I1.
        all: try discriminate.
        destruct H3 as [i2 [? ?]].
        destruct H4 as [i2' [? ?]].
        specialize (IHe2 i2 i2').
        assert (i2 = i2') by auto.
        subst i2'.
        destruct (Int64.signed i2) eqn : I2.
        ++  destruct H5; destruct H5; try contradiction.
            destruct H6; destruct H6; try contradiction.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
        ++  destruct H5; destruct H5;
            destruct H6; destruct H6. 
            all: try rewrite H5 in I2.
            all: try rewrite H6 in I2.
            all: try discriminate.
            rewrite H7, H8.
            tauto.
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.      
    - unfold cmp_sem in H, H0.
      simpl in H, H0.
      unfold cmp_sem_nrm in H, H0.
      unfold cmp_compute_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      subst i1' i2' a b; auto.      
    - unfold arith_sem1 in H, H0.
      simpl in H, H0.
      unfold arith_sem1_nrm in H, H0.
      unfold arith_compute1_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      destruct H2, H4.
      subst i1' i2' a b; auto.
    - unfold arith_sem1 in H, H0.
      simpl in H, H0.
      unfold arith_sem1_nrm in H, H0.
      unfold arith_compute1_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      destruct H2, H4.
      subst i1' i2' a b; auto.
    - unfold arith_sem1 in H, H0.
      simpl in H, H0.
      unfold arith_sem1_nrm in H, H0.
      unfold arith_compute1_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      destruct H2, H4.
      subst i1' i2' a b; auto.          
    - unfold arith_sem1 in H, H0.
      simpl in H, H0.
      unfold arith_sem1_nrm in H, H0.
      unfold arith_compute1_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      destruct H2, H4.
      subst i1' i2' a b; auto.     
    - unfold arith_sem1 in H, H0.
      simpl in H, H0.
      unfold arith_sem1_nrm in H, H0.
      unfold arith_compute1_nrm in H, H0.
      destruct H as [i1 [i2 [? [? ?]]]].
      destruct H0 as [i1' [i2' [? [? ?]]]].
      specialize (IHe1 i1 i1').
      specialize (IHe2 i2 i2').
      assert (i1 = i1') by tauto.
      assert (i2 = i2') by tauto.
      destruct H2, H4.
      subst i1' i2' a b; auto.   
  + unfold unop_sem in H, H0.
    destruct op; simpl; intros.
    - unfold not_sem in H, H0.
      simpl in H, H0.
      unfold not_sem_nrm in H, H0.
      unfold not_compute_nrm in H, H0.
      destruct H as [i1 [? ?]].
      destruct H0 as [i1' [? ?]].
      specialize (IHe i1 i1').
      assert (i1 = i1') by tauto.
      subst i1'.
      destruct (Int64.signed i1) eqn : I.
      * destruct H1; destruct H1; destruct H2; destruct H2.
        all: try discriminate; try contradiction.
        subst a b; auto.
      * destruct H1; destruct H1; destruct H2; destruct H2.
        all: try rewrite H1 in I.
        all: try rewrite H2 in I.
        all: try discriminate; try contradiction.
        subst a b; auto.
      * destruct H1; destruct H1; destruct H2; destruct H2.
        all: try rewrite H1 in I.
        all: try rewrite H2 in I.
        all: try discriminate; try contradiction.
        subst a b; auto.
    - unfold neg_sem in H, H0.
      simpl in H, H0.
      unfold neg_sem_nrm in H, H0.
      unfold neg_compute_nrm in H, H0.
      destruct H as [i1 [? ?]].
      destruct H0 as [i1' [? ?]].
      specialize (IHe i1 i1').
      assert (i1 = i1') by tauto.
      subst i1'.
      destruct H1, H2.
      subst a b; auto.
  + unfold deref_sem_nrm in H, H0.
    destruct H as [i1 [? ?]].
    destruct H0 as [i1' [? ?]].
    specialize (IHe i1 i1').
    assert (i1 = i1') by tauto.
    subst i1'.
    rewrite H2 in H1.
    injection H1.
    auto.
  + unfold eval_l in H, H0.
    destruct e eqn : I. 
    - revert H H0.
      unfold_RELS_tac.
      simpl.
      intros.
      contradiction.
    - unfold var_sem_l in H, H0.
      simpl in H, H0.
      subst a b; auto.
    - simpl in H, H0.
      revert H H0.
      unfold_RELS_tac.
      simpl.
      intros.
      contradiction.
    - simpl in H, H0.
      revert H H0.
      unfold_RELS_tac.
      simpl.
      intros.
      contradiction.
    - fold eval_r in H, H0.
      simpl in IHe.
      unfold deref_sem_nrm in IHe.
      specialize (IHe (s.(mem) a) (s.(mem) b)).

(** 这里_[test_true]_与_[test_false]_的定义不变，不过之后只会将其作用在表达式的
    右值上。*)

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(** 程序语句的指称定义不变，依然包括三种情况：正常运行终止、运行出错以及运行不终
    止。空语句、顺序执行、条件分支语句与while循环语句的语义定义也不变。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (iter_nrm_lt_n D0 D1);
    err := ⋃ (iter_err_lt_n D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(** 向地址赋值的语义与原先定义基本相同，只是现在需要规定所有变量的地址不被改变，
    而非所有变量的值不被改变。*)

Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = None.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

(** 变量赋值的行为可以基于此定义。*)

Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

(** 在递归定义的程序语句语义中，只会直接使用表达式用作右值时的值。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r e1) (eval_r e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  end.

End DntSem_WhileD.
