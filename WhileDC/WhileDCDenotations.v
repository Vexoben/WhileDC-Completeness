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


(** * WhileDC语言的语义 *)

Module DntSem_WhileDC.
Import Lang_While.
Import Lang_WhileDC.

(** 程序状态与表达式语义的定义不变。*)

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

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

(** 下面定义的比较运算关系利用了CompCert库定义的_[comparison]_类型和_[Int64.cmp]_
函数。*)

Definition cmp_compute_nrm
  (c: comparison)
  (i1 i2 i: int64): Prop :=
i = if Int64.cmp c i1 i2
then Int64.repr 1
else Int64.repr 0.

(** 一元运算的行为比较容易定义：*)

Definition neg_compute_nrm (i1 i: int64): Prop :=
i = Int64.neg i1 /\
Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
i1 = Int64.repr 0 /\ i = Int64.repr 1.

(** 最后，二元布尔运算的行为需要考虑短路求值的情况。下面定义中的缩写_[SC]_表示
short circuit。*)

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

Definition var_sem_l (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(env) X = i;
    err := ∅;
  |}.

Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).

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

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(** 由于在程序语句中加入了控制流，程序语句的指称定义需要做相应改变。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  brk: state -> state -> Prop;
  cnt: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(brk)'" := (CDenote.brk x)
  (at level 1).

Notation "x '.(cnt)'" := (CDenote.cnt x)
  (at level 1).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

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


(** 空语句的语义 *)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    brk := ∅;
    cnt := ∅;
    err := ∅;
    inf := ∅;
  |}.

(** Break语句的语义 *)

Definition brk_sem: CDenote :=
  {|
    nrm := ∅;
    brk := Rels.id;
    cnt := ∅;
    err := ∅;
    inf := ∅;
  |}.

(** Continue语句的语义 *)

Definition cnt_sem: CDenote :=
  {|
    nrm := ∅;
    brk := ∅;
    cnt := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

(** 顺序执行语句的语义 *)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    brk := D1.(brk) ∪ (D1.(nrm) ∘ D2.(brk));
    cnt := D1.(cnt) ∪ (D1.(nrm) ∘ D2.(cnt));
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

(** If语句的语义 *)

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    brk := (test_true D0 ∘ D1.(brk)) ∪
           (test_false D0 ∘ D2.(brk));
    cnt := (test_true D0 ∘ D1.(cnt)) ∪
           (test_false D0 ∘ D2.(cnt));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

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
    brk := ∅;
    cnt := ∅;
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D1.(nrm);
    inf := ∅;
  |}.

Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

Module WhileSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          (D1.(cnt) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          D1.(brk))) ∪
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
         (D1.(cnt) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D1.(nrm) ∘ X) ∪
         (D1.(cnt) ∘ X) ∪
         D1.(inf)).

End WhileSem.

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (WhileSem.iter_nrm_lt_n D0 D1);
    brk := ∅;
    cnt := ∅;
    err := ⋃ (WhileSem.iter_err_lt_n D0 D1);
    inf := Sets.general_union (WhileSem.is_inf D0 D1);
  |}.

Definition do_while_sem
             (D0: CDenote)
             (D1: EDenote): CDenote :=
  {|
    nrm := (D0.(brk)) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘ ⋃ (WhileSem.iter_nrm_lt_n D1 D0));
    brk := ∅;
    cnt := ∅;
    err := D0.(err) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            ⋃ (WhileSem.iter_err_lt_n D1 D0));
    inf := D0.(inf) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            Sets.general_union (WhileSem.is_inf D1 D0));
  |}.

Module ForSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D2.(nrm) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          (D2.(cnt) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          D2.(brk))) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         (D2.(nrm) ∘ D1.(err)) ∪
         (D2.(cnt) ∘ D1.(err)) ∪
         D2.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ X) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ X) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         D2.(inf)).

End ForSem.

Definition for_sem
             (D: CDenote)
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote): CDenote :=
  {|
    nrm := D.(nrm) ∘ ⋃ (ForSem.iter_nrm_lt_n D0 D1 D2);
    brk := ∅;
    cnt := ∅;
    err := D.(err) ∪ (D.(nrm) ∘ ⋃ (ForSem.iter_err_lt_n D0 D1 D2));
    inf := D.(inf) ∪ (D.(nrm) ∘ Sets.general_union (ForSem.is_inf D0 D1 D2));
  |}.

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
  | CDoWhile c1 e =>
      do_while_sem (eval_com c1) (eval_r e)
  | CFor c0 e c1 c2 =>
      for_sem
        (eval_com c0) (eval_r e) (eval_com c1) (eval_com c2)
  | CContinue =>
      cnt_sem
  | CBreak =>
      brk_sem
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
        pose proof (IHn i1 i2 e1 s).
        simpl in HH.
        assert (le (rank e1) n) by lia.
        assert (i1 = i2) by auto.
        subst i2.
        unfold SC_or_compute_nrm in H1, H2.
        unfold NonSC_or in H1, H2.
        unfold NonSC_compute_nrm in H1, H2.
        destruct (Int64.signed i1) eqn : I1.
        ++ destruct H1; destruct H1; try contradiction.
          destruct H2; destruct H2; try contradiction.
          destruct H5 as [i2 [? ?]].
          destruct H6 as [i2' [? ?]].
          pose proof (IHn i2 i2' e2 s).
          assert (le (rank e2) n) by lia.
          assert (i2 = i2') by auto.
          subst i2'.
          destruct (Int64.signed i2) eqn : I2.
          --  destruct H7; destruct H7; try contradiction.
              destruct H8; destruct H8; try contradiction.
              rewrite H11, H12.
              tauto.
          --  destruct H7; destruct H7;
              destruct H8; destruct H8.
              all: try rewrite H7 in I2.
              all: try rewrite H8 in I2.
              all: try discriminate.
              rewrite H11, H12.
              tauto.
          --  destruct H7; destruct H7;
              destruct H8; destruct H8.
              all: try rewrite H7 in I2.
              all: try rewrite H8 in I2.
              all: try discriminate.
              rewrite H11, H12.
              tauto.
        ++ destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          subst a b; auto.
        ++ destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          subst a b; auto.
      * unfold and_sem in H, H0. 
        simpl in H, H0.
        unfold and_sem_nrm in H, H0. 
        destruct H as [i1 [? ?]].
        destruct H0 as [i2 [? ?]].
        pose proof (IHn i1 i2 e1 s).
        simpl in HH.
        assert (le (rank e1) n) by lia.
        assert (i1 = i2) by auto.
        subst i2.
        unfold SC_and_compute_nrm in H1, H2.
        unfold NonSC_and in H1, H2.
        unfold NonSC_compute_nrm in H1, H2.
        destruct (Int64.signed i1) eqn : I1.
        ++ destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try contradiction.
          subst a b; auto.
        ++ destruct H1; destruct H1;
          destruct H2; destruct H2.
          all: try rewrite H1 in I1.
          all: try rewrite H2 in I1.
          all: try discriminate.
          destruct H5 as [i2 [? ?]].
          destruct H6 as [i2' [? ?]].
          pose proof IHn i2 i2' e2 s.
          assert(le(rank e2) n) by lia.
          assert (i2 = i2') by auto.
          subst i2'.
          destruct (Int64.signed i2) eqn : I2.
          --  destruct H7; destruct H7; try contradiction.
              destruct H8; destruct H8; try contradiction.
              rewrite H11, H12.
              tauto.
          --  destruct H7; destruct H7;
              destruct H8; destruct H8. 
              all: try rewrite H7 in I2.
              all: try rewrite H8 in I2.
              all: try discriminate.
              rewrite H11, H12.
              tauto.
          --  destruct H7; destruct H7;
              destruct H8; destruct H8. 
              all: try rewrite H7 in I2.
              all: try rewrite H8 in I2.
              all: try discriminate.
              rewrite H11, H12.
              tauto.
        ++  destruct H1; destruct H1;
            destruct H2; destruct H2.
            all: try rewrite H1 in I1.
            all: try rewrite H2 in I1.
            all: try discriminate.
            destruct H5 as [i2 [? ?]].
            destruct H6 as [i2' [? ?]].
            pose proof IHn i2 i2' e2 s.
            assert(le(rank e2) n) by lia.
            assert (i2 = i2') by auto.
            subst i2'.
            destruct (Int64.signed i2) eqn : I2.
            --  destruct H7; destruct H7; try contradiction.
                destruct H8; destruct H8; try contradiction.
                rewrite H11, H12.
                tauto.
            --  destruct H7; destruct H7;
                destruct H8; destruct H8. 
                all: try rewrite H7 in I2.
                all: try rewrite H8 in I2.
                all: try discriminate.
                rewrite H11, H12.
                tauto.
            --  destruct H7; destruct H7;
                destruct H8; destruct H8. 
                all: try rewrite H7 in I2.
                all: try rewrite H8 in I2.
                all: try discriminate.
                rewrite H11, H12.
                tauto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold cmp_sem in H, H0.
        simpl in H, H0.
        unfold cmp_sem_nrm in H, H0.
        unfold cmp_compute_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2' a b; auto.
      * unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2'.
        destruct H2, H4.
        subst a b; auto.
      * unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2'.
        destruct H2, H4.
        subst a b; auto.
      * unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2'.
        destruct H2, H4.
        subst a b; auto.
      * unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2'.
        destruct H2, H4.
        subst a b; auto.
      * unfold arith_sem1 in H, H0.
        simpl in H, H0.
        unfold arith_sem1_nrm in H, H0.
        unfold arith_compute1_nrm in H, H0.
        destruct H as [i1 [i2 [? [? ?]]]].
        destruct H0 as [i1' [i2' [? [? ?]]]].
        pose proof IHn i1 i1' e1 s.
        pose proof IHn i2 i2' e2 s.
        simpl in HH.
        assert(le (rank e1) n) by lia.
        assert(le (rank e2) n) by lia.
        assert (i1 = i1') by tauto.
        assert (i2 = i2') by tauto.
        subst i1' i2'.
        destruct H2, H4.
        subst a b; auto.
    - unfold unop_sem in H, H0.
      destruct op; simpl; intros.
      * unfold not_sem in H, H0.
        simpl in H, H0.
        unfold not_sem_nrm in H, H0.
        unfold not_compute_nrm in H, H0.
        destruct H as [i1 [? ?]].
        destruct H0 as [i1' [? ?]].
        pose proof IHn i1 i1' e s.
        simpl in HH.
        assert(le(rank e) n) by lia.
        assert (i1 = i1') by tauto.
        subst i1'.
        destruct (Int64.signed i1) eqn : I.
        ++ destruct H1; destruct H1; destruct H2; destruct H2.
          all: try discriminate; try contradiction.
          subst a b; auto.
        ++ destruct H1; destruct H1; destruct H2; destruct H2.
          all: try rewrite H1 in I.
          all: try rewrite H2 in I.
          all: try discriminate; try contradiction.
          subst a b; auto.
        ++ destruct H1; destruct H1; destruct H2; destruct H2.
          all: try rewrite H1 in I.
          all: try rewrite H2 in I.
          all: try discriminate; try contradiction.
          subst a b; auto.
      * unfold neg_sem in H, H0.
        simpl in H, H0.
        unfold neg_sem_nrm in H, H0.
        unfold neg_compute_nrm in H, H0.
        destruct H as [i1 [? ?]].
        destruct H0 as [i1' [? ?]].
        pose proof IHn i1 i1' e s.
        simpl in HH.
        assert(le(rank e) n) by lia.
        assert (i1 = i1') by tauto.
        subst i1'.
        destruct H1, H2.
        subst a b; auto.
    - unfold deref_sem_nrm in H, H0.
      destruct H as [i1 [? ?]].
      destruct H0 as [i1' [? ?]].
      pose proof IHn i1 i1' e s.
      simpl in HH.
      assert(le(rank e) n) by lia.
      assert (i1 = i1') by tauto.
      subst i1'.
      rewrite H2 in H1.
      injection H1.
      auto.
    - unfold eval_l in H, H0.
      destruct e eqn : I. 
      * revert H H0.
        unfold_RELS_tac.
        simpl.
        intros.
        contradiction.
      * unfold var_sem_l in H, H0.
        simpl in H, H0.
        subst a b; auto.
      * simpl in H, H0.
        revert H H0.
        unfold_RELS_tac.
        simpl.
        intros.
        contradiction.
      * simpl in H, H0.
        revert H H0.
        unfold_RELS_tac.
        simpl.
        intros.
        contradiction.
      * fold eval_r in H, H0.
        simpl in HH.
        specialize (IHn a b e0 s).
        assert(le (rank e0) n) by lia.
        auto.
      * simpl in H, H0.
        revert H H0.
        unfold_RELS_tac.
        simpl.
        intros.
        contradiction.
Qed.

Lemma eval_r_sem_inj: 
  forall (a b: int64)(e: expr)(s: state),
  (eval_r e).(nrm) s a ->
  (eval_r e).(nrm) s b ->
  a = b.
Proof.
  intros.
  pose proof eval_r_sem_inj_pre (rank e) a b e s.
  auto.
Qed.

Lemma Int64_not_equal_zero:
  forall (v : int64),
  v <> Int64.repr 0 ->
  Int64.signed v <> 0.
Proof.
  intros.
  destruct (Int64.signed v) eqn : J.
  -- rewrite <- J in H.
    rewrite Int64.repr_signed in H.
    contradiction.
  -- lia.
  -- lia.
Qed.

Lemma Int64_not_equal_min_signed:
  forall (v : int64),
  v <> Int64.repr Int64.min_signed ->
  Int64.signed v <> Int64.min_signed.
Proof.
  intros.
  intro.
  rewrite <- H0 in H.
  rewrite Int64.repr_signed in H.
  contradiction.
Qed.

Lemma eval_r_not_err_pre:
  forall (n: nat)(e: expr)(s: state),
  ((eval_r e).(err) s -> False) ->
  le (rank e) n ->
  (exists k, (eval_r e).(nrm) s k).
Proof.
  induction n; simpl; intros.
  + destruct e; simpl; intros.
    - exists (Int64.repr n).
      simpl in H.
      assert(Int64.min_signed <= n <= Int64.max_signed) by lia.
      tauto.
    - unfold deref_sem_nrm.
      simpl in H.
      revert H; unfold_RELS_tac; intros.
      assert(deref_sem_err (fun (s : state) (i : int64) => s.(env) x = i) s -> False) by tauto.
      clear H.
      unfold deref_sem_err in H1.
      destruct (s.(mem) (s.(env) x)) eqn : I.
      * destruct v eqn : J.
        ++ destruct H1.
           exists (s.(env) x).
           tauto.
        ++ exists i, (s.(env) x).
           tauto.
      * destruct H1.
        exists (s.(env) x).
        tauto.
    - simpl in H0.
      lia.
    - simpl in H0.
      lia.
    - simpl in H0.
      lia.
    - simpl in H0.
      lia.
  + destruct e; simpl; intros.
    - exists (Int64.repr n0).
      simpl in H.
      assert(Int64.min_signed <= n0 <= Int64.max_signed) by lia.
      tauto.
    - unfold deref_sem_nrm.
      simpl in H.
      revert H; unfold_RELS_tac; intros.
      assert(deref_sem_err (fun (s : state) (i : int64) => s.(env) x = i) s -> False) by tauto.
      clear H.
      unfold deref_sem_err in H1.
      destruct (s.(mem) (s.(env) x)) eqn : I.
      * destruct v eqn : J.
        ++ destruct H1.
          exists (s.(env) x).
          tauto.
        ++ exists i, (s.(env) x).
          tauto.
      * destruct H1.
        exists (s.(env) x).
        tauto.
    - destruct op; simpl; intros.
      * simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        pose proof IHn e1 s H1 H2.
        destruct H0 as [v1 ?].
        unfold or_sem_nrm.        
        unfold SC_or_compute_nrm.
        unfold NonSC_or.
        unfold NonSC_compute_nrm.
        pose proof Int64.eq_spec v1 (Int64.repr 0).
        destruct (Int64.eq v1 (Int64.repr 0)) eqn : I.
        ++ assert (or_sem_err (eval_r e1).(nrm) (eval_r e2).(err) s -> False) by tauto.
           unfold or_sem_err in H5.
           unfold NonSC_or in H5.
           assert((eval_r e2).(err) s -> False). {
             intros.
             apply H5.
             exists v1.
             tauto.
           }
           specialize (IHn e2 s H6 H3).
           destruct IHn.
           pose proof Int64.eq_spec x (Int64.repr 0).
           destruct (Int64.eq x (Int64.repr 0)) eqn : J.
           -- exists (Int64.repr 0), v1.
              split; auto.
              right.
              split; auto.
              exists x.
              auto.
           -- exists (Int64.repr 1), v1.
              split; auto.
              right.
              split; auto.
              exists x.
              split; auto.
              right.
              split; auto.
              destruct (Int64.signed x) eqn : K.
              ** rewrite <- K in H8.
                  rewrite Int64.repr_signed in H8.
                  contradiction.
              ** lia.
              ** lia.
        ++ exists (Int64.repr 1), v1.
           split; [ apply H0 |].
           left.
           split; auto.
           destruct (Int64.signed v1) eqn : J.
           -- rewrite <- J in H4.
              rewrite Int64.repr_signed in H4.
              contradiction.
           -- lia.
           -- lia.
      * simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        pose proof IHn e1 s H1 H2.
        unfold and_sem_nrm.
        unfold SC_and_compute_nrm.
        unfold NonSC_and.
        unfold NonSC_compute_nrm.
        destruct H0 as [v1 ?].
        pose proof Int64.eq_spec v1 (Int64.repr 0).
        destruct (Int64.eq v1 (Int64.repr 0)) eqn : I.
        ++ exists (Int64.repr 0), v1.
           split; [ apply H0 |].
           left.
           tauto.
        ++ assert (and_sem_err (eval_r e1).(nrm) (eval_r e2).(err) s -> False) by tauto.
           unfold and_sem_err in H5.
           unfold NonSC_and in H5.
           assert((eval_r e2).(err) s -> False). {
             intros.
             apply H5.
             exists v1.
             pose proof Int64_not_equal_zero v1 H4.
             tauto.
           }
           specialize (IHn e2 s H6 H3).
           destruct IHn.
           pose proof Int64.eq_spec x (Int64.repr 0).
           destruct (Int64.eq x (Int64.repr 0)) eqn : J.
           -- exists (Int64.repr 0), v1.
              split; auto.
              right.
              split. {
                apply (Int64_not_equal_zero v1 H4).
              }
              exists x.
              auto.
           -- exists (Int64.repr 1), v1.
              split; auto.
              right.
              split. {
                apply (Int64_not_equal_zero v1 H4).
              }
              exists x.
              split; auto.
              right.
              split; auto.
              destruct (Int64.signed x) eqn : K.
              ** rewrite <- K in H8.
                  rewrite Int64.repr_signed in H8.
                  contradiction.
              ** lia.
              ** lia.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.lt v1 v2) eqn : I.
        ++ exists (Int64.repr 1), v1, v2.
           simpl.
           split; auto; split; auto.
           destruct (Int64.lt v1 v2) eqn : J.
           -- reflexivity.
           -- discriminate.
        ++ exists (Int64.repr 0), v1, v2.
           simpl.
           split; auto; split; auto.
           destruct (Int64.lt v1 v2) eqn : J.
           -- discriminate.
           -- reflexivity.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.lt v2 v1) eqn : I.
        ++ exists (Int64.repr 0), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v2 v1) eqn : J; simpl.
          -- reflexivity.
          -- discriminate.
        ++ exists (Int64.repr 1), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v2 v1) eqn : J; simpl.
          -- discriminate.
          -- reflexivity.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.lt v2 v1) eqn : I.
        ++ exists (Int64.repr 1), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v2 v1) eqn : J; simpl.
          -- reflexivity.
          -- discriminate.
        ++ exists (Int64.repr 0), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v2 v1) eqn : J; simpl.
          -- discriminate.
          -- reflexivity.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.lt v1 v2) eqn : I.
        ++ exists (Int64.repr 0), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v1 v2) eqn : J; simpl.
          -- reflexivity.
          -- discriminate.
        ++ exists (Int64.repr 1), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.lt v1 v2) eqn : J; simpl.
          -- discriminate.
          -- reflexivity.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.eq v1 v2) eqn : I.
        ++ exists (Int64.repr 1), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.eq v1 v2) eqn : J; simpl.
          -- reflexivity.
          -- discriminate.
        ++ exists (Int64.repr 0), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.eq v1 v2) eqn : J; simpl.
          -- discriminate.
          -- reflexivity.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear H IHn.
        unfold cmp_sem_nrm.
        unfold cmp_compute_nrm.
        destruct (Int64.eq v1 v2) eqn : I.
        ++ exists (Int64.repr 0), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.eq v1 v2) eqn : J; simpl.
          -- reflexivity.
          -- discriminate.
        ++ exists (Int64.repr 1), v1, v2.
          simpl.
          split; auto; split; auto.
          destruct (Int64.eq v1 v2) eqn : J; simpl.
          -- discriminate.
          -- reflexivity. 
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear IHn.
        assert(arith_sem1_err Z.add (eval_r e1).(nrm) (eval_r e2).(nrm) s -> False) by tauto.
        unfold arith_sem1_err in H6.
        assert((arith_compute1_err Z.add v1 v2) -> False). {
          intros.
          apply H6.
          exists v1, v2.
          tauto.
        }
        unfold arith_compute1_err in H7.
        unfold arith_sem1_nrm.
        unfold arith_compute1_nrm.  
        exists (Int64.repr (Int64.signed v1 + Int64.signed v2)), v1, v2.
        split; auto; split; auto; split; auto.
        lia.
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear IHn.
        assert(arith_sem1_err Z.sub (eval_r e1).(nrm) (eval_r e2).(nrm) s -> False) by tauto.
        unfold arith_sem1_err in H6.
        assert((arith_compute1_err Z.sub v1 v2) -> False). {
          intros.
          apply H6.
          exists v1, v2.
          tauto.
        }
        unfold arith_compute1_err in H7.
        unfold arith_sem1_nrm.
        unfold arith_compute1_nrm.  
        exists (Int64.repr (Int64.signed v1 - Int64.signed v2)), v1, v2.
        split; auto; split; auto; split; auto.
        lia.    
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear IHn.
        assert(arith_sem1_err Z.mul (eval_r e1).(nrm) (eval_r e2).(nrm) s -> False) by tauto.
        unfold arith_sem1_err in H6.
        assert((arith_compute1_err Z.mul v1 v2) -> False). {
          intros.
          apply H6.
          exists v1, v2.
          tauto.
        }
        unfold arith_compute1_err in H7.
        unfold arith_sem1_nrm.
        unfold arith_compute1_nrm.  
        exists (Int64.repr (Int64.signed v1 * Int64.signed v2)), v1, v2.
        split; auto; split; auto; split; auto.
        lia.            
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear IHn.
        assert(arith_sem2_err (eval_r e1).(nrm) (eval_r e2).(nrm) s -> False) by tauto.
        unfold arith_sem2_err in H6.
        assert((arith_compute2_err v1 v2) -> False). {
          intros.
          apply H6.
          exists v1, v2.
          tauto.
        }
        unfold arith_compute2_err in H7.
        unfold arith_sem2_nrm.
        unfold arith_compute2_nrm.  
        exists (Int64.divs v1 v2), v1, v2.
        split; auto; split; auto; split; auto.
        lia.    
      * simpl in H0.
        assert ((rank e1 <= n) % nat) by lia.
        assert ((rank e2 <= n) % nat) by lia.
        clear H0.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e1).(err) s -> False) by tauto.
        assert ((eval_r e2).(err) s -> False) by tauto.
        pose proof IHn e1 s H0 H1.
        pose proof IHn e2 s H3 H2.
        destruct H4 as [v1 ?].
        destruct H5 as [v2 ?].
        clear IHn.
        assert(arith_sem2_err (eval_r e1).(nrm) (eval_r e2).(nrm) s -> False) by tauto.
        unfold arith_sem2_err in H6.
        assert((arith_compute2_err v1 v2) -> False). {
          intros.
          apply H6.
          exists v1, v2.
          tauto.
        }
        unfold arith_compute2_err in H7.
        unfold arith_sem2_nrm.
        unfold arith_compute2_nrm.  
        exists (Int64.mods v1 v2), v1, v2.
        split; auto; split; auto; split; auto.
        lia.  
    - destruct op; simpl.
      * simpl in H0.
        assert ((rank e <= n) % nat) by lia.
        simpl in H.
        specialize (IHn e s H H1).
        destruct IHn as [v ?].
        unfold not_sem_nrm.
        unfold not_compute_nrm.
        pose proof Int64.eq_spec v (Int64.repr 0).
        destruct (Int64.eq v (Int64.repr 0)).
        ++ exists (Int64.repr 1), v.
           tauto.
        ++ exists (Int64.repr 0), v.
           split; auto.
           left.
           split; auto.
           apply (Int64_not_equal_zero v H3).
      * simpl in H0.
        assert ((rank e <= n) % nat) by lia.
        simpl in H.
        revert H; unfold_RELS_tac; intros.
        assert ((eval_r e).(err) s -> False) by tauto.
        assert (neg_sem_err (eval_r e).(nrm) s -> False) by tauto.
        clear H.
        specialize (IHn e s H2 H1).
        destruct IHn as [v ?].
        unfold neg_sem_nrm.
        unfold neg_compute_nrm.
        unfold neg_sem_err in H3.
        unfold neg_compute_err in H3.
        pose proof Int64.eq_spec v (Int64.repr Int64.min_signed).
        destruct (Int64.eq v (Int64.repr Int64.min_signed)).
        ++ destruct H3.
            exists v.
            split; auto.
            rewrite H4.
            pose proof Int64.signed_range v.
            rewrite Int64.signed_repr; lia.
        ++ exists (Int64.neg v), v.
            split; auto; split; auto.
            apply (Int64_not_equal_min_signed v).
            tauto.
    - simpl in H0.
      assert ((rank e <= n)%nat) by lia.
      clear H0.
      simpl in H.
      revert H; unfold_RELS_tac; intros.
      unfold deref_sem_err in H.
      assert ((eval_r e).(err) s -> False) by tauto.
      assert ((exists i1 : int64,
       (eval_r e).(nrm) s i1 /\ (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit)) -> False) by tauto.
      pose proof IHn e s H0 H1.
      clear IHn H.
      destruct H3 as [v ?].
      unfold deref_sem_nrm.
      destruct (s.(mem) v) eqn : I.
      * destruct v0.
        ++ destruct H2.
              exists v.
              tauto.
        ++ exists i, v.
              tauto.
      * destruct H2.
        exists v.
        tauto.
    - simpl in H0.
      assert ((rank e <= n)%nat) by lia.
      clear H0.
      simpl in H.
      revert H.
      unfold eval_l.
      destruct e eqn : I.
      * simpl; unfold_RELS_tac. tauto.
      * simpl; unfold_RELS_tac. intros.
        exists (s.(env) x).
        reflexivity.
      * simpl; unfold_RELS_tac. tauto.
      * simpl; unfold_RELS_tac. tauto.
      * fold eval_r.
        intros.
        simpl in H1.
        assert ((rank e0 <= n)%nat) by lia.
        pose proof IHn e0 s H H0.
        tauto.
      * simpl; unfold_RELS_tac. tauto.
Qed.

Lemma eval_r_not_err:
  forall (e: expr)(s: state),
  ((eval_r e).(err) s -> False) ->
  (exists k, (eval_r e).(nrm) s k).
Proof.
  intros.
  pose proof eval_r_not_err_pre (rank e) e s.
  auto.
Qed.

Lemma eval_r_both_err_and_nrm_pre:
  forall (n: nat)(e: expr)(s: state)(a: int64),
  (eval_r e).(nrm) s a ->
  (eval_r e).(err) s ->
  le (rank e) n ->
  False.
Proof.
  induction n; intros.
  + destruct e; simpl; intros.
    all: simpl in H1.
    all: try lia.
    - simpl in H.
      simpl in H0.
      lia.
    - simpl in H.
      simpl in H0.
      revert H0; unfold_RELS_tac; intros.
      destruct H0; auto.
      unfold deref_sem_err in H0.
      unfold deref_sem_nrm in H.
      destruct H as [xp [? ?]].
      destruct H0 as [xp' [? ?]].
      subst xp' xp.
      rewrite H2 in H3.
      destruct H3; discriminate.
  + destruct e; simpl; intros.
    - simpl in H.
      simpl in H0.
      lia.
    - simpl in H.
      simpl in H0.
      revert H0; unfold_RELS_tac; intros.
      destruct H0; auto.
      unfold deref_sem_err in H0.
      unfold deref_sem_nrm in H.
      destruct H as [xp [? ?]].
      destruct H0 as [xp' [? ?]].
      subst xp' xp.
      rewrite H2 in H3.
      destruct H3; discriminate.
    - destruct op.
      all: simpl in H.
      all: simpl in H0.
      all: revert H0; unfold_RELS_tac; intros.
      all: simpl in H1.
      all: assert((rank e1 <= n)%nat) by lia.
      all: assert((rank e2 <= n)%nat) by lia.
      all: simpl in IHn.
      * unfold or_sem_nrm in H.
        destruct H as [v1 [? ?]].
        destruct H0.
        ++ apply (IHn e1 s v1 H H0 H2).
        ++ unfold or_sem_err in H0.
           destruct H0 as [v1' [? [? ?]]].
           unfold SC_or_compute_nrm in H4.
           unfold NonSC_or in H4.
           unfold NonSC_compute_nrm in H4.
           unfold NonSC_or in H5.
           pose proof eval_r_sem_inj _ _ _ _ H H0.
           subst v1 v1'.
           destruct H4.
           -- destruct H4.
              rewrite Int64.signed_repr in H4.
              contradiction.
              pose proof Int64.max_signed_pos.
              pose proof Int64.min_signed_neg.
              lia.
           -- destruct H4.
              destruct H5 as [v2 [? ?]].
              apply (IHn e2 s v2 H5 H6 H3).
      * unfold and_sem_nrm in H.
        destruct H as [v1 [? ?]].
        destruct H0.
        ++ apply (IHn e1 s v1 H H0 H2).
        ++ unfold and_sem_err in H0.
          destruct H0 as [v1' [? [? ?]]].
          unfold SC_and_compute_nrm in H4.
          unfold NonSC_and in H4.
          unfold NonSC_compute_nrm in H4.
          unfold NonSC_and in H5.
          pose proof eval_r_sem_inj _ _ _ _ H H0.
          subst v1'.
          destruct H4.
          -- destruct H4.
              subst a v1.
              rewrite Int64.signed_repr in H5.
              contradiction.
              pose proof Int64.max_signed_pos.
              pose proof Int64.min_signed_neg.
              lia.
          -- destruct H4.
              destruct H7 as [v2 [? ?]].
              apply (IHn e2 s v2 H7 H6 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold cmp_sem_nrm in H.
        unfold cmp_compute_nrm in H.
        destruct H as [v1 [v2 [? [? ?]]]].
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
      * unfold arith_sem1_nrm in H.
        unfold arith_compute1_nrm in H.
        unfold arith_sem1_err in H0.
        unfold arith_compute1_err in H0.
        destruct H as [v1 [v2 [? [? [? ?]]]]].
        destruct H0. destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
        ++ destruct H0 as [v1' [v2' [? [? ?]]]].
           pose proof eval_r_sem_inj _ _ _ _ H H0.
           pose proof eval_r_sem_inj _ _ _ _ H4 H7.
           subst v1' v2'.
           lia.
      * unfold arith_sem1_nrm in H.
        unfold arith_compute1_nrm in H.
        unfold arith_sem1_err in H0.
        unfold arith_compute1_err in H0.
        destruct H as [v1 [v2 [? [? [? ?]]]]].
        destruct H0. destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
        ++ destruct H0 as [v1' [v2' [? [? ?]]]].
          pose proof eval_r_sem_inj _ _ _ _ H H0.
          pose proof eval_r_sem_inj _ _ _ _ H4 H7.
          subst v1' v2'.
          lia.
      * unfold arith_sem1_nrm in H.
        unfold arith_compute1_nrm in H.
        unfold arith_sem1_err in H0.
        unfold arith_compute1_err in H0.
        destruct H as [v1 [v2 [? [? [? ?]]]]].
        destruct H0. destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
        ++ destruct H0 as [v1' [v2' [? [? ?]]]].
          pose proof eval_r_sem_inj _ _ _ _ H H0.
          pose proof eval_r_sem_inj _ _ _ _ H4 H7.
          subst v1' v2'.
          lia.
      * unfold arith_sem2_nrm in H.
        unfold arith_compute2_nrm in H.
        unfold arith_sem2_err in H0.
        unfold arith_compute2_err in H0.
        destruct H as [v1 [v2 [? [? [? ?]]]]].
        destruct H0. destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
        ++ destruct H0 as [v1' [v2' [? [? ?]]]].
          pose proof eval_r_sem_inj _ _ _ _ H H0.
          pose proof eval_r_sem_inj _ _ _ _ H4 H7.
          subst v1' v2'.
          lia.        
      * unfold arith_sem2_nrm in H.
        unfold arith_compute2_nrm in H.
        unfold arith_sem2_err in H0.
        unfold arith_compute2_err in H0.
        destruct H as [v1 [v2 [? [? [? ?]]]]].
        destruct H0. destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ apply (IHn _ _ _ H4 H0 H3).
        ++ destruct H0 as [v1' [v2' [? [? ?]]]].
          pose proof eval_r_sem_inj _ _ _ _ H H0.
          pose proof eval_r_sem_inj _ _ _ _ H4 H7.
          subst v1' v2'.
          lia.
    - destruct op; simpl; intros.
      all: simpl in H, H0, H1.
      all: assert ((rank e <= n)%nat) by lia.
      * unfold not_sem_nrm in H.
        destruct H as [v1 [? ?]].
        apply (IHn _ _ _ H H0 H2).
      * unfold neg_sem_nrm in H.
        destruct H as [v1 [? ?]].
        revert H0; unfold_RELS_tac; intros.
        unfold neg_compute_nrm in H3.
        destruct H3.
        destruct H0.
        ++ apply (IHn _ _ _ H H0 H2).
        ++ unfold neg_sem_err in H0.
           destruct H0 as [v1' [? ?]].
           pose proof eval_r_sem_inj _ _ _ _ H H0.
           subst v1'.
           unfold neg_compute_err in H5.
           lia.
    - simpl in H, H0, H1.
      assert ((rank e <= n)%nat) by lia.
      revert H0; unfold_RELS_tac; intros.
      unfold deref_sem_nrm in H.
      destruct H as [v1 [? ?]].
      destruct H0.
      * apply (IHn _ _ _ H H0 H2).
      * unfold deref_sem_err in H0.
        destruct H0 as [v1' [? ?]].
        pose proof eval_r_sem_inj _ _ _ _ H H0; subst v1'.
        rewrite H3 in H4; destruct H4; discriminate.
    - simpl in H, H0, H1.
      assert ((rank e <= n)%nat) by lia.
      revert H H0.
      unfold eval_l.
      destruct e eqn : I.
      * simpl; unfold_RELS_tac; contradiction.
      * simpl; unfold_RELS_tac; contradiction.
      * simpl; unfold_RELS_tac; contradiction.
      * simpl; unfold_RELS_tac; contradiction.
      * fold eval_r.
        simpl in H2.
        assert ((rank e0 <= n)%nat) by lia.
        intros.
        apply (IHn _ _ _ H0 H3 H).
      * simpl; unfold_RELS_tac; contradiction.
Qed.

Lemma eval_r_both_err_and_nrm:
  forall (e: expr)(s: state)(a: int64),
  (eval_r e).(nrm) s a ->
  (eval_r e).(err) s ->
  False.
Proof.
  intros.
  pose proof eval_r_both_err_and_nrm_pre (rank e) e s a.
  auto.
Qed.

End DntSem_WhileDC.