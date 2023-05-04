Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PV.Syntax.
Require Import PV.PracticalDenotations.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 局部变量 *)

Module WhileDCL.
Import Lang_While
       Lang_WhileDC
       DntSem_WhileDC
       EDenote CDenote.
(** 下面在程序语句中增加局部变量声明。*)

Inductive com : Type :=
  | CSkip: com
  | CLocalVar (x: var_name) (c1: com): com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com.


Definition set_addr
             (x: var_name)
             (l1 l2: int64):
  state -> state -> Prop :=
  fun s1 s2 => s1.(env) x = l1 /\ s2.(env) x = l2.

Definition alloc_mem (l: int64):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l = None /\ s2.(mem) l = Some Vuninit) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

Definition dealloc_mem (l: int64):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l <> None /\ s2.(mem) l = None) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

Definition alloc_mem_err: state -> Prop :=
  fun s => forall l, s.(mem) l <> None.

Definition local_var_sem
             (x: var_name)
             (D: CDenote): CDenote :=
  {|
    nrm := ⋃ (fun l1 =>
                ⋃ (fun l2 =>
                     (set_addr x l1 l2 ∩ alloc_mem l2) ∘
                     D.(nrm) ∘
                     (set_addr x l2 l1 ∩ dealloc_mem l2)));
    brk := ⋃ (fun l1 =>
                ⋃ (fun l2 =>
                     (set_addr x l1 l2 ∩ alloc_mem l2) ∘
                     D.(brk) ∘
                     (set_addr x l2 l1 ∩ dealloc_mem l2)));
    cnt := ⋃ (fun l1 =>
                ⋃ (fun l2 =>
                     (set_addr x l1 l2 ∩ alloc_mem l2) ∘
                     D.(cnt) ∘
                     (set_addr x l2 l1 ∩ dealloc_mem l2)));
    err := ⋃ (fun l1 =>
                ⋃ (fun l2 =>
                     (set_addr x l1 l2 ∩ alloc_mem l2) ∘
                     D.(err))) ∪
           alloc_mem_err;
    inf := ⋃ (fun l1 =>
                ⋃ (fun l2 =>
                     (set_addr x l1 l2 ∩ alloc_mem l2) ∘
                     D.(inf)))
  |}.

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CLocalVar x c =>
      local_var_sem x (eval_com c)
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

End WhileDCL.

(** * 函数过程调用 *)

Module WhileF.
Import Lang_While.

(** 下面在程序表达式中增加函数调用，在程序语句中增加过程调用。*)
Definition func_name: Type := string.
Definition proc_name: Type := string.

(** 下面是新的表达式定义，这是一个嵌套递归定义。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr
  | EFuncCall (f: func_name) (es: list expr).

(** 下面是新的程序语句定义，这也是一个嵌套递归定义。这里约定_[return_var]_是一个
    特定的表示返回值的变量，而返回指令本身没有参数。*)

Definition return_var: var_name := "__return".

Inductive com : Type :=
  | CSkip: com
  | CLocalVar (x: var_name) (c1: com): com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CProcCall (p: proc_name) (es: list expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com
  | CReturn: com.

(** 下面定义程序中的函数与过程。*)

Record func: Type := {
  name_of_func: func_name;
  body_of_func: com;
  args_of_func: list var_name;
}.

Record proc: Type := {
  name_of_proc: proc_name;
  body_of_proc: com;
  args_of_proc: list var_name;
}.

(** 最后，一段完整的程序由全局变量列表、函数列表、过程列表与入口函数组成。*)

Record prog: Type := {
  gvars: list var_name;
  funcs: list func;
  procs: list proc;
  entry: func_name
}.


End WhileF.



