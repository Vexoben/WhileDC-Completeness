## WhileDC Relative Completeness Proof

### Definition

- `syntax`

> ```math
> \begin{align}
> &\mbox{e:= } n\ |\ x\ |\ e_1\otimes e_2\ |\ \odot e \ |\ *e\ |\  \&e \\
> &\otimes \in \{ +,-,\times,/,\%,<,>,\le,\ge,=,\ne, ||, \&\& \} \\
> & \odot \in\{!,-\} \\
> & c:= \ \text{skip}\ |\ x:=e\ |\ *e_1:=e_2\ |\ c_1;c_2\ |\ \text{if}\ (e) \ \text{then}\ c_1\ \text{else}\ c_2\ |\ \text{while}\ (e) \ c\ |\\ & \ \ \ \ \ \ \ \ \ \ \text{do}\ c \ \text{while}\ (e)\ |\ \text{for}\ (c_1;e;c_2)\ c_3\ |\ \text{break}\ |\ \text{continue}
>  \end{align}
> ```


- `semantic` 

  ```
  val := Vuninit | Vint (i: int64)
  
  Record state: Type := {
    env: var_name -> int64;
    mem: int64 -> option val;
  }.
  
  // the type of the denotational semantic of expressions
  Record EDenote: Type := {
    nrm: state -> int64 -> Prop;
    err: state -> Prop;
  }.
  
  // the type of the denotational semantic of commands
  Record CDenote: Type := {
    nrm: state -> state -> Prop;
    brk: state -> state -> Prop;
    cnt: state -> state -> Prop;
    err: state -> Prop;
    inf: state -> Prop
  }.
  ```

  The detailed definitions of the denotational semantic can be found in the file `WhileDCDenotations.v` .

- `assertion`

  ```
  Definition assertion: Type := state -> Prop.
  ```

- `HoareTriple`

  ```
  Inductive HoareTriple: Type :=
  | BuildHoareTriple: assertion -> com -> assertion -> assertion -> assertion -> HoareTriple.
  ```

  We notate $\text{BuildHoareTriple}\ P\ c\ Q_{nrm}\ Q_{brk}\ Q_{cnt}$  as $`\{\{P\}\}\ c\ \{\{Q_{nrm},Q_{brk},Q_{cnt} \}\}`$ 

- `valid` 

  ```
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
  ```

- weakest precondition

  ```
  Definition wp (c:com) (Q Q_brk Q_cnt:assertion) : assertion :=
    fun s => 
    ((eval_com c).(err) s -> False) /\
    (forall s', (eval_com c).(nrm) s s' -> Q s') /\ 
    (forall s', (eval_com c).(brk) s s' -> Q_brk s') /\ 
    (forall s', (eval_com c).(cnt) s s' -> Q_cnt s').
  ```

- provable

  ```
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
        provable {{ P }} c1 {{ Q, R_brk, R_cnt }} ->
        provable {{ Q }} c2 {{ R, R_brk, R_cnt }} ->
        provable {{ P }} (CSeq c1 c2) {{ R, R_brk, R_cnt }}
  | hoare_if:
      forall (P Q Q_brk Q_cnt: assertion) (e: expr) (c1 c2: com),
        provable {{ P && e }} c1 {{ Q, Q_brk, Q_cnt }} ->
        provable {{ P && !e }} c2 {{ Q, Q_brk, Q_cnt }} ->
        (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
        provable {{ P }}(CIf e c1 c2) {{ Q, Q_brk, Q_cnt }}
  | hoare_while:
      forall (P P_brk: assertion) (e: expr) (c: com),
        provable {{ P && e }} c {{ P, P_brk, P }} ->
        (forall s: state, (P s -> (eval_r e).(err) s -> False)) ->
        provable {{ P }} (CWhile e c) {{ (P && !e) || P_brk, asrt_false, asrt_false }}
  | hoare_do_while:
      forall (P R R_brk: assertion) (e: expr) (c: com),
        provable {{ P }} c {{ R, R_brk, R}} ->
        provable {{ R && e }} c {{ R, R_brk, R }} ->
        (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
        provable {{ P }} (CDoWhile c e) {{ (R && !e) || R_brk, asrt_false, asrt_false }}
  | hoare_for:
      forall (P Q R R_brk: assertion) (e: expr) (c1 c2 c3: com),
        provable {{ P }} c1 {{ R, asrt_false, asrt_false }} ->
        (forall s: state, (R s -> (eval_r e).(err) s -> False)) ->
        provable {{ R && e }} c3 {{ Q, R_brk, Q }} ->
        provable {{ Q }} c2 {{ R, asrt_false, asrt_false }} ->
        provable {{ P || (CFor c1 e c2 c3) {{ (R && !e) || R_brk, asrt_false, asrt_false }}   
  | hoare_asgn_deref_fwd:
      forall (P Q : assertion) (e1 e2 : expr) (a b: int64),
      (forall (s:state), P s -> ((eval_r e1).(nrm) s a)) ->
      (forall (s:state), P s -> ((eval_r e2).(nrm) s b)) ->
        P |-- (exp (fun u => (sepcon (store a u) Q) )) ->
        provable ( {{ P }} ( * (e1) ::= e2 ) {{ (store a (Vint b)) * Q, asrt_false, asrt_false }} )
  | hoare_asgn_var_fwd:
      forall (P Q: assertion) (e: expr) (a b: int64) (x : var_name),
      (forall (s:state), P s -> ((eval_r e).(nrm) s b)) ->
      (forall (s:state), P s -> s.(env) x = a) ->
        P |-- (exp (fun u => (sepcon (store a u) Q) )) ->
        provable ( {{ P }} (x = e) {{(store a (Vint b)) * Q, asrt_false, asrt_false }})
  | hoare_conseq:
      forall (P P' Q Q_brk Q_cnt Q' Q'_brk Q'_cnt: assertion) (c: com),
        provable {{ P' }} c {{ Q', Q'_brk, Q'_cnt }} ->
        P |-- P' ->
        Q' |-- Q ->
        Q'_brk |-- Q_brk ->
        Q'_cnt |-- Q_cnt ->
        provable {{ P }} c {{ Q, Q_brk, Q_cnt }}
  | hoare_exist:
      forall (P : int64 -> assertion) (Q Q_brk Q_cnt: assertion) (c : com),
        (forall (a : int64), provable ({{P a}} c {{ Q, Q_brk, Q_cnt}} )) ->
        (provable ( {{ exp64 P }} c {{ Q, Q_brk, Q_cnt}}  )).
  ```

### About the proof

##### `hoare_asgn_deref_fwd`

Since the condition `valid {{ P }} *e1 = e2 {{ Q }}` secure that `e1` can be safely evaluated under the assertion `P` , we can prove that
```math
P \vdash \exists a, (P \wedge [e_1 = a])
```
Due to `hoare_exist` , it suffices to prove that 

```math
\forall a, \text{provable} (P \wedge [e_1 =a]) (*e_1 = e_2) Q
```
Similarly, it suffices to prove that

```math
\forall a,b, \text{provable} (P \wedge [e_1 =a] \wedge [e_2 = b]) (*e_1 = e_2) Q
```
Therefore, we can use `hoare_asgn_deref_fwd` , and the postcondition is like
```math
store(a, b) * ((P \wedge [e_1 =a] \wedge [e_2 = b])/ \text{delete }a \text{ from }mem)
```
Then, we prove that this post-condition can derive $Q$ by `conseq`.

##### `hoare_while`

The weakest precondition is the loop invariant.

##### `hoare_do_while`

For the statement `do c while (e)`, the weakest precondition of `do c while (e)` after `c` implies the weakest precondition of `while(e) c`. This weakest precondition of `while(e) c` is considered as the loop invariant.

##### `hoare_for`

For the statement `for (c1; e; c2) c3`,

The loop invariant is taken as the weakest precondition of `for (skip; e; c2) c3`, denoted as $R$.

Let $P$ be the weakest precondition of $c_1$ that leads to $R$, and $Q$ be the weakest precondition of $c_2$ that leads to $R$.

It suffices to prove:

- $\text{provable } P (c_1) (R, \text{false}, \text{false})$
- $\text{provable } (R \land [e]) (c_3) (Q, \text{if terminated by break, to the postcondition}, Q)$
- $\text{provable } Q (c_2) (R, \text{false}, \text{false})$
- $(R \land [\lnot e]) \vdash \text{postcondition}$
