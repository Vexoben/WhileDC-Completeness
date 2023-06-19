- `asgn_deref_sem ` 里面的 `err` 部分，应该是 

    `err := D1.(err) ∪ D2.(err) ∪ asgn_deref_sem_err D2.(nrm)`

- `do_while_sem` 里面的 `nrm` 部分，应该还要包含第一次进入 `c` 直接 break 的情况

- `For` 的 `iter_err_lt_n` 应该加上 `D1` error 的情况

    ```
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
    
    ```

    