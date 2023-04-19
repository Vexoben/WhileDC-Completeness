Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Require Import PV.HoareLogic.
Local Open Scope string.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       HoareSimpleWhile
       HoareSimpleWhile_Derived
       HoareSimpleWhile_Admissible.

Theorem hoare_complet: forall P Q c,
   valid {{ P }} c {{ Q }} -> provable {{ P }} c {{ Q }}.
Proof.
  unfold valid.
  intros; revert P Q H.
  induction c; intros P Q HT. 
  + assert (P |-- Q).
    - assn_unfold.
      intros.
      specialize (HT s s).
      apply HT; auto.
      unfold eval_com.
      unfold skip_sem.
      unfold_RELS_tac.
      reflexivity.
    - eapply hoare_conseq_post; [|apply H].
      apply (hoare_skip P).
  + pose proof (hoare_asgn_fwd P x e).
    apply (hoare_conseq_post _ _ _ _ H).
    assn_unfold; simpl.
    unfold const_sem.
    unfold_substs.
    unfold var_sem.
    unfold ei2exprZ.
    unfold exp.
    unfold exprZ_eq.
    intros.
    destruct H0 as [n [? ?] ].
    pose proof (HT (state_subst s x n) s).
    apply H2; auto.
    unfold eval_com.
    unfold asgn_sem.
    split; auto.
    intros.
    unfold state_subst.
    destruct (x =? Y)%string eqn : I; auto.
    apply String.eqb_eq in I.
    rewrite I in H3; contradiction.
  + admit.
  + apply hoare_if.
    - specialize (IHc1 Assn(P && [[e]]) Q).
      apply IHc1.
      intros.
      specialize (HT s1 s2); apply HT.
      * revert H. assn_unfold. tauto.
      * simpl.
        unfold if_sem.
        left.
        unfold test_true.
        unfold_RELS_tac.
        exists s1.
        split; auto.
        split; auto.
        revert H; assn_unfold; tauto.
    - specialize (IHc2 Assn(P && [[!e]]) Q).
      apply IHc2.
      intros.
      specialize (HT s1 s2); apply HT.
      * revert H. assn_unfold. tauto.
      * simpl.
        unfold if_sem.
        right.
        unfold test_false.
        unfold_RELS_tac.
        exists s1.
        split; auto.
        split; auto.
        revert H; assn_unfold.
        unfold eb2assn.
        simpl.
        unfold not_sem.
        intros.
        unfold negb in H; destruct H.
        destruct (eval_expr_bool e s1); auto.
  +  
        
        
        

Qed.
