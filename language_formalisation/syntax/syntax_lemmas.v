Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export Arith syntax.
Require Import Le Compare_dec.

Ltac inv H := inversion H; clear H; subst.

Lemma gets_same Γ (id:var_id) (db_i:nat) :
  id_has_dbi id db_i = true -> get_vtype Γ id = get_vtype_i Γ db_i.
Proof.
revert id db_i. induction Γ; intros id db_i matches; destruct id as (name, num).
+ auto.
+ simpl in matches. apply beq_nat_true in matches.
  rewrite matches. simpl. auto.
Qed.

Lemma get_in_changed_other Γ j k αj :
  j <> k -> get_vtype_i Γ k = get_vtype_i (ctx_change_var Γ j αj) k.
Proof.
revert j k. induction Γ; intros j k neq_jk.
auto.
simpl.
destruct k.
+ destruct j; auto.
  apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ destruct j; auto.
  simpl. apply IHΓ. omega.
Qed.

Lemma get_in_changed_same Γ j αj_orig αj 
  (p_j : get_vtype_i Γ j = Some αj_orig) :
  get_vtype_i (ctx_change_var Γ j αj) j = Some αj.
Proof.
revert j p_j. induction Γ; intros j p_j.
+ simpl in p_j. discriminate.
+ destruct j; auto. simpl.
  apply IHΓ. simpl in p_j. assumption.
Qed.

Lemma get_in_switched_other Γ k i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  i <> k -> j <> k ->
  get_vtype_i Γ k = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) k.
Proof.
revert k i j p_i p_j. induction Γ;
intros k i j p_i p_j neq_ik neq_jk.
auto.
revert i j p_i p_j neq_ik neq_jk. destruct k;
intros i j p_i p_j neq_ik neq_jk.
+ destruct i.
  - apply beq_nat_false_iff in neq_ik. simpl in neq_ik. discriminate.
  - simpl. destruct j; auto.
    apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ destruct i.
  - destruct j; auto.
    simpl. apply get_in_changed_other. omega.
  - destruct j; simpl.
    * apply get_in_changed_other. omega.
    * unfold ctx_switch_vars in IHΓ. apply IHΓ.
      auto. auto. omega. omega.
Qed.
      
Lemma get_in_switched_i Γ i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  get_vtype_i Γ i = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) j.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_i. rewrite p_i.
  apply (get_in_changed_same Γ j αj). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma get_in_switched_j Γ i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  get_vtype_i Γ j = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) i.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_j. rewrite p_j.
  apply (get_in_changed_same Γ i αi). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma ctx_switch_extend1 Γ α i j αi αj
    (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) 
    (pp_i : get_vtype_i (CtxU Γ α) (i+1) = Some αi)
    (pp_j : get_vtype_i (CtxU Γ α) (j+1) = Some αj) :
  CtxU (ctx_switch_vars Γ i j αi αj p_i p_j) α
    = 
  (ctx_switch_vars (CtxU Γ α) (i+1) (j+1) αi αj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; auto.
+ rename v into γ. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (ctx_change_var Γ' j αi) α
      =
    ctx_change_var (CtxU Γ' α) (j + 1) αi).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+1 = S j) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ γ) i αj)).
    rewrite H. f_equal.
    destruct i; auto; simpl.
    assert (i+1 = S i) by omega; rewrite H0; auto.

Qed.

Lemma ctx_switch_extend2 Γ β α i j αi αj
    (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) 
    (pp_i : get_vtype_i (CtxU (CtxU Γ β) α) (i+2) = Some αi)
    (pp_j : get_vtype_i (CtxU (CtxU Γ β) α) (j+2) = Some αj) :
  CtxU (CtxU (ctx_switch_vars Γ i j αi αj p_i p_j) β) α
    = 
  (ctx_switch_vars (CtxU (CtxU Γ β) α) (i+2) (j+2) αi αj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; simpl in *; discriminate.
+ rename v into γ. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (CtxU (ctx_change_var Γ' j αi) β) α
      =
    ctx_change_var (CtxU (CtxU Γ' β) α) (j + 2) αi).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+2 = S (S j)) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ γ) i αj)).
    rewrite H. f_equal.
    destruct i; auto; simpl.
    assert (i+2 = S (S i)) by omega; rewrite H0; auto.
Qed.

Lemma hcases_switch_None h i j op:
  find_op_case h op = None -> find_op_case (h_switch_vars h i j) op = None.
Proof.
intro orig.
induction h; auto.
simpl. simpl in *.
remember (op==o) as cmp.
destruct cmp.
+ discriminate.
+ apply IHh. assumption.
Qed.

Lemma hcases_switch_Some h i j op x_op k_op c_op:
  find_op_case h op = Some (x_op, k_op, c_op) ->
  find_op_case (h_switch_vars h i j) op
    =
  Some (x_op, k_op, c_switch_vars c_op (i+2) (j+2)).
Proof.
intro orig.
induction h; auto.
+ simpl. discriminate.
+ simpl. simpl in *.
  remember (op==o) as cmp. destruct cmp.
  - f_equal. inv orig. auto.
  - apply IHh. auto.
Qed.