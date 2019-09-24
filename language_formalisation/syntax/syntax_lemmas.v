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
  rewrite matches. auto.
Qed.

Lemma change_j_get_k Γ j k αj :
  j <> k -> get_vtype_i Γ k = get_vtype_i (ctx_change_var Γ j αj) k.
Proof.
revert j k. induction Γ; intros j k neq_jk; auto.
destruct k; destruct j; auto.
+ apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ simpl. apply IHΓ. omega.
Qed.

Lemma change_j_get_j Γ j αj_orig αj 
  (p_j : get_vtype_i Γ j = Some αj_orig) :
  get_vtype_i (ctx_change_var Γ j αj) j = Some αj.
Proof.
revert j p_j. induction Γ; intros j p_j; simpl in p_j.
+ discriminate.
+ destruct j; auto. simpl. apply IHΓ. assumption.
Qed.


Lemma v_switch_ii v i : v_switch_vars v i i = v
with c_switch_ii c i : c_switch_vars c i i = c
with h_switch_ii h i : h_switch_vars h i i = h.
Proof.
{
revert i. induction v; intros i; simpl; try reflexivity;
try f_equal; try apply IHv || apply IHv1 || apply IHv2.
+ destruct v as (name, num). remember (num=?i) as cmp. destruct cmp.
  apply beq_nat_eq in Heqcmp. rewrite Heqcmp. reflexivity. reflexivity.
+ apply c_switch_ii.
+ apply c_switch_ii.
+ apply h_switch_ii.
}{
revert i. induction c; intros i; simpl; try reflexivity; try destruct p;
try f_equal; try apply v_switch_ii; try apply IHc || apply IHc1 || apply IHc2.
}{
revert i. induction h; intros i; simpl; try reflexivity.
f_equal. apply IHh. apply c_switch_ii.
}
Qed.

Lemma v_switchswitch v i j:
  v_switch_vars (v_switch_vars v i j) i j = v
with c_switchswitch c i j:
  c_switch_vars (c_switch_vars c i j) i j = c
with h_switchswitch h i j:
  h_switch_vars (h_switch_vars h i j) i j = h.
Proof.
all: revert i j.
{
induction v; intros i j; simpl; try reflexivity; try f_equal;
try apply IHv || apply IHv1 || apply IHv2;
try apply c_switchswitch || apply h_switchswitch.

destruct v as (name, num).
remember (num=?i) as cmpi. destruct cmpi;
remember (num=?j) as cmpj; destruct cmpj; simpl.
+ apply beq_nat_eq in Heqcmpi. apply beq_nat_eq in Heqcmpj. rewrite Heqcmpi.
  rewrite Heqcmpi in Heqcmpj. rewrite Heqcmpj. rewrite <-beq_nat_refl. auto.
+ apply beq_nat_eq in Heqcmpi. rewrite Heqcmpi in Heqcmpj.
  apply eq_sym in Heqcmpj. rewrite beq_nat_false_iff in Heqcmpj.
  apply not_eq_sym in Heqcmpj. rewrite <-beq_nat_false_iff in Heqcmpj.
  rewrite Heqcmpj. rewrite <-beq_nat_refl. rewrite Heqcmpi. reflexivity.
+ apply beq_nat_eq in Heqcmpj. rewrite Heqcmpj in Heqcmpi.
  apply eq_sym in Heqcmpi. rewrite beq_nat_false_iff in Heqcmpi.
  apply not_eq_sym in Heqcmpi. rewrite <-beq_nat_false_iff in Heqcmpi.
  rewrite Heqcmpi. rewrite <-beq_nat_refl. rewrite Heqcmpj. reflexivity.
+ rewrite <-Heqcmpi. rewrite <-Heqcmpj. reflexivity.
}{
induction c; intros i j; try destruct p; simpl; f_equal;
try apply v_switchswitch || apply IHc || apply IHc1 || apply IHc2.
}{
induction h; intros i j; simpl.
reflexivity. f_equal. apply IHh. apply c_switchswitch.
}
Qed.

Lemma v_switch_sym v i j :
  v_switch_vars v i j = v_switch_vars v j i
with c_switch_sym c i j :
  c_switch_vars c i j = c_switch_vars c j i
with h_switch_sym h i j :
  h_switch_vars h i j = h_switch_vars h j i.
Proof.
{
induction v; simpl;
try f_equal; try apply IHv || apply IHv1 || apply IHv2;
try apply h_switch_sym || apply c_switch_sym; try reflexivity.
destruct v as (name, num).
remember (num=?i) as cmpi. remember (num=?j) as cmpj.
destruct cmpi; destruct cmpj; auto.
apply eq_sym in Heqcmpi. apply eq_sym in Heqcmpj. 
apply beq_nat_true_iff in Heqcmpi. 
apply beq_nat_true_iff in Heqcmpj.
rewrite Heqcmpj in Heqcmpi. rewrite Heqcmpi. auto.
}{
revert i j. induction c; intros i j; try destruct p; simpl;
try f_equal; try apply IHc || apply IHc1 || apply IHc2;
apply v_switch_sym.
}{
induction h; simpl; f_equal; try auto || apply IHh.
}
Qed.

Lemma switch_ij_get_k Γ k i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  i <> k -> j <> k ->
  get_vtype_i Γ k = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) k.
Proof.
revert k i j p_i p_j. induction Γ;
intros k i j p_i p_j neq_ik neq_jk. auto.
revert i j p_i p_j neq_ik neq_jk. destruct k;
intros i j p_i p_j neq_ik neq_jk.
+ destruct i.
  - apply beq_nat_false_iff in neq_ik. simpl in neq_ik. discriminate.
  - simpl. destruct j; auto.
    apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ destruct i; destruct j; simpl; auto.
  - apply change_j_get_k. omega.
  - apply change_j_get_k. omega.
  - unfold ctx_switch_vars in IHΓ. apply IHΓ; auto; omega.
Qed.
      
Lemma switch_ij_get_j Γ i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  get_vtype_i Γ i = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) j.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_i. rewrite p_i.
  apply (change_j_get_j Γ j αj). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma switch_ij_get_i Γ i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  get_vtype_i Γ j = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) i.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_j. rewrite p_j.
  apply (change_j_get_j Γ i αi). auto.
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

Lemma find_op_None_switch h i j op:
  find_op_case h op = None -> find_op_case (h_switch_vars h i j) op = None.
Proof.
intro orig. induction h; auto.
simpl. simpl in *.
destruct (op==o).
+ discriminate.
+ apply IHh. assumption.
Qed.

Lemma find_op_Some_switch h i j op x_op k_op c_op:
  find_op_case h op = Some (x_op, k_op, c_op) ->
  find_op_case (h_switch_vars h i j) op
    =
  Some (x_op, k_op, c_switch_vars c_op (i+2) (j+2)).
Proof.
intro orig.
induction h; auto; simpl; simpl in *.
+ discriminate.
+ destruct (op==o).
  - f_equal. inv orig. auto.
  - apply IHh. auto.
Qed.

