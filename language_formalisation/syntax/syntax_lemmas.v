Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export Arith syntax.
Require Import Le Compare_dec.

Ltac inv H := inversion H; clear H; subst.

Lemma change_j_get_k Γ j k Aj :
  j <> k -> get_vtype Γ k = get_vtype (ctx_change_var Γ j Aj) k.
Proof.
revert j k. induction Γ; intros j k neq_jk; auto.
destruct k; destruct j; auto.
+ omega.
+ simpl. apply IHΓ. omega.
Qed.

Lemma change_j_get_j Γ j Aj_orig Aj 
  (p_j : get_vtype Γ j = Some Aj_orig) :
  get_vtype (ctx_change_var Γ j Aj) j = Some Aj.
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
+ destruct v as (name, num). destruct (num=?i) eqn:cmp.
  apply Nat.eqb_eq in cmp. rewrite cmp. reflexivity. reflexivity.
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
destruct (num=?i) eqn:cmpi;
destruct (num=?j) eqn:cmpj; simpl.
+ apply Nat.eqb_eq in cmpi. apply Nat.eqb_eq in cmpj. rewrite cmpi in *.
  rewrite cmpj. rewrite <-beq_nat_refl. auto.
+ apply Nat.eqb_eq in cmpi. rewrite cmpi in *. rewrite Nat.eqb_neq in cmpj.
  apply not_eq_sym in cmpj. rewrite <-Nat.eqb_neq in cmpj.
  rewrite cmpj. rewrite <-beq_nat_refl. reflexivity.
+ apply Nat.eqb_eq in cmpj. rewrite cmpj in *. rewrite Nat.eqb_neq in cmpi.
  apply not_eq_sym in cmpi. rewrite <-Nat.eqb_neq in cmpi.
  rewrite cmpi. rewrite <-beq_nat_refl. reflexivity.
+ rewrite cmpi. rewrite cmpj. reflexivity.
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
destruct (num=?i) eqn:cmpi. destruct (num=?j) eqn:cmpj.
apply Nat.eqb_eq in cmpi. apply Nat.eqb_eq in cmpj.
rewrite cmpj, cmpi in *. all: auto.
}{
revert i j. induction c; intros i j; try destruct p; simpl;
try f_equal; try apply IHc || apply IHc1 || apply IHc2;
apply v_switch_sym.
}{
induction h; simpl; f_equal; try auto || apply IHh.
}
Qed.

Lemma switch_ij_get_k Γ k i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  i <> k -> j <> k ->
  get_vtype Γ k = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) k.
Proof.
revert k i j p_i p_j. induction Γ;
intros k i j p_i p_j neq_ik neq_jk. auto.
revert i j p_i p_j neq_ik neq_jk. destruct k;
intros i j p_i p_j neq_ik neq_jk.
+ destruct i.
  - omega.
  - simpl. destruct j; auto. omega.
+ destruct i; destruct j; simpl; auto.
  - apply change_j_get_k. omega.
  - apply change_j_get_k. omega.
  - unfold ctx_switch_vars in IHΓ. apply IHΓ; auto; omega.
Qed.
      
Lemma switch_ij_get_j Γ i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  get_vtype Γ i = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) j.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_i. rewrite p_i.
  apply (change_j_get_j Γ j Aj). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma switch_ij_get_i Γ i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  get_vtype Γ j = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) i.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_j. rewrite p_j.
  apply (change_j_get_j Γ i Ai). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma ctx_switch_extend1 Γ A i j Ai Aj
    (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) 
    (pp_i : get_vtype (CtxU Γ A) (i+1) = Some Ai)
    (pp_j : get_vtype (CtxU Γ A) (j+1) = Some Aj) :
  CtxU (ctx_switch_vars Γ i j Ai Aj p_i p_j) A
    = 
  (ctx_switch_vars (CtxU Γ A) (i+1) (j+1) Ai Aj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; auto.
+ rename v into G. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (ctx_change_var Γ' j Ai) A
      =
    ctx_change_var (CtxU Γ' A) (j + 1) Ai).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+1 = S j) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ G) i Aj)).
    rewrite H. f_equal.
    destruct i; auto; simpl.
    assert (i+1 = S i) by omega; rewrite H0; auto.
Qed.

Lemma ctx_switch_extend2 Γ B A i j Ai Aj
    (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) 
    (pp_i : get_vtype (CtxU (CtxU Γ B) A) (i+2) = Some Ai)
    (pp_j : get_vtype (CtxU (CtxU Γ B) A) (j+2) = Some Aj) :
  CtxU (CtxU (ctx_switch_vars Γ i j Ai Aj p_i p_j) B) A
    = 
  (ctx_switch_vars (CtxU (CtxU Γ B) A) (i+2) (j+2) Ai Aj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; simpl in *; discriminate.
+ rename v into G. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (CtxU (ctx_change_var Γ' j Ai) B) A
      =
    ctx_change_var (CtxU (CtxU Γ' B) A) (j + 2) Ai).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+2 = S (S j)) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ G) i Aj)).
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

Lemma v_no_var_j_switch_i_j v i j:
  v_no_var_j v j -> v_no_var_j (v_switch_vars v j i) i
with c_no_var_j_switch_i_j c i j:
  c_no_var_j c j -> c_no_var_j (c_switch_vars c j i) i
with h_no_var_j_switch_i_j h i j:
  h_no_var_j h j -> h_no_var_j (h_switch_vars h j i) i.
Proof.
{
clear v_no_var_j_switch_i_j.
revert i j; induction v; intros i j orig; simpl; auto;
try constructor; try destruct orig; simpl; auto.
destruct v as (name, num).
destruct (num=?j) eqn:cmpj.
+ simpl in orig. destruct orig. apply Nat.eqb_eq in cmpj. auto.
+ destruct (num=?i) eqn:cmpi; simpl.
  * apply Nat.eqb_eq in cmpi. rewrite cmpi in *. simpl in orig. auto.
  * apply Nat.eqb_neq in cmpi. auto.
}{
clear c_no_var_j_switch_i_j.
revert i j; induction c; intros i j orig; try destruct p; simpl; auto;
try constructor; try destruct orig; simpl; auto.
constructor; destruct H0; auto.
}{
clear h_no_var_j_switch_i_j.
revert i j; induction h; intros i j orig; simpl; auto;
try constructor; try destruct orig; simpl; auto.
}
Qed.

Lemma get_ctx_remove_unchanged Γ i j :
  i > j -> get_vtype Γ j = get_vtype (ctx_remove_var Γ i) j.
Proof.
revert i j; induction Γ; intros i j lt; auto.
destruct i; destruct j; simpl.
+ omega.
+ omega.
+ reflexivity.
+ apply IHΓ. omega.
Qed.

Lemma get_ctx_remove_changed Γ i j :
  i <= j -> get_vtype Γ (S j) = get_vtype (ctx_remove_var Γ i) j.
Proof.
revert i j; induction Γ; intros i j lt; auto.
destruct i; destruct j; simpl; auto.
+ omega.
+ apply IHΓ. omega.
Qed.

Lemma ctx_remove_extend Γ i A :
  CtxU (ctx_remove_var Γ i) A = ctx_remove_var (CtxU Γ A) (i+1).
Proof.
revert i; induction Γ; intros i; assert (i+1 = S i) by omega; rewrite H.
+ reflexivity.
+ simpl. reflexivity.
Qed.

Lemma get_ctx_insert_unchanged Γ A i j:
  i < j -> get_vtype Γ i = get_vtype (ctx_insert_var Γ A j) i.
Proof.
revert i j. induction Γ; intros i j cmp; simpl.
destruct i; destruct j; simpl; try reflexivity.
+  omega.
+ destruct j.
  - omega.
  - simpl. destruct i; auto. apply IHΓ. omega.
Qed.

Lemma get_ctx_insert_changed Γ A i j:
  i >= j -> get_vtype Γ i = get_vtype (ctx_insert_var Γ A j) (i+1).
Proof.
revert i j. induction Γ; intros i j cmp; simpl.
destruct i; destruct j; simpl; try reflexivity.
destruct j; destruct i.
+ auto.
+ assert (S i + 1 = S (S i)) by omega. rewrite H. auto.
+ omega.
+ simpl. apply IHΓ. omega.
Qed.

Lemma ctx_insert_extend Γ i A_ins A :
  CtxU (ctx_insert_var Γ A_ins i) A = ctx_insert_var (CtxU Γ A) A_ins (i+1).
Proof.
revert i; induction Γ; intros i; assert (i+1 = S i) by omega; rewrite H.
+ reflexivity.
+ simpl. reflexivity.
Qed.