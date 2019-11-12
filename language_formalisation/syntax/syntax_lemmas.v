(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Export Arith syntax.
Require Import Le Compare_dec.

Ltac inv H := inversion H; clear H; subst.


Lemma get_ctx_remove_unchanged Γ i j :
  i > j -> get_vtype Γ j = get_vtype (ctx_remove_var Γ i) j.
Proof.
revert i j; induction Γ; intros i j lt; auto.
destruct i; destruct j; simpl; try omega.
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
  CtxU (ctx_remove_var Γ i) A = ctx_remove_var (CtxU Γ A) (1+i).
Proof.
revert i; induction Γ; intros i; auto.
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
  i >= j -> get_vtype Γ i = get_vtype (ctx_insert_var Γ A j) (1+i).
Proof.
revert i j. induction Γ; intros i j cmp; simpl.
destruct i; destruct j; simpl; try reflexivity.
destruct j; destruct i.
+ auto.
+ auto.
+ omega.
+ simpl. apply IHΓ. omega.
Qed.


Lemma ctx_insert_extend Γ i A_ins A :
  CtxU (ctx_insert_var Γ A_ins i) A = ctx_insert_var (CtxU Γ A) A_ins (1+i).
Proof.
revert i; induction Γ; intros i; auto.
Qed.


Lemma join_ctxs_insert_var Γ1 Γ2 i A :
  join_ctxs (ctx_insert_var Γ1 A i) Γ2= 
    ctx_insert_var (join_ctxs Γ1 Γ2) A (ctx_len Γ2 + i). 
Proof.
induction Γ2; simpl. auto. f_equal. auto.
Qed.


Lemma join_ctx_tctx_insert_var  Γ Z D i A :
  join_ctx_tctx (ctx_insert_var Γ A i) Z D = 
    ctx_insert_var (join_ctx_tctx Γ Z D) A (tctx_len Z + i). 
Proof.
induction Z; simpl. auto. f_equal. auto.
Qed.


Lemma ctx_len_get_vtype Γ n :
  (exists A, get_vtype Γ n = Some A) <-> ctx_len Γ > n.
Proof.
constructor.
+ revert n. induction Γ; intros n gets.
  - simpl in gets. destruct gets. discriminate.
  - simpl in *. destruct n.
    * omega.
    * apply IHΓ in gets. omega.
+ revert n. induction Γ; intros n gets.
  - simpl in gets. omega.
  - simpl in *. destruct n.
    * eauto.
    * apply IHΓ. omega.
Qed.


Lemma ctx_len_gets Γ n A:
  get_vtype Γ n = Some A -> ctx_len Γ > n.
Proof.
intro. apply ctx_len_get_vtype. eauto.
Qed.


Lemma tctx_len_get_ttype Z n :
  (exists A, get_ttype Z n = Some A) <-> tctx_len Z > n.
Proof.
constructor.
+ revert n. induction Z; intros n gets.
  - simpl in gets. destruct gets. discriminate.
  - simpl in *. destruct n.
    * omega.
    * apply IHZ in gets. omega.
+ revert n. induction Z; intros n gets.
  - simpl in gets. omega.
  - simpl in *. destruct n.
    * eauto.
    * apply IHZ. omega.
Qed.


Lemma tctx_len_gets Z n A:
  get_ttype Z n = Some A -> tctx_len Z > n.
Proof.
intro. apply tctx_len_get_ttype. eauto.
Qed.
