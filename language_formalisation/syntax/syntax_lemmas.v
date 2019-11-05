Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export Arith syntax.
Require Import Le Compare_dec.

Ltac inv H := inversion H; clear H; subst.


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
revert i; induction Γ; intros i; assert (i+1 = S i) by omega; rewrite H; auto.
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
revert i; induction Γ; intros i; assert (i+1 = S i) by omega; rewrite H; auto.
Qed.