(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Export syntax.
Require Import Le Compare_dec.

Ltac inv H := inversion H; clear H; subst.

(* ==================== Ctx Modification ==================== *)

Lemma get_ctx_remove_unchanged Γ i j :
  i > j -> get_vtype Γ j = get_vtype (ctx_remove Γ i) j.
Proof.
revert i j; induction Γ; intros i j lt; simpl.
destruct i; auto. destruct j; destruct i; simpl; omega || auto.
apply IHΓ. omega.
Qed.


Lemma get_ctx_remove_changed Γ i j :
  i <= j -> get_vtype Γ (S j) = get_vtype (ctx_remove Γ i) j.
Proof.
revert i j; induction Γ; intros i j lt; auto. simpl.
- destruct i; auto.
- destruct i; destruct j; simpl; auto. omega. apply IHΓ. omega.
Qed.


Lemma ctx_remove_extend Γ i A :
  CtxU (ctx_remove Γ i) A = ctx_remove (CtxU Γ A) (1+i).
Proof.
revert i; induction Γ; intros i; auto.
Qed.


Lemma get_ctx_insert_unchanged Γ A i j:
  i < j -> get_vtype Γ i = get_vtype (ctx_insert Γ A j) i.
Proof.
revert i j. induction Γ; intros i j cmp; simpl.
destruct i; destruct j; simpl; try reflexivity.
+  omega.
+ destruct j.
  - omega.
  - simpl. destruct i; auto. apply IHΓ. omega.
Qed.


Lemma get_ctx_insert_changed Γ A i j:
  i >= j -> get_vtype Γ i = get_vtype (ctx_insert Γ A j) (1+i).
Proof.
revert i j. induction Γ; intros i j cmp; simpl.
destruct i; destruct j; simpl; try reflexivity.
destruct j; destruct i; auto.
+ omega.
+ simpl. apply IHΓ. omega.
Qed.


Lemma get_ctx_insert_new Γ A i:
  ctx_len Γ >= i -> get_vtype (ctx_insert Γ A i) i = Some A.
Proof.
revert i. induction Γ; intros i len; simpl; destruct i.
+ simpl. reflexivity.
+ simpl in *. omega.
+ simpl. reflexivity.
+ simpl in *. apply IHΓ. omega.
Qed.


Lemma ctx_insert_extend Γ i A_ins A :
  CtxU (ctx_insert Γ A_ins i) A = ctx_insert (CtxU Γ A) A_ins (1+i).
Proof.
revert i; induction Γ; intros i; auto.
Qed.


Lemma ctx_insert_remove Γ i j A (cmp : i <= j):
  ctx_insert (ctx_remove Γ j) A i = ctx_remove (ctx_insert Γ A i) (1+j).
Proof.
revert i j cmp. induction Γ; intros i j cpm. 
destruct i. simpl. destruct j; simpl; reflexivity.
simpl. destruct j. omega. simpl. reflexivity. simpl. destruct j. 
assert (i=0) by omega. rewrite H. simpl. destruct Γ; simpl; reflexivity.
destruct i. simpl. reflexivity. simpl. f_equal. apply IHΓ. omega.
Qed.


Lemma ctx_insert_remove_alt Γ i j A (cmp : i > j):
  ctx_insert (ctx_remove Γ j) A i = ctx_remove (ctx_insert Γ A (1+i)) j.
Proof.
revert i j cmp. induction Γ; intros i j cpm; simpl. 
all: destruct j; simpl; auto.
all: destruct i; simpl; omega || auto. f_equal. apply IHΓ. omega.
Qed.

(* ==================== Ctx Joins ==================== *)

Lemma join_ctxs_left_unit Γ:
  join_ctxs CtxØ Γ = Γ.
Proof.
induction Γ; simpl; auto. rewrite IHΓ. auto.
Qed.


Lemma join_ctxs_left_step Γ' A Γ:
  join_ctxs (CtxU Γ' A) Γ = join_ctxs Γ' (ctx_insert Γ A (ctx_len Γ)).
Proof.
induction Γ; simpl; auto. f_equal. auto.
Qed.


Fixpoint join_ctxs_assoc Γ Γ' Γ'':
  join_ctxs Γ (join_ctxs Γ' Γ'') = join_ctxs (join_ctxs Γ Γ') Γ''.
Proof.
destruct Γ''; simpl; auto. f_equal. auto.
Qed.


Fixpoint get_tctx_to_ctx Z D A i:
  get_ttype Z i = Some A <-> get_vtype (tctx_to_ctx Z D) i = Some (TyFun A D).
Proof.
constructor; destruct Z; simpl.
+ intro. discriminate. 
+ destruct i. intro same. inv same. reflexivity. 
  intro. apply get_tctx_to_ctx. auto.
+ intro. discriminate.
+ destruct i. intro same. inv same. reflexivity.
  intro. apply get_tctx_to_ctx in H. auto.
Qed.


Lemma get_join_ctxs_left Γ Γ' i:
  get_vtype Γ' i = get_vtype (join_ctxs Γ' Γ) (ctx_len Γ+i).
Proof.
induction Γ; simpl; auto.
Qed.


Fixpoint get_join_ctxs_right Γ Γ' i A {struct Γ'}:
  get_vtype Γ' i = Some A -> get_vtype (join_ctxs Γ Γ') i = Some A.
Proof.
intro gets. destruct Γ'; simpl in *. discriminate.
destruct i. auto. auto.
Qed.


Lemma join_ctxs_insert Γ1 Γ2 i A :
  join_ctxs (ctx_insert Γ1 A i) Γ2 
  = ctx_insert (join_ctxs Γ1 Γ2) A (ctx_len Γ2+i). 
Proof.
induction Γ2; simpl. auto. f_equal. auto.
Qed.


Lemma join_ctxs_remove Γ1 Γ2 i:
    join_ctxs (ctx_remove Γ1 i) Γ2
  = ctx_remove (join_ctxs Γ1 Γ2) (ctx_len Γ2 + i). 
Proof.
induction Γ2; simpl. auto. f_equal. auto.
Qed.


(* ==================== Ctx Length ==================== *)

Lemma len_join_ctxs Γ Γ':
  ctx_len (join_ctxs Γ Γ') = ctx_len Γ + ctx_len Γ'.
Proof.
induction Γ'; simpl; auto. rewrite IHΓ'. omega.
Qed.

Lemma len_tctx_to_ctx Z D:
  tctx_len Z = ctx_len (tctx_to_ctx Z D).
Proof.
induction Z; simpl; auto.
Qed.

(* ==================== Ctx Guarantees ==================== *)

Lemma ctx_len_get_vtype Γ n :
  (exists A, get_vtype Γ n = Some A) <-> ctx_len Γ > n.
Proof.
constructor; revert n; induction Γ; intros n gets; simpl in *.
- destruct gets. discriminate.
- destruct n. omega. apply IHΓ in gets. omega.
- omega.
- destruct n. eauto. apply IHΓ. omega.
Qed.


Lemma ctx_len_gets Γ n A:
  get_vtype Γ n = Some A -> ctx_len Γ > n.
Proof.
intro. apply ctx_len_get_vtype. eauto.
Qed.


Lemma tctx_len_get_ttype Z n :
  (exists A, get_ttype Z n = Some A) <-> tctx_len Z > n.
Proof.
constructor; revert n; induction Z; intros n gets; simpl in *.
- destruct gets. discriminate.
- destruct n. omega. apply IHZ in gets. omega.
- omega.
- destruct n. eauto. apply IHZ. omega.
Qed.


Lemma tctx_len_gets Z n A:
  get_ttype Z n = Some A -> tctx_len Z > n.
Proof.
intro. apply tctx_len_get_ttype. eauto.
Qed.

(* ==================== Term Properties ==================== *)

Fixpoint v_under_var_weaken v i j:
  v_under_var v j -> j <= i -> v_under_var v i
with c_under_var_weaken c i j:
  c_under_var c j -> j <= i -> c_under_var c i
with h_under_var_weaken h i j:
  h_under_var h j -> j <= i -> h_under_var h i.
Proof.
all: intros orig cmp.
{
induction v; simpl in orig; simpl; auto.
+ destruct v. omega.
+ destruct orig. auto.
+ destruct orig. auto.
+ eapply c_under_var_weaken. eauto. omega.
+ destruct orig. constructor. 2: eauto.
  eapply c_under_var_weaken. eauto. omega.
}{
induction c; simpl in orig; simpl; eauto.
all: destruct orig; constructor; eauto. 
2: (destruct H0; constructor).
4: (destruct H0; constructor).
all: try (eapply c_under_var_weaken; eauto; omega).
}{
induction h; simpl in orig; simpl; eauto.
destruct orig; constructor; auto.
eapply c_under_var_weaken; eauto; omega.
}
Qed.

Lemma v_under_var_no_var v i j:
  v_under_var v i -> i<=j -> v_no_var v j
with c_under_var_no_var c i j:
  c_under_var c i -> i<=j -> c_no_var c j
with h_under_var_no_var h i j:
  h_under_var h i -> i<=j -> h_no_var h j.
Proof.
{
induction v; intros under cmp; simpl; auto; simpl in under.
+ destruct v. omega.
+ inv under. auto.
+ inv under. auto.
+ eapply c_under_var_no_var. eauto. omega.
+ inv under. constructor. eapply c_under_var_no_var. eauto.     
  omega. eapply h_under_var_no_var. eauto. omega.
}{
induction c; intros under cmp; simpl; auto.
all: simpl in under; try inv under; try constructor.
all: try eapply v_under_var_no_var; eauto.
all: try eapply c_under_var_no_var; eauto; try omega.
all: destruct H0; constructor; eapply c_under_var_no_var; eauto; omega.
}{
induction h; intros under cmp; simpl; auto.
inv under. constructor. auto. eapply c_under_var_no_var; eauto; omega.
}
Qed.

Lemma find_case_no_var h i op x k c:
  h_no_var h i -> find_case h op = Some (x, k, c) -> c_no_var c (2+i).
Proof.
intros. induction h. simpl in H0. discriminate.
inv H. simpl in H0. destruct (op==o); try inv H0; auto.
Qed.

