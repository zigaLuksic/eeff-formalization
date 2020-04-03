(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Export syntax.
Require Import Le Compare_dec.

(* ==================== Ctx Insert ==================== *)

Fixpoint get_ctx_insert_unchanged Γ A i j {struct Γ}:
  i < j -> get_vtype Γ i = get_vtype (ctx_insert Γ j A) i.
Proof.
intros cmp. destruct Γ; simpl.
all: destruct i; destruct j; simpl; aomega.
apply get_ctx_insert_unchanged. omega.
Qed.


Fixpoint get_ctx_insert_changed Γ A i j {struct Γ}:
  i >= j -> get_vtype Γ i = get_vtype (ctx_insert Γ j A) (1+i).
Proof.
intros cmp. destruct Γ; simpl.
all: destruct i; destruct j; simpl; aomega.
apply get_ctx_insert_changed. omega.
Qed.


Fixpoint get_ctx_insert_new Γ A i {struct Γ}:
  ctx_len Γ >= i -> get_vtype (ctx_insert Γ i A) i = Some A.
Proof.
intros safe. destruct Γ; simpl; destruct i; simpl in *; aomega.
apply get_ctx_insert_new. omega.
Qed.


Lemma ctx_insert_extend Γ i B A :
  CtxU (ctx_insert Γ i B) A = ctx_insert (CtxU Γ A) (1+i) B.
Proof.
revert i; induction Γ; intros i; auto.
Qed.


Fixpoint ctx_insert_comm Γ i A j B {struct Γ}:
  i <= ctx_len Γ -> i <= j ->
  ctx_insert (ctx_insert Γ i A) (1+j) B = ctx_insert (ctx_insert Γ j B) i A.
Proof.
intros. destruct Γ; destruct i; destruct j; simpl; aomega.
f_equal. simpl in *. apply ctx_insert_comm; omega.
Qed.

(* ==================== Ctx Joins ==================== *)

Lemma join_ctxs_CtxØ Γ:
  join_ctxs CtxØ Γ = Γ.
Proof.
induction Γ; simpl; auto. rewrite IHΓ. auto.
Qed.


Lemma join_ctxs_CtxU Γ' A Γ:
  join_ctxs (CtxU Γ' A) Γ = join_ctxs Γ' (ctx_insert Γ (ctx_len Γ) A).
Proof.
induction Γ; simpl; auto. f_equal. auto.
Qed.


Fixpoint join_ctxs_assoc Γ Γ' Γ'':
  join_ctxs Γ (join_ctxs Γ' Γ'') = join_ctxs (join_ctxs Γ Γ') Γ''.
Proof.
destruct Γ''; simpl; auto. f_equal. auto.
Qed.


Fixpoint get_tctx_to_ctx Z i A D {struct Z}:
  get_ttype Z i = Some A <-> get_vtype (tctx_to_ctx Z D) i = Some (TyFun A D).
Proof.
constructor; intros gets; destruct Z; simpl.
all: try discriminate.
all: destruct i; try (inv gets; reflexivity).
+ apply get_tctx_to_ctx. auto.
+ simpl in gets. apply get_tctx_to_ctx in gets. auto.
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
destruct i; auto.
Qed.


Lemma join_ctxs_insert Γ Γ' i A :
    join_ctxs (ctx_insert Γ i A) Γ' 
  = ctx_insert (join_ctxs Γ Γ') (ctx_len Γ'+i) A. 
Proof.
induction Γ'; simpl. auto. f_equal. auto.
Qed.

(* ==================== Length ==================== *)

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


Fixpoint ctx_len_insert_trivial Γ i A {struct Γ}:
  ctx_len (ctx_insert Γ i A) >= ctx_len Γ.
Proof.
destruct Γ; simpl; destruct i; simpl; aomega.
specialize (ctx_len_insert_trivial Γ i A). omega.
Qed.


Fixpoint ctx_len_insert Γ i A {struct Γ}:
  i <= ctx_len Γ ->
  ctx_len (ctx_insert Γ i A) = 1 + ctx_len Γ.
Proof.
intros safe. destruct Γ; simpl; destruct i; simpl in *; aomega.
specialize (ctx_len_insert Γ i A). omega.
Qed.


Lemma inst_len_insert I i v:
  i <= inst_len I -> 
  inst_len (inst_insert I i v) = 1 + inst_len I.
Proof.
revert i v. induction I; intros; simpl.
+ destruct i. simpl. auto. simpl in H. omega.
+ destruct i. auto.
  assert (S i=?0=false) by (apply Nat.eqb_neq; omega). 
  rewrite H0. simpl. rewrite IHI. omega. simpl in H. omega.
Qed.

(* ==================== Ctx Length Guarantees ==================== *)

Fixpoint ctx_len_get_vtype Γ n {struct Γ}:
  (exists A, get_vtype Γ n = Some A) <-> ctx_len Γ > n.
Proof.
constructor; induction Γ; intros; simpl in *; aomega.
- destruct H. discriminate.
- destruct n. omega. apply ctx_len_get_vtype in H. omega.
- destruct n. eauto. apply ctx_len_get_vtype. omega.
Qed.


Lemma ctx_len_get_Some Γ n A:
  get_vtype Γ n = Some A -> ctx_len Γ > n.
Proof.
intro. apply ctx_len_get_vtype. eauto.
Qed.


Fixpoint tctx_len_get_ttype Z n {struct Z}:
  (exists A, get_ttype Z n = Some A) <-> tctx_len Z > n.
Proof.
constructor; destruct Z; intros; simpl in *; aomega.
- destruct H. discriminate.
- destruct n. omega. apply tctx_len_get_ttype in H. omega.
- destruct n. eauto. apply tctx_len_get_ttype. omega.
Qed.


Lemma tctx_len_get_Some Z n A:
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
induction v; simpl in *; try destruct orig; aomega.
+ eapply c_under_var_weaken; eaomega.
+ constructor; eauto. eapply c_under_var_weaken; eaomega.
}{
induction c; simpl in orig; simpl in *; eauto.
all: destruct orig; constructor; eauto. 
2: (destruct H0; constructor). 4: (destruct H0; constructor).
all: try (eapply c_under_var_weaken; eaomega).
}{
induction h; simpl in orig; simpl; eauto.
destruct orig; aconstructor; eapply c_under_var_weaken; eaomega.
}
Qed.


Fixpoint v_under_var_no_var v i j:
  v_under_var v i -> i<=j -> v_no_var v j
with c_under_var_no_var c i j:
  c_under_var c i -> i<=j -> c_no_var c j
with h_under_var_no_var h i j:
  h_under_var h i -> i<=j -> h_no_var h j.
Proof.
all: intros under cmp.
{
induction v; simpl in *; try destruct under; eaomega.
+ eapply c_under_var_no_var; eaomega.
+ constructor. eapply c_under_var_no_var; eaomega. eauto.
}{
induction c; simpl in *; try destruct under; eaomega.
all: constructor; try constructor; try destruct H0; eaomega.
all: try eapply c_under_var_no_var; eaomega.
}{
induction h; simpl in *; auto.
destruct under. aconstructor. eapply c_under_var_no_var; eaomega.
}
Qed.


Lemma get_case_no_var h i op c:
  h_no_var h i -> get_case h op = Some c -> c_no_var c (2+i).
Proof.
intros hno gets. induction h. 
+ simpl in hno. discriminate.
+ inv hno. simpl in gets. destruct (op==o); try inv gets; auto.
Qed.


Lemma get_case_under_var h i op c:
  h_under_var h i -> get_case h op = Some c -> c_under_var c (2+i).
Proof.
intros hno gets. induction h.
+ simpl in hno. discriminate.
+ inv hno. simpl in gets. destruct (op==o); try inv gets; auto.
Qed.

(* ==================== Instantiation Properties ==================== *)

Fixpoint inst_insert_same I n v {struct I}:
  n <= inst_len I ->
  get_inst_val (inst_insert I n v) n = Some v.
Proof.
intros cmp. destruct I; simpl in *.
+ assert (n=0) as same by omega. subst. simpl. auto.
+ destruct (n=?0) eqn:n0; simpl in *.
  - apply Nat.eqb_eq in n0. subst. simpl. auto.
  - apply Nat.eqb_neq in n0. destruct n. omega.
    assert (S n - 1 = n) as same by omega. rewrite same.
    apply inst_insert_same. omega.
Qed.


Fixpoint inst_insert_under I n m v {struct I}:
  n <= inst_len I -> m < n ->
  get_inst_val (inst_insert I n v) m = get_inst_val I m.
Proof.
intros safe cmp. induction I; simpl in *; aomega.
destruct (n=?0) eqn:n0.
- apply Nat.eqb_eq in n0. omega.
- simpl. destruct m. auto. apply inst_insert_under; omega.
Qed.


Fixpoint inst_insert_above I n m v {struct I}:
  n <= inst_len I -> S m > n ->
  get_inst_val (inst_insert I n v) (S m) = get_inst_val I m.
Proof.
intros safe cmp. induction I; simpl in *; aomega.
+ destruct (n=?0); simpl; auto.
+ destruct (n=?0) eqn:n0; simpl.
  - destruct m; auto.
  - destruct n; simpl.
    * apply Nat.eqb_neq in n0. destruct n0. auto.
    * assert (n-0=n) as same by omega. rewrite same.
      destruct m. omega. apply inst_insert_above; omega.
Qed.
