Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas.

Ltac inv H := inversion H; clear H; subst.


Lemma extend_get_proof Γ A i Ai:
  get_vtype_i Γ i = Some Ai-> get_vtype_i (CtxU Γ A) (i + 1) = Some Ai.
Proof.
assert (i + 1 = S i) by omega.
induction Γ; rewrite H; auto.
Qed.


Fixpoint v_insert_typesafe Γ v A A_ins i {struct v} :
  has_vtype Γ v A ->
  has_vtype (ctx_insert_var Γ A_ins i) (Sub.v_shift v 1 i) A
with c_insert_typesafe Γ c C A_ins i {struct c} :
  has_ctype Γ c C ->
  has_ctype (ctx_insert_var Γ A_ins i) (Sub.c_shift c 1 i) C
with h_insert_typesafe Γ h Σ D A_ins i {struct h} :
  has_htype Γ h Σ D ->
  has_htype (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D.
Proof.
{
clear v_insert_typesafe.
revert A i. induction v; intros A i orig; simpl; inv orig.
+ apply TypeVar. simpl. destruct v as (name, num).
  simpl. destruct (i<=?num) eqn:cmp.
  - erewrite gets_same. instantiate (1:=num+1).
    erewrite <-get_ctx_insert_changed.
    * erewrite gets_same in H1. 2:instantiate (1:=num). assumption.
      simpl. apply Nat.eqb_eq. reflexivity.
    * apply leb_complete in cmp. omega.
    * simpl. apply Nat.eqb_eq. reflexivity.
  - erewrite gets_same. instantiate (1:=num).
    erewrite <-get_ctx_insert_unchanged.
    * erewrite gets_same in H1. 2:instantiate (1:=num). assumption.
      simpl. apply Nat.eqb_eq. reflexivity.
    * apply leb_iff_conv in cmp. omega.
    * simpl. apply Nat.eqb_eq. reflexivity.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv. assumption.
+ apply TypeInr. apply IHv. assumption.
+ apply TypePair; try apply IHv1 || apply IHv2; assumption.
+ apply TypeFun. rewrite ctx_insert_extend. auto.
+ apply TypeHandler; auto. rewrite ctx_insert_extend. auto.
+ apply TypeVAnnot. apply IHv. assumption.
}{
clear c_insert_typesafe.
revert Γ C i. induction c; intros Γ C i orig; simpl; inv orig.
+ apply TypeRet. auto.
+ eapply TypeΠMatch.
  - eapply v_insert_typesafe. exact H4.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H. auto.
+ eapply TypeΣMatch.
  - apply v_insert_typesafe. exact H6.
  - rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ eapply TypeApp.
  - apply v_insert_typesafe. exact H2.
  - auto.
+ eapply TypeOp. exact H5. auto.
  rewrite ctx_insert_extend. auto.
+ eapply TypeLetRec.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H. auto.
  - rewrite ctx_insert_extend. auto.
+ eapply TypeHandle.
  - apply v_insert_typesafe. exact H2.
  - auto.
+ eapply TypeCAnnot. auto.
}{
clear h_insert_typesafe.
revert Γ Σ D i. induction h; intros Γ Σ D i orig; simpl; inv orig.
+ apply TypeCasesØ.
+ apply TypeCasesU; auto.
  - assert (forall h,
      find_op_case h o = None ->
      find_op_case (Sub.h_shift h 1 i) o = None).
    * intros h' orig. induction h'; auto.
      simpl in *. destruct (o==o0). discriminate. auto.
    * apply H. assumption.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H. auto.
}
Qed.

Fixpoint v_shift_typesafe
  (Γ:ctx) (A0:vtype) v A {struct v} :
  has_vtype Γ v A ->
  has_vtype (CtxU Γ A0) (Sub.v_shift v 1 0) A

with c_shift_typesafe
  (Γ:ctx) (A0:vtype) c C {struct c} :
  has_ctype Γ c C ->
  has_ctype (CtxU Γ A0) (Sub.c_shift c 1 0) C

with h_shift_typesafe
  (Γ:ctx) (A0:vtype) h Σ D {struct h} :
  has_htype Γ h Σ D ->
  has_htype (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D.
Proof.
all: intro orig;
assert (ctx_insert_var Γ A0 0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H.
apply v_insert_typesafe. assumption.
apply c_insert_typesafe. assumption.
apply h_insert_typesafe. assumption.
Qed.


Fixpoint v_negshift_typesafe
  (Γ:ctx) v A i {struct v} :
  has_vtype Γ v A ->
  v_no_var_j v i ->
  has_vtype (ctx_remove_var Γ i) (Sub.v_negshift v 1 i) A

with c_negshift_typesafe
  (Γ:ctx) c C i {struct c} :
  has_ctype Γ c C ->
  c_no_var_j c i ->
  has_ctype (ctx_remove_var Γ i) (Sub.c_negshift c 1 i) C

with h_negshift_typesafe
  (Γ:ctx) h Σ D i {struct h} :
  has_htype Γ h Σ D ->
  h_no_var_j h i ->
  has_htype (ctx_remove_var Γ i) (Sub.h_negshift h 1 i) Σ D.
Proof.
{
clear v_negshift_typesafe.
revert Γ A i. induction v; intros Γ A i orig no_var; simpl; inv orig;
simpl in no_var.
+ destruct v as (name, num). simpl in *.
  apply TypeVar. destruct (i<=?num) eqn:cmp.
  - erewrite gets_same. instantiate (1:=(num - 1)).
    erewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct num. destruct no_var. omega.
      simpl. assert (num-0=num) by omega. rewrite H. assumption.
    * omega.
    * simpl. apply Nat.eqb_eq. omega.
  - erewrite gets_same. instantiate (1:=num).
    erewrite <-get_ctx_remove_unchanged. assumption.
    * apply leb_iff_conv in cmp. omega.
    * simpl. apply Nat.eqb_eq. omega.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. eapply IHv. exact H1. assumption.
+ apply TypeInr. eapply IHv. exact H1. assumption.
+ apply TypePair; destruct no_var.
  - eapply IHv1. exact H2. assumption.
  - eapply IHv2. exact H4. assumption.
+ apply TypeFun. rewrite ctx_remove_extend.
  apply c_negshift_typesafe; assumption.
+ apply TypeHandler; destruct no_var.
  - rewrite ctx_remove_extend. apply c_negshift_typesafe; assumption.
  - apply h_negshift_typesafe; assumption.
+ apply TypeVAnnot. apply IHv; assumption.
}{
clear c_negshift_typesafe.
revert Γ C i. induction c; intros Γ C i orig no_var; simpl; inv orig;
simpl in no_var; try destruct no_var.
+ apply TypeRet. apply v_negshift_typesafe; assumption.
+ eapply TypeΠMatch.
  - apply v_negshift_typesafe. exact H4. assumption.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. apply IHc; assumption.
+ eapply TypeΣMatch; destruct H0.
  - apply v_negshift_typesafe. exact H6. assumption.
  - rewrite ctx_remove_extend. apply IHc1; assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ eapply TypeApp; apply v_negshift_typesafe.
  exact H2. all: assumption.
+ eapply TypeOp. exact H5.
  - apply v_negshift_typesafe; assumption.
  - rewrite ctx_remove_extend. apply IHc; assumption.
+ eapply TypeLetRec.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. apply IHc1; assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ eapply TypeHandle.
  - apply v_negshift_typesafe. exact H2. assumption.
  - apply IHc; assumption.
+ eapply TypeCAnnot. apply IHc; assumption.
}{
clear h_negshift_typesafe.
revert Γ Σ i. induction h; intros Γ Σ i orig no_var; simpl; inv orig;
simpl in no_var; try destruct no_var.
- apply TypeCasesØ.
- apply TypeCasesU.
  assert (forall h, find_op_case h o = None 
    -> find_op_case (Sub.h_negshift h 1 i) o = None).
  + intro h'. induction h'; intro orig; auto.
    simpl. simpl in orig. destruct (o==o0); auto. discriminate.
  + apply H1. assumption.
  + auto.
  + rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H1.
    apply c_negshift_typesafe; assumption.
}
Qed.

