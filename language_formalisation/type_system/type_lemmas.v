(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas.


Ltac inv H := inversion H; clear H; subst.

Fixpoint v_subs_typesafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype Γ v A -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype Γ c C -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct h}:
  has_htype Γ h Σ D -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
{
clear v_subs_typesafe.
revert Γ A i. induction v; intros Γ A i orig in_ctx vstyped;
simpl; inv orig.
+ destruct v as (name, num). simpl.
  destruct (num=?i) eqn:cmp.
  - rewrite (gets_same _ _ i) in H1.
    * rewrite H1 in in_ctx. injection in_ctx. intro samety.
      rewrite samety. assumption.
    * simpl. assumption.
  - apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv; auto.
+ apply TypeInr. apply IHv; auto.
+ apply TypePair; try apply IHv1 || apply IHv2; auto.
+ apply TypeFun. eapply c_subs_typesafe.
  - assumption.
  - assert (i+1=S i) by omega. rewrite H. simpl.
    exact in_ctx.
  - apply v_shift_typesafe. assumption.
+ apply TypeHandler.
  - eapply c_subs_typesafe.
    * assumption.
    * assert (i+1=S i) by omega. rewrite H. simpl. exact in_ctx.
    * apply v_shift_typesafe. assumption.
  - eapply h_subs_typesafe.
    * assumption.
    * exact in_ctx.
    * assumption.
+ apply TypeVAnnot. apply IHv; assumption.
}{
clear c_subs_typesafe.
assert (forall i, i+1=S i) as Si by (intro; omega).
assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
revert Γ C i v_s. induction c; intros Γ C i v_s orig in_ctx vstyped;
simpl; inv orig.
+ apply TypeRet. eapply v_subs_typesafe. 2 : exact in_ctx. all: assumption.
+ eapply TypeΠMatch.
  - eapply v_subs_typesafe. exact H4. exact in_ctx. assumption.
  - apply IHc. assumption.
    * rewrite SSi. assumption.
    * rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
+ eapply TypeΣMatch.
  { eapply v_subs_typesafe. exact H6. exact in_ctx. assumption. }
  all: try apply IHc1 || apply IHc2; try apply v_shift_typesafe; auto.
  all: rewrite Si; assumption.
+ eapply TypeApp.
  - eapply v_subs_typesafe. exact H2. exact in_ctx. assumption.
  - eapply v_subs_typesafe. auto. exact in_ctx. assumption.
+ eapply TypeOp. exact H5.
  - eapply v_subs_typesafe. 2: exact in_ctx. assumption. assumption.
  - apply IHc; auto.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption.
+ eapply TypeLetRec.
  - apply IHc1. assumption.
    * rewrite SSi. assumption.
    * rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
  - apply IHc2. assumption.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption.
+ eapply TypeHandle.
  - eapply v_subs_typesafe. exact H2. exact in_ctx. assumption.
  - apply IHc; auto.
+ eapply TypeCAnnot. auto.
}{
clear h_subs_typesafe.
assert (forall i, i+1=S i) as Si by (intro; omega).
assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
revert Γ Σ D i v_s. induction h; intros Γ Σ D i v_s orig in_ctx vstyped;
simpl; inv orig.
+ apply TypeCasesØ.
+ apply TypeCasesU.
  assert (forall h,
    find_op_case h o = None ->
    find_op_case (Sub.h_sub h (i, v_s)) o = None).
  * intros h' cantfind. induction h'. auto.
    simpl. simpl in cantfind. destruct (o==o0). discriminate.
    apply IHh'. exact cantfind.
  * apply H. assumption.
  * auto.
  * rewrite SSi. eapply c_subs_typesafe; auto.
    - simpl. exact in_ctx.
    - rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
}
Qed.


Fixpoint v_sub_out_typesafe
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype (CtxU Γ A_s) v A -> has_vtype Γ v_s A_s ->
  has_vtype Γ (vsub_out v v_s) A
with c_sub_out_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype (CtxU Γ A_s) c C -> has_vtype Γ v_s A_s ->
  has_ctype Γ (csub_out c v_s) C
with h_sub_out_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (v_s:val) (A_s:vtype) {struct h}:
  has_htype (CtxU Γ A_s) h Σ D -> has_vtype Γ v_s A_s ->
  has_htype Γ (hsub_out h v_s) Σ D.
Proof.
{
intros orig sub. unfold vsub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply v_negshift_typesafe.
eapply v_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply v_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold csub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply c_negshift_typesafe.
eapply c_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply c_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold hsub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply h_negshift_typesafe.
eapply h_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply h_no_var_sub. apply v_shift_makes_no_var.
}
Qed.

