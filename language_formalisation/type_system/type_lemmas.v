Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics". *)
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas operational_semantics.


Ltac inv H := inversion H; clear H; subst.

Fixpoint v_subs_typesafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype Γ v A -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype Γ c C -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct h}:
  has_htype Γ h Σ D -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
{
clear v_subs_typesafe.
revert Γ A i. induction v; intros Γ A i orig in_ctx vstyped;
simpl; inv orig.
+ simpl in *. destruct (num=?i) eqn:cmp.
  * apply Nat.eqb_eq in cmp. rewrite <-cmp in in_ctx.
    rewrite H1 in in_ctx. injection in_ctx. intro samety.
    rewrite samety. assumption.
  * apply TypeVar. assumption.
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
  - apply IHc1. exact H5.
    * rewrite SSi. assumption.
    * rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
  - apply IHc2. assumption.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption.
+ eapply TypeHandle.
  - eapply v_subs_typesafe. exact H2. exact in_ctx. assumption.
  - apply IHc; auto.
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
Admitted.


Fixpoint v_sub_out_typesafe
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype (CtxU Γ A_s) v A -> has_vtype Γ v_s A_s ->
  has_vtype Γ (v_sub_out v v_s) A
with c_sub_out_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype (CtxU Γ A_s) c C -> has_vtype Γ v_s A_s ->
  has_ctype Γ (c_sub_out c v_s) C
with h_sub_out_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (v_s:val) (A_s:vtype) {struct h}:
  has_htype (CtxU Γ A_s) h Σ D -> has_vtype Γ v_s A_s ->
  has_htype Γ (h_sub_out h v_s) Σ D.
Proof.
{
intros orig sub. unfold v_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply v_negshift_typesafe.
eapply v_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply v_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold c_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply c_negshift_typesafe.
eapply c_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply c_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold h_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply h_negshift_typesafe.
eapply h_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption.
apply h_no_var_sub. apply v_shift_makes_no_var.
}
Admitted.

Lemma preservation Γ c c' C:
  has_ctype Γ c C -> step c c' -> has_ctype Γ c' C.
Proof.
intros orig step. revert C orig. induction step; intros C orig; inv orig.
+ inv H5.
  unfold c_sub2_out.
  eapply c_sub_out_typesafe. 2: exact H3.
  eapply c_sub_out_typesafe. exact H6.
  apply v_shift_typesafe. assumption.
+ inv H6.
  eapply c_sub_out_typesafe. exact H7. assumption.
+ inv H6.
  eapply c_sub_out_typesafe. exact H8. assumption.
+ inv H2.
  eapply c_sub_out_typesafe. exact H1. assumption.
+ eapply c_sub_out_typesafe. exact H6.
  apply TypeFun. eapply TypeLetRec. 2: exact H5.
  assert (CtxU (CtxU (CtxU Γ A) A) (TyFun A C0) 
    = ctx_insert_var (CtxU (CtxU Γ A) (TyFun A C0)) A 2).
  simpl. destruct Γ; auto.
  rewrite H.
  apply c_insert_typesafe. assumption.
+ eapply TypeHandle. exact H2. apply IHstep. assumption.
+ inv H2. eapply c_sub_out_typesafe. exact H3. inv H4. assumption.
+ unfold c_sub2_out. inv H5.
  eapply c_sub_out_typesafe.
  Focus 2.
    apply TypeFun. eapply TypeHandle.
    apply v_shift_typesafe. exact H3. exact H10.
  inv H3.
  assert (forall h Σ,
    find_op_case h op_id = Some (x_op, k_op, c_op) ->
    get_op_type Σ op_id = Some (A_op, B_op) ->
    has_htype Γ h Σ C ->
    has_ctype (CtxU Γ (TyFun B_op C))
      (c_sub_out c_op (Sub.v_shift v_arg 1 0)) C).
  - intro h'. induction h'; intros Σ' finds gets types.
    * simpl in finds. discriminate.
    * clear H8 H4 H13.
      simpl in finds. inv types; destruct (op_id==o) eqn:name; simpl.
      ++ injection finds. intros. subst.
         simpl in gets. rewrite name in gets.
         injection gets. intros. subst.
         eapply c_sub_out_typesafe. exact H12.
         apply v_shift_typesafe. assumption.
      ++ eapply IHh'; simpl in gets; rewrite name in gets.
         assumption. exact gets. assumption. 
  - eapply H0. exact H. exact H8. assumption. 
Admitted.

Lemma progress c C:
  has_ctype CtxØ c C ->
  (exists v, c = Ret v) \/ (exists o v y c', c = Op o v y c') \/
  (exists c', step c c'). 
Proof.
revert C. induction c; intros C orig.
+ left. exists v. reflexivity.
+ right. right. inv orig. destruct v; inv H4.
  - simpl in H1. discriminate.
  - eexists. apply Step_ΠMatch.
+ right. right. rename v0 into x. rename v1 into y.
  inv orig. destruct v; inv H6.
  - simpl in H1. discriminate.
  - eexists. apply Step_ΣMatch_Inl.
  - eexists. apply Step_ΣMatch_Inr.
+ right. right. inv orig. destruct v; inv H2.
  - simpl in H1. discriminate.
  - eexists. apply Step_App.
+ right. left. exists o. exists v. exists v0. exists c. reflexivity.
+ right. right. rename v into f. rename v0 into x.
  eexists. apply Step_LetRec.
+ inv orig.
+ 