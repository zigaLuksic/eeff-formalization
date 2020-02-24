Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic". *)
Require Export type_aux_lemmas operational_semantics.

Ltac inv H := inversion H; clear H; subst.

(* ==================== Substitution Lemma ==================== *)

Fixpoint v_subs_out_typesafe Γ v A v_s A_s {struct v}:
  has_vtype (CtxU Γ A_s) v A -> has_vtype Γ v_s A_s ->
  has_vtype Γ (v_subs_out v v_s) A

with c_subs_out_typesafe Γ c C v_s A_s {struct c}:
  has_ctype (CtxU Γ A_s) c C -> has_vtype Γ v_s A_s ->
  has_ctype Γ (c_subs_out c v_s) C

with h_subs_out_typesafe Γ h Σ D v_s A_s {struct h}:
  has_htype (CtxU Γ A_s) h Σ D -> has_vtype Γ v_s A_s ->
  has_htype Γ (h_subs_out h v_s) Σ D.
Proof.
{
intros orig sub. unfold v_subs_out.
assert (CtxU Γ A_s = ctx_insert Γ A_s 0) by (destruct Γ; auto).
eapply v_subs_typesafe; eauto. destruct Γ; omega.
}{
intros orig sub. unfold c_subs_out.
assert (CtxU Γ A_s = ctx_insert Γ A_s 0) by (destruct Γ; auto).
eapply c_subs_typesafe; eauto. destruct Γ; omega.
}{
intros orig sub. unfold h_subs_out.
assert (Γ = ctx_remove (CtxU Γ A_s) 0) by auto.
assert (CtxU Γ A_s = ctx_insert Γ A_s 0) by (destruct Γ; auto).
eapply h_subs_typesafe; eauto. destruct Γ; omega.
}
Qed.

(* ==================== Preservation ==================== *)

Theorem preservation Γ c c' C:
  has_ctype Γ c C -> step c c' -> has_ctype Γ c' C.
Proof.
intros orig step. revert C orig. 
induction step; intros C orig.
+ unfold c_subs2_out. apply shape_prodmatch in orig.
  destruct orig as [A [B [pair]]]. apply shape_pair in pair. destruct pair.
  eapply c_subs_out_typesafe. eapply c_subs_out_typesafe.
  all: eauto. inv H0. apply v_shift_typesafe; auto.
+ unfold c_subs2_out. apply shape_summatch in orig.
  destruct orig as [A [B [vty [inl _]]]].
  eapply c_subs_out_typesafe. exact inl. apply shape_inl in vty. auto.
+ unfold c_subs2_out. apply shape_summatch in orig.
  destruct orig as [A [B [vty [_ inr]]]].
  eapply c_subs_out_typesafe. exact inr. apply shape_inr in vty. auto.
+ apply shape_listmatch in orig.
  destruct orig as [A[_[ty1 _]]]. auto.
+ unfold c_subs2_out. 
  apply shape_listmatch in orig. destruct orig as [A[vty[_ ty2]]]. 
  apply shape_cons in vty. destruct vty as [vty vsty].  
  eapply c_subs_out_typesafe; eauto. eapply c_subs_out_typesafe; eauto.
  eapply v_shift_typesafe; eauto. inv vty. auto.
+ apply shape_app in orig. destruct orig as [A [f]].
  eapply c_subs_out_typesafe; eauto.
+ apply shape_letrec in orig. destruct orig as [A [C' [c1ty]]].
  eapply c_subs_out_typesafe; eauto. apply TypeV. inv c1ty.
  inv H. inv H3. assumption. inv H. inv H0. assumption.  
  apply TypeFun. apply TypeC. 
  - inv c1ty. inv H0. assumption.
  - inv c1ty. assumption.
  - eapply TypeLetRec. 2: exact c1ty.
    assert (CtxU (CtxU (CtxU Γ A) A) (TyFun A C') 
      = ctx_insert (CtxU (CtxU Γ A) (TyFun A C')) A 2)
    as insertion. { simpl. destruct Γ; auto. }
    rewrite insertion. apply c_insert_typesafe. assumption.
    inv H. inv H0. inv H5. assumption.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]].
  apply TypeC. inv c1ty. 3 : eapply TypeDoBind. all: eauto. inv H. auto.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]]. eapply c_subs_out_typesafe. eauto.
  apply shape_ret in c1ty. assumption.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]]. eapply shape_op in c1ty.
  destruct c1ty as [Aop [Bop [gets [vty]]]]. apply TypeC.
  - inv H. inv H1. assumption.
  - inv H. assumption.
  - eapply TypeOp; eauto. eapply TypeC. inv H0. assumption. inv H. assumption.
    eapply TypeDoBind. exact H0.
    assert (CtxU (CtxU Γ Bop) A' = ctx_insert (CtxU Γ A') Bop 1).
    { simpl. destruct Γ; auto. }
    rewrite H1. apply c_insert_typesafe. assumption. inv H0. inv H2. assumption.
+ eapply shape_handle in orig. destruct orig as [C' [hty]]. 
  apply TypeC. inv hty. assumption. inv hty. inv H1. assumption.
  eapply TypeHandle; eauto.
+ eapply shape_handle in orig. rename C into D. destruct orig as [C[hty]].
  destruct C as (A, Σ, E). eapply shape_handler in hty as hty'. 
  destruct hty' as [Σ'[D'[retty[hcty[r[st]]]]]]. eapply shape_ret in H.
  eapply c_subs_out_typesafe. 2:exact H. apply TypeC. 
  - inv H. apply WfCtxU; assumption.
  - inv hty. inv H2. assumption.
  - eapply TypeCSubtype; eauto.
+ eapply shape_handle in orig. rename C into D. 
  destruct orig as [C[hty]]. destruct C as (A, Σ, E).
  eapply shape_handler in hty as hty'.
  destruct hty' as [Σ'[D'[retty[hcty[r[st]]]]]].
  eapply shape_op in H0 as opt. destruct opt as [Aop[Bop[gets]]].
  assert (wf_ctx Γ) by (inv hty; assumption). 
  apply TypeC; auto. inv hty. inv H5. assumption.
  eapply TypeCSubtype; eauto. inv H2.
  assert (wf_vtype Aop) by (inv H4; assumption).
  assert (wf_vtype Bop) by (inv H5; inv H6; assumption).
  assert (wf_ctype D') by (inv hcty; assumption).
  unfold c_subs2_out. eapply c_subs_out_typesafe.
  instantiate (1:= TyFun Bop D').
  unfold c_subs2_out. eapply c_subs_out_typesafe.
  instantiate (1:= Aop).
  - eapply sig_subtype_get_Some in gets; eauto.
    destruct gets as [A'[B'[gets']]]. inv H8.
    eapply ctx_subtype_ctype. eapply case_has_type; eauto.
    * apply WfCtxU. apply WfCtxU. 2: apply WfTyFun. all: auto.
    * apply SubtypeCtxU. apply SubtypeCtxU.
      apply ctx_subtype_refl; auto. apply SubtypeTyFun; auto.
      apply csubtype_refl. all: auto.
  - assert (CtxU Γ (TyFun Bop D') = ctx_insert Γ (TyFun Bop D') 0).
    { destruct Γ; simpl; reflexivity. }
    rewrite H8. eapply v_insert_typesafe. auto. apply WfTyFun; auto.
  - apply TypeV. auto. apply WfTyFun; auto.
    eapply TypeFun. apply TypeC. apply WfCtxU. all: auto.
    eapply TypeHandle. 2: exact H5.
    assert (CtxU Γ Bop = ctx_insert Γ Bop 0) by (destruct Γ; simpl; auto).
    rewrite H8. eapply v_insert_typesafe. 2: auto.
    apply TypeV. auto. apply WfTyHandler. inv H0. auto. auto.
    eapply TypeVSubtype. instantiate (1:=(TyHandler (CTy A Σ' E) D'));
    inv H5; inv H10; inv H0.
    * apply TypeV. auto. apply WfTyHandler. apply WfCTy; auto.
      all: try (inv hcty; assumption). eapply wf_eqs_sig_subtype; eauto.
      inv hcty. assumption. apply TypeHandler; auto.
    * apply SubtypeTyHandler. apply SubtypeCTy. 2: auto.
      apply vsubtype_refl. inv H5. inv H10. auto.
      eapply eqs_subtype_refl. inv H5. inv H10. eauto.
      apply csubtype_refl. assumption.
Qed.

(* ==================== Progress ==================== *)

Theorem progress c C:
  has_ctype CtxØ c C ->
  (exists v, c = Ret v) \/
  (exists o v c', c = Op o v c') \/
  (exists c', step c c'). 
Proof.
revert C. induction c; intros C orig.
+ left. eauto.
+ apply shape_absurd in orig. apply shape_empty in orig as shape. 
  destruct shape. subst. apply shape_var_ctx_empty in orig.
  destruct orig.
+ right. right. clear IHc.
  eapply shape_prodmatch in orig. destruct orig as [A [B [vty]]].
  eapply shape_prod_full in vty as shape. 2: reflexivity.
  destruct shape.
  - destruct H0 as [n same]. rewrite same in *.
    apply shape_var_ctx_empty in vty. destruct vty.
  - destruct H0 as [v1[v2[same[ty1]]]]. subst.
    eexists. apply Step_ΠMatch.
+ right. right. clear IHc1 IHc2.
  eapply shape_summatch in orig. destruct orig as [A [B [vty]]].
  eapply shape_sum_full in vty as shape. 2: reflexivity.
  destruct shape. 2: destruct H0.
  - destruct H0 as [n same]. rewrite same in *.
    apply shape_var_ctx_empty in vty. destruct vty.
  - destruct H0 as [v' [same]]. rewrite same. eexists. apply Step_ΣMatch_Inl.
  - destruct H0 as [v' [same]]. rewrite same. eexists. apply Step_ΣMatch_Inr.
+ right. right.
  eapply shape_listmatch in orig. destruct orig as [A[vty[cty1 cty2]]].
  eapply shape_list_full in vty as shape; eauto. destruct shape. 
  destruct H as [n same]. subst. apply shape_var_ctx_empty in vty. destruct vty. 
  destruct H.
  - exists c1. subst. apply Step_ListMatch_Nil.
  - destruct H as [w[ws[same[wty wsty]]]]. subst. 
    eexists. apply Step_ListMatch_Cons. 
+ right. right.
  eapply shape_app_full in orig. 2: reflexivity.
  destruct orig as [A [fty]]. eapply shape_tyfun_full in fty as ffty.
  2: reflexivity. destruct ffty.
  - destruct H0 as [n same]. rewrite same in *.
    apply shape_var_ctx_empty in fty. destruct fty.
  - destruct H0 as [x [c [same]]]. subst. eexists. apply Step_App.
+ right. left. eauto.
+ right. right. clear IHc1 IHc2.
  eexists. apply Step_LetRec.
+ right. right. clear IHc2. destruct C as (A, Σ, E). 
  eapply shape_dobind in orig. destruct orig as [A' [c1ty]].
  apply IHc1 in c1ty as IH. clear IHc1. destruct IH as [h1 | [h2 | h3]].
  - destruct h1. rewrite H0 in *. eexists. apply Step_DoBind_Ret.
  - destruct h2. destruct H0. destruct H0 as [c' same]. rewrite same in *.
    eexists. apply Step_DoBind_Op.
  - destruct h3. eexists. apply Step_DoBind_step. exact H0.
+ right. right. eapply shape_handle in orig. rename C into D.
  destruct orig as [C [hty]]. apply IHc in H as H'. clear IHc.
  destruct C as (A, Σ, E). eapply shape_tyhandler_full in hty as shape.
  2: reflexivity. destruct shape.
  { destruct H0 as [n same]. subst.
    apply shape_var_ctx_empty in hty. contradiction. }
  destruct H0 as [c_r[h[Σ'[D'[same[crty]]]]]]. subst.
  destruct H'. 2: destruct H1.
  - destruct H1 as [v]. subst. eexists. apply Step_Handle_Ret.   
  - destruct H1 as [op[v[c']]]. subst. destruct H0 as [hcsty[r[sigsty]]].
    apply shape_op in H. destruct H as [A_op[B_op[gets]]].
    eapply sig_subtype_get_Some in gets. 2: exact sigsty.
    destruct gets as [A'[B'[gets']]].
    eapply h_has_case in hcsty. 2: exact gets'.
    destruct hcsty as [c_op finds].
    eexists. eapply Step_Handle_Op. eauto.    
  - destruct H1 as [c']. eexists. apply Step_Handle_Step. exact H1.
Qed.
