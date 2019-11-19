(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics".
Require Export declarational subtyping_lemmas substitution_lemmas 
  type_aux_lemmas operational_semantics.


Ltac inv H := inversion H; clear H; subst.

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
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply v_remove_typesafe.
- eapply v_sub_typesafe. assumption. simpl. reflexivity.
  apply v_shift_typesafe. assumption. inv sub. assumption.
- apply v_no_var_subbed. apply v_shift_makes_no_var.
}{
intros orig sub. unfold c_subs_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply c_remove_typesafe.
- eapply c_sub_typesafe. assumption. simpl. reflexivity.
  apply v_shift_typesafe. assumption. inv sub. assumption.
- apply c_no_var_subbed. apply v_shift_makes_no_var.
}{
intros orig sub. unfold h_subs_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply h_remove_typesafe.
- eapply h_sub_typesafe. assumption. simpl. reflexivity.
  apply v_shift_typesafe. assumption. inv sub. assumption.
- apply h_no_var_subbed. apply v_shift_makes_no_var.
}
Qed.


Lemma preservation Γ c c' C:
  has_ctype Γ c C -> step c c' -> has_ctype Γ c' C.
Proof.
intros orig step. revert C orig. 
induction step; intros C orig.
+ unfold c_subs2_out. apply shape_prodmatch in orig.
  destruct orig as [A [B [pair]]].
  eapply c_subs_out_typesafe.
  eapply c_subs_out_typesafe. exact H.
  apply v_shift_typesafe.
  - apply shape_pair in pair. destruct pair. assumption. 
  - inv pair. inv H1. assumption.
  - apply shape_pair in pair. destruct pair. assumption.
+ unfold c_subs2_out. apply shape_summatch in orig.
  destruct orig as [A [B [vtyped [inl]]]].
  eapply c_subs_out_typesafe. exact inl.
  apply shape_sum_inl in vtyped. assumption.
+ unfold c_subs2_out. apply shape_summatch in orig.
  destruct orig as [A [B [vtyped [inl]]]].
  eapply c_subs_out_typesafe. exact H.
  apply shape_sum_inr in vtyped. assumption.
+ apply shape_app in orig. destruct orig as [A [f]].
  eapply c_subs_out_typesafe. exact f. assumption.
+ apply shape_letrec in orig. destruct orig as [A [C' [c1ty]]].
  eapply c_subs_out_typesafe. exact H.
  apply TypeV. inv c1ty.
  inv H. inv H3. assumption. inv H. inv H0. assumption.  
  apply TypeFun. apply TypeC. 
  - inv c1ty. inv H0. assumption.
  - inv c1ty. assumption.
  - eapply TypeLetRec. 2: exact c1ty.
    assert (CtxU (CtxU (CtxU Γ A) A) (TyFun A C') 
      = ctx_insert_var (CtxU (CtxU Γ A) (TyFun A C')) A 2)
    as insertion.
    { simpl. destruct Γ; auto. }
    rewrite insertion.
    apply c_insert_typesafe. assumption.
    inv H. inv H0. inv H5. assumption.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]].
  apply TypeC. inv c1ty. assumption. inv H. assumption.
  eapply TypeDoBind. 2: exact H. auto.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]].
  eapply c_subs_out_typesafe. exact H.
  apply shape_ret in c1ty. assumption.
+ destruct C as (A, Σ, E) eqn:e. apply shape_dobind in orig.
  destruct orig as [A' [c1ty]]. eapply shape_op in c1ty.
  destruct c1ty as [Aop [Bop [gets [vty]]]].
  apply TypeC.
  - inv H. inv H1. assumption.
  - inv H. assumption.
  - eapply TypeOp. exact gets. assumption.
    eapply TypeC. inv H0. assumption. inv H. assumption.
    eapply TypeDoBind. exact H0.
    assert (CtxU (CtxU Γ Bop) A' = ctx_insert_var (CtxU Γ A') Bop 1).
    { simpl. destruct Γ; auto. }
    rewrite H1. apply c_insert_typesafe. assumption.
    inv H0. inv H2. assumption.
+ eapply shape_handle in orig. destruct orig as [C' [hty]]. 
  apply TypeC. inv hty. assumption. inv hty. inv H1. assumption.
  eapply TypeHandle. exact hty.  apply IHstep. assumption.
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
  - eapply sig_subtype_gets_Some in gets; eauto.
    destruct gets as [A'[B'[gets']]]. inv H8.
    eapply ctx_subtype_ctype. eapply case_has_type; eauto.
    * apply WfCtxU. apply WfCtxU. 2: apply WfTyFun. all: auto.
    * apply SubtypeCtxU. apply SubtypeCtxU.
      apply ctx_subtype_refl; auto. apply SubtypeTyFun; auto.
      apply csubtype_refl. all: auto.
  - assert (CtxU Γ (TyFun Bop D') = ctx_insert_var Γ (TyFun Bop D') 0).
    { destruct Γ; simpl; reflexivity. }
    rewrite H8. eapply v_insert_typesafe. assumption.
    apply WfTyFun; assumption.
  - apply TypeV. assumption. apply WfTyFun; assumption.
    eapply TypeFun. apply TypeC. apply WfCtxU. all: try assumption.
    eapply TypeHandle. 2: exact H5.
    assert (CtxU Γ Bop = ctx_insert_var Γ Bop 0).
    { destruct Γ; simpl; reflexivity. }
    rewrite H8. eapply v_insert_typesafe. 2: assumption.
    apply TypeV. assumption. apply WfTyHandler. inv H0. assumption. assumption.
    eapply TypeVSubtype. instantiate (1:=(TyHandler (CTy A Σ' E) D'));
    inv H5; inv H10; inv H0.
    * apply TypeV. assumption. apply WfTyHandler. apply WfCTy; auto.
      inv hcty. assumption. eapply wf_eqs_sig_subtype; eauto.
      inv hcty. assumption. inv hcty. assumption.
      apply TypeHandler; auto.
    * apply SubtypeTyHandler. apply SubtypeCTy. 2: assumption.
      apply vsubtype_refl. inv H5. inv H10. assumption.
      eapply eqs_subtype_refl. inv H5. inv H10. eauto.
      apply csubtype_refl. assumption.
Qed.


Lemma progress c C:
  has_ctype CtxØ c C ->
  (exists v, c = Ret v) \/
  (exists o v y c', c = Op o v y c') \/
  (exists c', step c c'). 
Proof.
revert C. induction c; intros C orig.
+ left. exists v. reflexivity.
+ apply shape_absurd in orig. apply shape_empty in orig as shape. 
  destruct shape as [x [i]]. subst. apply shape_var_empty_ctx in orig.
  destruct orig.
+ rename v0 into x. rename v1 into y. right. right. clear IHc.
  eapply shape_prodmatch in orig. destruct orig as [A [B [vty]]].
  eapply shape_prod_full in vty as shape. 2: reflexivity.
  destruct shape.
  - destruct H0 as [name [db_i]]. rewrite H0 in *.
    apply shape_var_empty_ctx in vty. destruct vty.
  - destruct H0 as [v1[v2[same[ty1]]]]. subst.
    eexists. apply Step_ΠMatch.
+ right. right. rename v0 into x. rename v1 into y. clear IHc1 IHc2.
  eapply shape_summatch in orig. destruct orig as [A [B [vty]]].
  eapply shape_sum_full in vty as shape. 2: reflexivity.
  destruct shape. 2: destruct H0.
  - destruct H0 as [name [db_i]]. rewrite H0 in *.
    apply shape_var_empty_ctx in vty. destruct vty.
  - destruct H0 as [v' [same]]. rewrite same. eexists. apply Step_ΣMatch_Inl.
  - destruct H0 as [v' [same]]. rewrite same. eexists. apply Step_ΣMatch_Inr.
+ right. right.
  eapply shape_app_full in orig. 2: reflexivity.
  destruct orig as [A [fty]]. eapply shape_tyfun_full in fty as ffty.
  2: reflexivity. destruct ffty.
  - destruct H0 as [name [db_i]]. rewrite H0 in *.
    apply shape_var_empty_ctx in fty. destruct fty.
  - destruct H0 as [x [c [same]]]. subst. eexists. apply Step_App.
+ right. left. exists o. exists v. exists v0. exists c. reflexivity.
+ right. right. rename v into f. rename v0 into x. clear IHc1 IHc2.
  eexists. apply Step_LetRec.
+ right. right. rename v into x. clear IHc2. destruct C as (A, Σ, E). 
  eapply shape_dobind in orig. destruct orig as [A' [c1ty]].
  apply IHc1 in c1ty as IH. clear IHc1. destruct IH as [h1 | [h2 | h3]].
  - destruct h1. rewrite H0 in *. eexists. apply Step_DoBind_Ret.
  - destruct h2. destruct H0. destruct H0 as [y [c']]. rewrite H0 in *.
    eexists. apply Step_DoBind_Op.
  - destruct h3. eexists. apply Step_DoBind_step. exact H0.
+ right. right. eapply shape_handle in orig. rename C into D.
  destruct orig as [C [hty]]. apply IHc in H as H'. clear IHc.
  destruct C as (A, Σ, E). eapply shape_tyhandler_full in hty as shape.
  2: reflexivity. destruct shape.
  { destruct H0 as [x [i]]. subst.
    apply shape_var_empty_ctx in hty. contradiction. }
  destruct H0 as [x[c_r[h[Σ'[D'[same[crty]]]]]]]. subst.
  destruct H'. 2: destruct H1.
  - destruct H1 as [v]. subst. eexists. apply Step_Handle_Ret.   
  - destruct H1 as [op[v[y[c']]]]. subst. destruct H0 as [hcsty[r[sigsty]]].
    apply shape_op in H. destruct H as [A_op[B_op[gets]]].
    eapply sig_subtype_gets_Some in gets. 2: exact sigsty.
    destruct gets as [A'[B'[gets']]].
    eapply h_has_case in hcsty. 2: exact gets'.
    destruct hcsty as [x'[k'[c_op]]].
    eexists. eapply Step_Handle_Op. exact H2.    
  - destruct H1 as [c']. eexists. apply Step_Handle_Step. exact H1.
Qed.
