(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\examples". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\examples".

Require Export syntax_lemmas substitution_lemmas instantiation_lemmas 
  type_lemmas logic_tactics.


Lemma operational_in_logic Γ c c' C:
  has_ctype Γ c C -> step c c'-> judg Γ HypØ (Ceq C c c'). 
Proof.
intros tys steps.
assert (has_ctype Γ c' C) as tys' by (eapply preservation; eauto).
revert C tys tys'. induction steps; intros C' tys tys'; apply WfJudg.
all: apply WfCeq || apply WfHypØ || auto.
all: assumption || (inv tys; assumption) || auto.
+ eapply βMatchPair.
+ eapply βMatchLeft.
+ eapply βMatchRight.
+ eapply βMatchNil.
+ eapply βMatchCons.
+ eapply βApp.
+ eapply βLetRec.
+ destruct C' as [A Σ E]. eapply shape_do_full in tys.
  3: reflexivity. 2: reflexivity. destruct tys as [A' [ty1 ty2]].
  eapply CeqDo.
  - eapply IHsteps. eauto. eapply preservation; eauto.
  - apply ceq_refl. auto. 
    apply wf_hyp_shift_typesafe. apply WfHypØ.
    inv ty1. inv H0. auto.
+ eapply βDoRet.
+ eapply βDoOp. 
+ eapply shape_handle in tys. destruct tys as [C'' [tyh tyc]].
  eapply CeqHandle. 
  - apply veq_refl. eauto. apply WfHypØ.
  - apply IHsteps. assumption. eapply preservation; eauto.
+ eapply βHandleRet.
+ eapply βHandleOp. eauto.
Qed.

(* ==================== Substitution is Safe in Logic ==================== *)

Fixpoint veq_subs_logicsafe_weak
  Γ Γ' Ψ A v (orig: has_vtype Γ' v A) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Veq A (v_subs v i v_s) (v_subs v i v_s'))

with ceq_subs_logicsafe_weak
  Γ Γ' Ψ C c (orig: has_ctype Γ' c C) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Ceq C (c_subs c i v_s) (c_subs c i v_s'))

with heq_subs_logicsafe_weak
  Γ Γ' Ψ Σ D h (orig: has_htype Γ' h Σ D) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Heq Σ D (h_subs h i v_s) (h_subs h i v_s')).

Proof.
all: rename veq_subs_logicsafe_weak into VEQ.
all: rename ceq_subs_logicsafe_weak into CEQ.
all: rename heq_subs_logicsafe_weak into HEQ.
all: intros vseq ctxs clen.
all: assert (forall A, wf_vtype A -> 
      judg (CtxU Γ A) (hyp_shift Ψ 1 0) 
        (Veq A_s (v_shift v_s 1 0) (v_shift v_s' 1 0)) ) as vseq_ext by
  (intros; eapply judg_shift_typesafe in vseq; simpl in vseq; eauto).
{
apply WfJudg. inv vseq. auto. apply WfVeq.
{ inv vseq. inv H0. eapply v_subs_typesafe; eauto. }
{ inv vseq. inv H0. eapply v_subs_typesafe; eauto. }
{ inv vseq. auto. }
destruct orig. destruct H1.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqInt.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. 
  destruct (n=?i) eqn: ni; simpl.
  - rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    apply Nat.eqb_eq in ni. subst. rewrite get_ctx_insert_new in H1. inv H1. 
    inv vseq. assumption. all: omega || assumption.
  - assert (judg Γ Ψ (Veq A 
      (if i <=? n then Var (n-1) else Var n)
      (if i <=? n then Var (n-1) else Var n))).
    apply veq_refl. apply TypeV; auto.
    { inv vseq. assumption. }
    destruct (i<=?n) eqn: cmp.
    * apply TypeVar. subst. erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * apply TypeVar. subst. erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. assumption.
    * inv vseq. auto.
    * inv H2. assumption.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqPair; eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. eapply VeqLeft. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. eapply VeqRight. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqNil.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqCons; eapply VEQ; eauto.
+ clear VEQ HEQ. unfold v_subs. unfold c_subs in CEQ. simpl. 
  apply VeqFun. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext.
  inv H0. auto. subst. apply ctx_insert_extend. simpl. all: aomega.
+ clear VEQ. unfold v_subs. unfold c_subs in CEQ. unfold h_subs in HEQ. simpl.
  eapply VeqHandler.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_ext. inv H0. inv H6. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
  - eapply HEQ; eauto.
+ eapply VeqSubsume; eauto.
}{
assert (forall A B, wf_vtype A -> wf_vtype B -> 
judg (CtxU (CtxU Γ B) A) (hyp_shift Ψ 2 0) 
  (Veq A_s (v_shift v_s 2 0) (v_shift v_s' 2 0)) ) as vseq_extext.
{ intros. eapply judg_shift_typesafe in vseq. 
  eapply judg_shift_typesafe in vseq. 
  rewrite hyp_shift_shift, form_shift_shift in vseq. simpl in vseq.
  eauto. all: eauto. } 
apply WfJudg. inv vseq. auto. apply WfCeq.
{ inv vseq. inv H0. eapply c_subs_typesafe; eauto. }
{ inv vseq. inv H0. eapply c_subs_typesafe; eauto. }
{ inv vseq. auto. }
destruct orig. destruct H1.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqRet. eauto.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqAbsurd. all: apply csubtype_refl; auto.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqProdMatch. eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply vseq_extext.
  inv H1. inv H4. assumption. inv H1. inv H4. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqSumMatch. eauto.
  all: rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext. inv H1. inv H5.
  assumption. subst. apply ctx_insert_extend. simpl.
  all: try omega. 
  eapply CEQ; eauto. apply vseq_ext. inv H1. inv H5.
  assumption. subst. apply ctx_insert_extend. simpl. omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqListMatch; eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply vseq_extext. inv H1. assumption. inv H1. inv H5. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ VEQ. unfold c_subs in *. simpl.
  eapply CeqDo. eauto. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext.
  inv H1. inv H4. assumption. subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs. unfold v_subs in *. simpl. eapply CeqApp; eauto.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl.
  eapply CeqHandle; eauto.
+ clear VEQ HEQ. unfold c_subs in *. simpl. eapply CeqLetRec.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_extext.
    inv H1. inv H3. eauto. inv H1. inv H3. inv H8. eauto.
    subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
    simpl. all: omega.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_ext. inv H2. inv H3. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl. 
  eapply CeqOp; eauto.
  - clear CEQ. eapply VEQ in vseq as IH. all: clear VEQ. 2: eauto. all: eauto.
    apply WfJudg; try (inv vseq; assumption).
    * apply get_op_type_wf in H1. 2: inv H0; auto. destruct H1.
      apply WfVeq; eapply v_subs_typesafe; eauto; inv vseq; inv H8; auto.
      all: apply TypeV; auto; eapply TypeVSubsume; eauto.
    * eapply VeqSubsume; eauto.
  - clear vseq_extext VEQ. specialize (vseq_ext Bop).
    eapply CEQ in vseq_ext as IH. all: clear CEQ. 2: eauto.
    3: instantiate (1:= S i).
    * rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
      inv vseq. eapply ctx_subtype_judg; eauto.
      all: apply WfCtxU || apply STyCtxU || omega; auto.
      apply get_op_type_wf in H1. 2: inv H0; auto. destruct H1. auto.
      apply ctx_subtype_refl. auto.
    * inv H5. inv H6. auto.
    * subst. simpl. auto.
    * simpl. omega.
+ eapply CeqSubsume; eauto.
}{
apply WfJudg. inv vseq. auto. eapply WfHeq.
{ inv orig. auto. }
{ apply sig_subtype_refl. inv orig. auto. }
{ apply sig_subtype_refl. inv orig. auto. }
{ inv vseq. inv H0. eapply h_subs_typesafe; eauto. }
{ inv vseq. inv H0. eapply h_subs_typesafe; eauto. }
{ inv vseq. auto. }
destruct orig. destruct H2.
+ clear VEQ CEQ HEQ. 
  unfold h_subs; simpl. apply HeqSigØ.
+ unfold h_subs in *. unfold c_subs in *. simpl in *.
  eapply HEQ in H2 as IHh; eauto. eapply CEQ in H3 as IHc.
  all: clear VEQ CEQ HEQ.
  4: instantiate (2:=CtxU (CtxU Γ A) (TyFun B D)).
  Focus 3.
    erewrite <-ctx_insert_extend. f_equal. erewrite <-ctx_insert_extend.
    f_equal. eauto.
  Focus 2.
    eapply judg_shift_typesafe in vseq. eapply judg_shift_typesafe in vseq.
    simpl in vseq. eauto. apply WfTyFun. all: inv H0; auto.
  apply HeqExtend; eauto.
  - apply negshift_get_case_None. apply sub_get_case_None. auto.
    inv H0. eapply wf_sig_unique_cases; eauto.
  - apply negshift_get_case_None. apply sub_get_case_None. auto.
    inv H0. eapply wf_sig_unique_cases; eauto.
  - rewrite v_shift_comm, (v_shift_comm 1 i).
    rewrite v_shift_shift, v_shift_shift, hyp_shift_shift in IHc.
    simpl in *. all: eaomega.
  - simpl. omega.
}
Qed.


(* ==================== Sanity Check for Induction ==================== *)

Lemma induction_check_base Γ A Σ E φ:
  wf_ctype (CTy A Σ E) -> wf_ctx Γ ->
  wf_form (CtxU Γ (TyFun TyUnit (CTy A Σ E))) φ ->
  wf_form (CtxU Γ A) (form_subs (form_shift φ 1 0) 1 (Fun TyUnit (Ret (Var 1)))).
Proof.
intros wfc wfg orig. eapply wf_form_subs_typesafe; eauto; simpl.
instantiate (1:=(TyFun TyUnit (CTy A Σ E))).
+ apply wf_form_shift_typesafe.
  assert (forall B, ctx_insert Γ 0 B = CtxU Γ B) as same.
  { intros. destruct Γ; simpl; auto. }
  rewrite same. auto. inv wfc. auto.
+ inv wfc. vtype_step. ctype_step. eapply TypeCSubsume.
  instantiate (1:= CTy A SigØ EqsØ). ctype_step.
  obvious_vtype. apply STyCTy. apply vsubtype_refl. auto.
  apply STySigØ. apply STyEqsØ.
+ omega.
Qed.

Lemma induction_check_assumption Γ A Σ E φ op Aop Bop:
  wf_ctype (CTy A Σ E) -> wf_ctx Γ ->
  wf_form (CtxU Γ (TyFun TyUnit (CTy A Σ E))) φ ->
  get_op_type Σ op = Some (Aop, Bop) ->
  wf_form (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) 
    (Forall Bop (form_subs (form_shift φ 3 0) 3 (Fun TyUnit (App (Var 2) (Var 1))))).
Proof.
intros wfc wfg orig gets. inv wfc.
apply get_op_type_wf in gets as getss; auto. destruct getss.
apply WfForall. auto. eapply wf_form_subs_typesafe; eauto; simpl.
instantiate (1:=(TyFun TyUnit (CTy A Σ E))).
+ rewrite <-(form_shift_shift 1), <-(form_shift_shift 1).
   assert (forall B, ctx_insert Γ 0 B = CtxU Γ B) as same.
  { intros. destruct Γ; simpl; auto. }
  rewrite same. apply wf_form_shift_typesafe.
  apply wf_form_shift_typesafe. apply wf_form_shift_typesafe.
  all: obvious.
+ vtype_step. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
+ omega.
Qed.


Lemma induction_check_step Γ A Σ E φ op Aop Bop:
  wf_ctype (CTy A Σ E) -> wf_ctx Γ ->
  wf_form (CtxU Γ (TyFun TyUnit (CTy A Σ E))) φ ->
  get_op_type Σ op = Some (Aop, Bop) ->
  wf_form (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) 
    (form_subs (form_shift φ 2 0) 2 
      (Fun TyUnit (Op op Aop Bop (Var 2) (App (Var 2) (Var 0))))).
Proof.
intros wfc wfg orig gets. eapply wf_form_subs_typesafe; eauto; simpl.
instantiate (1:=(TyFun TyUnit (CTy A Σ E))).
+ apply get_op_type_wf in gets. destruct gets. inv wfc.
  rewrite <-(form_shift_shift 1). apply wf_form_shift_typesafe.
  apply wf_form_shift_typesafe.
  assert (forall B, ctx_insert Γ 0 B = CtxU Γ B) as same.
  { intros. destruct Γ; simpl; auto. }
  rewrite same. all: obvious. inv wfc. auto.
+ inv wfc. apply get_op_type_wf in gets as getss. destruct getss. 
  vtype_step. ctype_step. eapply TypeOp; eauto; try apply vsubtype_refl; auto.
  - vtype_step.
  - ctype_step. instantiate (1:=Bop). 2: obvious_vtype. vtype_step.
  - auto.
+ omega.
Qed.

    
Lemma induction_check_conclusion Γ A Σ E φ:
  wf_ctype (CTy A Σ E) -> wf_ctx Γ ->
  wf_form (CtxU Γ (TyFun TyUnit (CTy A Σ E))) φ ->
  wf_form Γ (Forall (TyFun TyUnit (CTy A Σ E)) φ).
Proof.
intros wfc wfg orig. apply WfForall. inv wfc. obvious. auto.
Qed.
