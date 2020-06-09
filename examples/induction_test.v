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

Require Export type_lemmas logic_lemmas logic_tactics.
Open Scope string_scope.

(* Helpful lemma *)
Lemma letbind_ctype A c1 c2 Γ D:
  has_ctype Γ c1 (CTy A SigØ EqsØ) -> has_ctype (CtxU Γ A) c2 D ->
  has_ctype Γ (Do c1 c2) D.
Proof.
intros tys1 tys2.
apply TypeC. inv tys1. auto. inv tys2. auto.
destruct D as [B Σ E]. eapply TypeDo; eauto.
apply TypeC. inv tys1. auto.
+ apply WfCTy. inv tys1. inv H0. auto.
  all: inv tys2; inv H0; auto.
+ eapply TypeCSubsume; eauto. apply STyCTy.
  apply vsubtype_refl. inv tys1. inv H0. auto.
  apply STySigØ. apply STyEqsØ.
Qed.


(* ========================================================================== *)


Example etabind_with_induction Γ Ψ C c:
  wf_ctype C -> wf_ctx Γ -> wf_hyp Γ Ψ -> has_ctype Γ c C ->
  judg Γ Ψ (Ceq C (Do c (Ret (Var 0))) c).
Proof.
intros wfc wfg wfh ctys. destruct C as [A Σ E]. inv wfc.
(* Translate arbitrary computation to arbitrary functions. *)
assert (
  judg Γ Ψ (Forall (TyFun TyUnit (CTy A Σ E))
    (Ceq (CTy A Σ E) 
      (Do (App (Var 0) Unit) (Ret (Var 0))) (App (Var 0) Unit)
  ))).
{ 
apply WfJudg; obvious.
{ apply WfForall; obvious. apply WfCeq.
  + ctype_step. instantiate (1:=A). obvious_ctype.
    apply dirty_ret; obvious_vtype.
  + obvious_ctype. }
apply CompInduction. 
(* START INDUCTION *)
+ apply AdmissCeq.

+ (* BASE CASE *)
  simpl. simpl_c_subs.
  assert (wf_hyp (CtxU Γ A) (hyp_shift Ψ 1 0)) as wfhyp.
  { apply wf_hyp_shift_typesafe; auto. }
  
  eapply ceq_trans. apply WfJudg; obvious. 2: eapply CeqDo.
  3: apply ceq_refl. 2: apply WfJudg; obvious. 3: eapply βApp. all: auto.
  2: instantiate (1:=A). all: simpl_c_subs. apply WfCeq. 3: apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
    vtype_step. apply dirty_ret; obvious_vtype. apply dirty_ret; obvious_vtype. }
  { ctype_step. instantiate (1:=A). apply dirty_ret; obvious_vtype.
    apply dirty_ret; obvious_vtype. }
  { ctype_step. 2:obvious_vtype. vtype_step. apply dirty_ret; auto. obvious_vtype. }
  { simpl_c_subs. apply dirty_ret; obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }
  { apply wf_hyp_shift_typesafe; auto. }

  eapply ceq_trans. apply WfJudg; obvious. 2:eapply βDoRet.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. instantiate (1:=A). all: apply dirty_ret; obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }

  eapply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2:eapply βApp.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. vtype_step. apply dirty_ret; obvious_vtype. obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }

  eapply ceq_refl. apply dirty_ret; obvious_vtype. auto.

+ (* STEP CASE *)
  intros op Aop Bop gets.
  apply get_op_type_wf in gets as getss. destruct getss. 2: auto.
  simpl. simpl_c_subs.


  assert (
    wf_hyp (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
    (HypU (hyp_shift Ψ 2 0)
      (Forall Bop
        (Ceq (CTy A Σ E)
          (Do (App (Fun TyUnit (App (Var 2) (Var 1))) Unit) (Ret (Var 0)))
          (App (Fun TyUnit (App (Var 2) (Var 1))) Unit)))) ) 
  as wfhyp.
  { apply WfHypU.
    + rewrite <-(hyp_shift_shift 1). apply wf_hyp_shift_typesafe.
      apply wf_hyp_shift_typesafe. all: obvious.
    + apply WfForall. obvious. apply WfCeq.
      - ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
        vtype_step. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
        apply dirty_ret; obvious_vtype.
      - ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
        instantiate (1:=Bop). all:obvious_vtype. }
  
  eapply ceq_trans. apply WfJudg; obvious. 2: eapply CeqDo.
  3: apply ceq_refl. 2: apply WfJudg; obvious. 3: eapply βApp.
  2: instantiate (1:=A). all: simpl_c_subs. apply WfCeq. 3: apply WfCeq.

  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    ctype_step. 2: obvious_vtype. vtype_step. obvious_ctype. auto.
    ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    obvious_ctype. auto. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { ctype_step; obvious_vtype. obvious_ctype. auto. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { obvious_ctype. auto. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }
  { eapply wf_hyp_shift_typesafe in wfhyp. simpl in wfhyp. eauto. auto. }

  eapply ceq_trans. apply WfJudg; obvious. 2: eapply βDoOp.
  all: simpl. apply WfCeq.

  { ctype_step. instantiate (1:=A). obvious_ctype. auto. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. apply dirty_ret; obvious_vtype. }
  { obvious_ctype. auto. ctype_step. instantiate (1:=A). ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. apply dirty_ret; obvious_vtype. }

  apply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2: eapply βApp.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. 2: obvious_vtype. vtype_step. obvious_ctype. auto.
    ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { obvious_ctype. auto. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }

  apply WfJudg; obvious. 2: eapply CeqOp; eauto. 2: apply veq_refl.
  2: obvious_vtype. 2: obvious. apply WfCeq.

  { obvious_ctype. auto. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { obvious_ctype. auto. ctype_step. instantiate (1:=A). 
    ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    apply dirty_ret; obvious_vtype. }

  (* Extracting induction hypothesis *)
  assert (
    judg (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
      (HypU (hyp_shift Ψ 2 0)
        (Forall Bop
          (Ceq (CTy A Σ E)
            (Do (App (Fun TyUnit (App (Var 2) (Var 1))) Unit)
             (Ret (Var 0))) (App (Fun TyUnit (App (Var 2) (Var 1))) Unit))))
      (Forall Bop
        (Ceq (CTy A Σ E)
            (Do (App (Fun TyUnit (App (Var 2) (Var 1))) Unit)
              (Ret (Var 0))) (App (Fun TyUnit (App (Var 2) (Var 1))) Unit)))) 
  as IH.
  { apply WfJudg; obvious. apply WfForall; obvious. apply WfCeq.
    * ctype_step. instantiate (1:=A). ctype_step. 2:obvious_vtype. vtype_step.
      ctype_step. instantiate (1:=Bop). all: obvious_vtype.
      apply dirty_ret; obvious_vtype.
    * ctype_step. vtype_step. ctype_step. instantiate (1:=Bop).
      all: obvious_vtype.
    * apply IsHyp. simpl. left. auto. }
  
  (* IH cleanup *)
  assert (
    wf_hyp (CtxU (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) Bop)
      (HypU (hyp_shift (hyp_shift Ψ 2 0) 1 0)
        (Forall Bop
            (Ceq (CTy A Σ E)
              (Do (App (Fun TyUnit (App (Var 3) (Var 1))) Unit) (Ret (Var 0)))
              (App (Fun TyUnit (App (Var 3) (Var 1))) Unit)))) )
  as wfhyp2.
  { apply WfHypU. apply wf_hyp_shift_typesafe; auto. inv wfhyp. auto.
    inv wfhyp. eapply wf_form_shift_typesafe in H8. simpl in H8. exact H8. auto. }
  clear wfhyp.

  eapply judg_shift_typesafe in IH. 2: exact H0. eapply ForallEl in IH.
  2: instantiate (1:=(Var 0)); obvious_vtype. simpl in IH.
  unfold c_subs in IH. simpl in IH. simpl.

  eapply WfJudg in IH; obvious. eapply ceq_trans in IH. (* Continue here *)
  2: apply ceq_sym. 2: eapply WfJudg; obvious. 3: eapply CeqDo.
  4: apply ceq_refl. 3: eapply WfJudg; obvious. 4: eapply βApp.
  
  4: instantiate(1:=A). 4: apply dirty_ret; obvious_vtype. 4: auto.
  Focus 2.
    apply WfCeq. ctype_step. instantiate (1:=A). ctype_step. obvious_vtype.
    ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    apply dirty_ret; obvious_vtype. simpl_c_subs. ctype_step.
    instantiate (1:=A). ctype_step. instantiate (1:=Bop). 3: apply dirty_ret.
    all: obvious_vtype.
  Focus 2.
    simpl_c_subs. apply WfCeq. ctype_step; obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype.
  Focus 2.
    apply wf_hyp_shift_typesafe; auto.
  Focus 2.
    apply WfCeq; ctype_step. instantiate (1:=A). ctype_step; obvious_vtype.
    ctype_step. instantiate (1:=Bop). 3: apply dirty_ret. all: obvious_vtype.
    ctype_step. instantiate (1:=Bop). all: obvious_vtype.
  
  unfold c_subs_out in IH. unfold c_subs in IH. simpl in IH.
  eapply ceq_trans. 2: apply ceq_sym. 2: exact IH. clear IH. apply ceq_sym.
  eapply WfJudg; obvious. 2: apply βApp. apply WfCeq.

  { ctype_step; obvious_vtype. ctype_step. instantiate(1:=Bop).
    all: obvious_vtype. }
  { ctype_step. instantiate(1:=Bop). all: obvious_vtype. }

+ (* NONTERMINATION CASE *)
  simpl. simpl_c_subs. eapply ceq_sym. eapply ceq_trans.
  eapply WfJudg; auto. 2: eapply βApp. simpl_c_subs. apply WfCeq.

  { ctype_step; obvious_vtype. ctype_step; ctype_step; obvious_vtype. }
  { ctype_step; ctype_step; obvious_vtype. }
  
  simpl_c_subs. eapply ceq_trans. eapply ceq_sym. eapply WfJudg; auto.
  2: eapply DoLoop. instantiate (1:=(Ret (Var 0))). apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step; ctype_step; obvious_vtype.
    apply dirty_ret; obvious_vtype.  }
  { ctype_step; ctype_step; obvious_vtype. }

  eapply ceq_sym. eapply WfJudg; auto. 2: eapply CeqDo.
  2: instantiate (1:=A). apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step; obvious_vtype.
    ctype_step; ctype_step; obvious_vtype. apply dirty_ret; obvious_vtype.  }
  { ctype_step. instantiate (1:=A). ctype_step; ctype_step; obvious_vtype.
    apply dirty_ret; obvious_vtype.  }

  eapply WfJudg; auto. 2: eapply βApp. eapply WfCeq.

  { ctype_step; obvious_vtype. ctype_step; ctype_step; obvious_vtype. }
  { ctype_step; ctype_step; obvious_vtype. }
  
  apply ceq_refl; obvious.

  { apply dirty_ret; auto. obvious_vtype. }
  { apply wf_hyp_shift_typesafe; auto. }

}{
(* Now lets put induction to good use *)
eapply ForallEl in H.
Focus 2.
  instantiate (1:= (Fun TyUnit (c_shift c 1 0))).
  vtype_step. apply c_shift_typesafe; obvious.
simpl in H. unfold c_subs in H. simpl in H. 
rewrite c_negshift_shift, c_shift_0 in H. 2: omega.

eapply WfJudg in H; obvious. apply ceq_sym in H. eapply ceq_trans in H.
2: apply ceq_sym. 2: apply WfJudg; obvious. 3: apply βApp. 

Focus 2.
  apply WfCeq. obvious_ctype. apply c_shift_typesafe; obvious.
  simpl_c_subs. rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0.
  auto. omega. apply c_shift_makes_no_var.
Focus 2.
  apply WfCeq. ctype_step. instantiate (1:=A). obvious_ctype.
  apply c_shift_typesafe; obvious. apply dirty_ret; obvious_vtype.
  obvious_ctype. apply c_shift_typesafe; obvious.

unfold c_subs_out in H. unfold c_subs in H. simpl in H.
rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0 in H.
2: omega. 2: apply c_shift_makes_no_var.
apply ceq_sym. eapply ceq_trans. exact H. apply WfJudg; obvious.
2: eapply CeqDo. 2: instantiate(1:=A). apply WfCeq.

{ ctype_step. instantiate (1:=A). obvious_ctype. apply c_shift_typesafe; 
  obvious. apply dirty_ret; obvious_vtype. }
{ ctype_step. instantiate (1:=A). auto. apply dirty_ret; obvious_vtype. }
Focus 2.
  apply ceq_refl. apply dirty_ret; obvious_vtype.
  apply wf_hyp_shift_typesafe; auto.

assert (c_negshift (c_sub (c_shift c 1 0) (0, Unit)) 1 0 = c) as same.
{ rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0; aomega.
  apply c_shift_makes_no_var. }

clear H. eapply ceq_trans. apply WfJudg; obvious. 2: apply βApp.
all: simpl_c_subs; rewrite same. clear same. apply WfCeq; auto.
obvious_ctype. apply c_shift_typesafe; obvious.

apply ceq_refl; obvious.
}
Qed.
