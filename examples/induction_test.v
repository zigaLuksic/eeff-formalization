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


Lemma letbind_ctype A c1 c2 Γ D:
  has_ctype Γ c1 (CTy A SigØ EqsØ) -> has_ctype (CtxU Γ A) c2 D ->
  has_ctype Γ (DoBind c1 c2) D.
Proof.
intros tys1 tys2.
apply TypeC. inv tys1. auto. inv tys2. auto.
destruct D as [B Σ E]. eapply TypeDoBind; eauto.
apply TypeC. inv tys1. auto.
+ apply WfCTy. inv tys1. inv H0. auto.
  all: inv tys2; inv H0; auto.
+ eapply TypeCSubtype; eauto. apply SubtypeCTy.
  apply vsubtype_refl. inv tys1. inv H0. auto.
  apply SubtypeSigØ. apply SubtypeEqsØ.
Qed.


(* ========================================================================== *)


Example etabind_with_induction Γ Ψ C c:
  wf_ctype C -> wf_ctx Γ -> wf_hyp Γ Ψ -> has_ctype Γ c C ->
  judg Γ Ψ (Ceq C (DoBind c (Ret (Var 0))) c).
Proof.
intros wfc wfg wfh ctys. destruct C as [A Σ E]. inv wfc.
(* Translate arbitrary computation to arbitrary functions. *)
assert (
  judg Γ Ψ (Forall (TyFun TyUnit (CTy A Σ E))
    (Ceq (CTy A Σ E) 
      (DoBind (App (Var 0) Unit) (Ret (Var 0))) (App (Var 0) Unit)
  ))).
{ (* The showcase of induction. *)
apply WfJudg; auto.
{ apply WfForall; obvious. apply WfCeq.
  + ctype_step. instantiate (1:=A). obvious_ctype.
    apply dirty_ret; obvious_vtype.
  + obvious_ctype. }
apply CompInduction.
+ apply WfCeq. ctype_step. instantiate (1:=A). obvious_ctype.
  apply dirty_ret; obvious_vtype. obvious_ctype.
+ (* Base Case *)
  simpl. simpl_c_subs.
  assert (wf_hyp (CtxU Γ A) (hyp_shift Ψ 1 0)) as wfhyp.
  { apply wf_hyp_shift_typesafe; auto. }
  
  eapply ceq_trans. apply WfJudg; obvious. 2: eapply CeqDoBind.
  3: apply ceq_refl. 2: apply WfJudg. 4: eapply βApp. all: auto.
  apply WfCeq. 3: apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
    vtype_step. apply dirty_ret; obvious_vtype.
    apply dirty_ret; obvious_vtype. }
  { simpl_c_subs. ctype_step. instantiate (1:=A).
    apply dirty_ret; obvious_vtype. apply dirty_ret; obvious_vtype. }
  { instantiate (1:=A). ctype_step. 2:obvious_vtype.
    vtype_step. apply dirty_ret; obvious_vtype. }
  { simpl_c_subs. apply dirty_ret; obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }
  { apply wf_hyp_shift_typesafe; auto. }

  simpl_c_subs. eapply ceq_trans. apply WfJudg; auto. 2:eapply βDoBind_Ret.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. instantiate (1:=A). all: apply dirty_ret; obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }

  eapply ceq_sym. eapply ceq_trans. apply WfJudg; auto. 2:eapply βApp.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. vtype_step. apply dirty_ret; obvious_vtype. obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }

  eapply ceq_refl. apply dirty_ret; obvious_vtype. auto.

+ (* Step Case *)
  intros op Aop Bop gets.
  apply get_op_type_wf in gets as getss. destruct getss. 2: auto.
  simpl. simpl_c_subs.

  assert (
    wf_hyp (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
    (HypU (hyp_shift Ψ 2 0)
     (Forall Bop (Ceq (CTy A Σ E)
      (DoBind (App (Fun (App (Var 2) (Var 1))) Unit) (Ret (Var 0)))
      (App (Fun (App (Var 2) (Var 1))) Unit)))) ) as wfhyp.
  { apply WfHypU.
    + rewrite <-(hyp_shift_shift 1). apply wf_hyp_shift_typesafe.
      apply wf_hyp_shift_typesafe. all: obvious.
    + apply WfForall. obvious. apply WfCeq.
      - ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
        vtype_step. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
        apply dirty_ret; obvious_vtype.
      - ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
        instantiate (1:=Bop). all:obvious_vtype. }
  
  eapply ceq_trans. apply WfJudg; obvious. 2: eapply CeqDoBind.
  3: apply ceq_refl. 2: apply WfJudg. 4: eapply βApp. all: auto.
  apply WfCeq. 3: apply WfCeq. all: simpl_c_subs.

  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
    eapply TypeOp; eauto. obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    ctype_step. eapply TypeOp; eauto. obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { instantiate (1:=A). ctype_step. 2: obvious_vtype. vtype_step.
    ctype_step. eapply TypeOp; eauto. obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { ctype_step. eapply TypeOp; eauto. obvious_vtype. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { apply dirty_ret; obvious_vtype. }
  { eapply wf_hyp_shift_typesafe in wfhyp. simpl in wfhyp. eauto. auto. }

  eapply ceq_trans. apply WfJudg; obvious. 2: eapply βDoBind_Op.
  all: simpl. apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step. eapply TypeOp; eauto.
    obvious_vtype. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    apply dirty_ret; obvious_vtype. }
  { ctype_step. eapply TypeOp; eauto. obvious_vtype. ctype_step.
    instantiate (1:=A). ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    apply dirty_ret; obvious_vtype. }

  apply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2: eapply βApp.
  all: simpl_c_subs. apply WfCeq.

  { ctype_step. 2: obvious_vtype. vtype_step. ctype_step. eapply TypeOp; eauto.
    obvious_vtype. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { ctype_step. eapply TypeOp; eauto.
    obvious_vtype. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }

  apply ceq_sym. apply WfJudg; obvious. 2: eapply CeqOp; eauto.
  2: apply veq_refl. apply WfCeq. 4: auto.

  { ctype_step. eapply TypeOp; eauto. obvious_vtype.
    ctype_step. instantiate (1:=A). ctype_step. instantiate (1:=Bop).
    all: obvious_vtype. apply dirty_ret; obvious_vtype. }
  { ctype_step. eapply TypeOp; eauto.
    obvious_vtype. ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  { obvious_vtype. }

  assert (
    judg (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
      (HypU (hyp_shift Ψ 2 0)
        (Forall Bop
          (Ceq (CTy A Σ E)
            (DoBind (App (Fun (App (Var 2) (Var 1))) Unit)
             (Ret (Var 0))) (App (Fun (App (Var 2) (Var 1))) Unit))))
      (Forall Bop
        (Ceq (CTy A Σ E)
            (DoBind (App (Fun (App (Var 2) (Var 1))) Unit)
              (Ret (Var 0))) (App (Fun (App (Var 2) (Var 1))) Unit)))) as IH.
  { apply WfJudg; auto.
    apply WfForall; obvious. apply WfCeq. ctype_step. instantiate (1:=A).
    ctype_step. 2:obvious_vtype. vtype_step. ctype_step. instantiate (1:=Bop).
    all: obvious_vtype. apply dirty_ret; obvious_vtype.
    ctype_step. vtype_step. ctype_step. instantiate (1:=Bop).
    all: obvious_vtype.
    apply IsHyp. simpl. left. auto. }
  
  eapply judg_shift_typesafe in IH. 2: exact H0. eapply ForallEl in IH.
  2: instantiate (1:=(Var 0)); obvious_vtype. simpl in IH.
  unfold c_subs in IH. simpl in IH. simpl.

  assert (forall Ψ', 
    wf_hyp (CtxU (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) Bop) Ψ' ->
    judg (CtxU (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) Bop) Ψ'
       (Ceq (CTy A Σ E)
          (DoBind (App (Fun (App (Var 2) (Var 1))) Unit) (Ret (Var 0)))
          (DoBind (App (Var 1) (Var 0)) (Ret (Var 0))))) as IH1.
  { clear wfhyp IH. intros Ψ' wfh'.
    apply WfJudg; auto. apply WfCeq.
    3: eapply CeqDoBind. 3: instantiate (1:=A). 4: apply ceq_refl.
    3: eapply ceq_trans. 3: eapply WfJudg; auto. 4: apply βApp.
    + ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
      vtype_step. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
      apply dirty_ret; obvious_vtype.
    + ctype_step. instantiate (1:=A). ctype_step. instantiate (1:=Bop).
      all: obvious_vtype. apply dirty_ret; obvious_vtype.
    + simpl_c_subs. apply WfCeq. ctype_step. 2:obvious_vtype.
      vtype_step. ctype_step. instantiate (1:=Bop). all: obvious_vtype.
      ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    + simpl_c_subs. apply ceq_refl; auto. ctype_step.
      instantiate (1:=Bop). all: obvious_vtype.
    + apply dirty_ret; obvious_vtype.
    + eapply wf_hyp_shift_typesafe in wfh'; eauto. }

  eapply ceq_sym in IH1. 
  2: eapply wf_hyp_shift_typesafe in wfhyp; eauto.
  eapply ceq_trans. eauto. clear IH1.
  
  assert (forall Ψ', 
    wf_hyp (CtxU (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) Bop) Ψ' ->
    judg (CtxU (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) Bop) Ψ'
       (Ceq (CTy A Σ E)
          (App (Fun (App (Var 2) (Var 1))) Unit)
          (App (Var 1) (Var 0)))) as IH1.
  { clear wfhyp IH. intros Ψ' wfh'. eapply ceq_trans. apply WfJudg; auto.
    2: apply βApp. all: simpl_c_subs. apply WfCeq.
    3: apply ceq_refl; auto.
    + ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
      instantiate (1:=Bop). all: obvious_vtype.
    + ctype_step. instantiate (1:=Bop). all: obvious_vtype.
    + ctype_step. instantiate (1:=Bop). all: obvious_vtype. }
  
  eapply ceq_sym. eapply ceq_sym in IH1.
  2: eapply wf_hyp_shift_typesafe in wfhyp; eauto.
  eapply ceq_trans. eauto. clear IH1. apply ceq_sym.
  eapply WfJudg; auto. eapply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step. 2: obvious_vtype.
    vtype_step. ctype_step. instantiate (1:=Bop). 2: obvious_vtype.
    all: obvious_vtype. apply dirty_ret; obvious_vtype. }
  { ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
    instantiate (1:=Bop). all: obvious_vtype. }
  { eapply wf_hyp_shift_typesafe in wfhyp; eauto. }

+ (* Nontermination case *)
  simpl. simpl_c_subs. eapply ceq_sym. eapply ceq_trans.
  eapply WfJudg; auto. 2: eapply βApp. simpl_c_subs. apply WfCeq.

  { ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
    instantiate (1:=(CTy A Σ E)). instantiate (2:=TyUnit). 
    obvious_ctype. obvious_ctype. }
  { ctype_step. instantiate (1:=(CTy A Σ E)). instantiate (2:=TyUnit). 
    obvious_ctype. obvious_ctype. }
  
  simpl_c_subs. eapply ceq_trans. eapply ceq_sym. eapply WfJudg; auto.
  2: eapply DoLoop. instantiate (1:=(Ret (Var 0))). apply WfCeq.

  { ctype_step. instantiate (1:=A). ctype_step. instantiate (1:=(CTy A Σ E)).
    instantiate (1:=TyUnit). obvious_ctype. obvious_ctype.
    apply dirty_ret; obvious. obvious_vtype.  }
  { ctype_step. instantiate (1:=(CTy A Σ E)). instantiate (1:=TyUnit).
    obvious_ctype. obvious_ctype. }

  eapply ceq_sym. eapply WfJudg; auto. 2: eapply CeqDoBind.
  2: instantiate (1:=A). apply WfCeq.

  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    ctype_step. 2: obvious_vtype. vtype_step. ctype_step.
    instantiate (1:=(CTy A Σ E)). instantiate (1:=TyUnit).
    obvious_ctype. obvious_ctype.  }
  { ctype_step. instantiate (1:=A). 2: apply dirty_ret; obvious_vtype.
    ctype_step. instantiate (1:=(CTy A Σ E)). instantiate (1:=TyUnit).
    obvious_ctype. obvious_ctype.  }

  eapply ceq_trans. eapply WfJudg; auto. 2: eapply βApp. eapply WfCeq.

  { ctype_step. instantiate (1:=TyUnit). 2: obvious_vtype.
    ctype_step. vtype_step. ctype_step.
    instantiate (1:=(CTy A Σ E)). instantiate (1:=TyUnit).
    obvious_ctype. obvious_ctype.  }
  { simpl_c_subs. ctype_step. instantiate (1:=(CTy A Σ E)). 
    instantiate (1:=TyUnit). obvious_ctype. obvious_ctype.  }
  
  simpl_c_subs. apply ceq_refl; auto. 2: apply ceq_refl.

  { ctype_step. instantiate (1:=(CTy A Σ E)). instantiate (1:=TyUnit). 
    obvious_ctype. obvious_ctype.  }
  { apply dirty_ret; auto. obvious_vtype. }
  { apply wf_hyp_shift_typesafe; auto. }

}{
(* Now lets put induction to good use *)
eapply ForallEl in H.
Focus 2.
  instantiate (1:= (Fun (c_shift c 1 0))).
  vtype_step. apply c_shift_typesafe; obvious.
simpl in H. unfold c_subs in H. simpl in H. 
rewrite c_negshift_shift, c_shift_0 in H. 2: omega.

assert (
  judg Γ Ψ
      (Ceq (CTy A Σ E)
         (DoBind (App (Fun (c_shift c 1 0)) Unit) (Ret (Var 0)))
         (App (Fun (c_shift c 1 0)) Unit)) ) as IH.
{ apply WfJudg; auto. apply WfCeq. ctype_step. instantiate (1:=A).
  obvious_ctype. apply TypeFun. apply c_shift_typesafe; obvious.
  apply dirty_ret; obvious_vtype. obvious_ctype. apply TypeFun.
  apply c_shift_typesafe; obvious. }

assert (
  judg Γ Ψ
    (Ceq (CTy A Σ E)
      (DoBind (App (Fun (c_shift c 1 0)) Unit) (Ret (Var 0)))
      (DoBind c (Ret (Var 0))) )) as IH1.
{ eapply ceq_trans. apply WfJudg; auto. 2: eapply CeqDoBind.
  3: apply ceq_refl. 2: instantiate (2:=A). 2: apply WfJudg; auto.
  3: apply βApp. apply WfCeq. 3: apply WfCeq. 
  + ctype_step. instantiate (1:=A). obvious_ctype. apply TypeFun.
    apply c_shift_typesafe; obvious. apply dirty_ret; obvious_vtype.
  + ctype_step. eapply c_subs_typesafe. apply c_shift_typesafe. eauto.
    2: obvious_vtype. 3: omega. obvious. destruct Γ; simpl; auto.
    apply dirty_ret; obvious_vtype.
  + ctype_step. vtype_step. apply c_shift_typesafe. all: obvious_vtype.
  + eapply c_subs_typesafe. apply c_shift_typesafe. eauto.
    2: obvious_vtype. 3: omega. obvious. destruct Γ; simpl; auto.
  + apply dirty_ret; obvious_vtype.
  + apply wf_hyp_shift_typesafe; auto.
  + simpl_c_subs. rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0.
    apply ceq_refl. ctype_step. eauto. apply dirty_ret; obvious_vtype.
    all: aomega. apply c_shift_makes_no_var. }

assert (
  judg Γ Ψ (Ceq (CTy A Σ E) (App (Fun (c_shift c 1 0)) Unit) c) ) as IH2.
{ eapply ceq_trans. apply WfJudg; auto. 2: eapply βApp.
  all: simpl_c_subs; rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0.
  2: omega. 4:omega. all: try apply c_shift_makes_no_var.
  apply WfCeq. 3: apply ceq_refl. all: auto.
  obvious_ctype. apply TypeFun. apply c_shift_typesafe; obvious. }

eapply ceq_trans. apply ceq_sym. eauto.
apply ceq_sym. eapply ceq_trans. apply ceq_sym. eauto.
apply ceq_sym. auto.
}
Qed.
