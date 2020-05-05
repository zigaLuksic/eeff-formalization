(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".

Require Export type_lemmas subtyping_lemmas.


Ltac simpl_c_subs := 
unfold c_subs2_out; unfold c_subs_out; unfold c_subs; simpl.

Ltac obvious := 
   apply WfCtxØ || (apply WfCtxU; obvious) 
|| apply WfTCtxØ  || (apply WfTCtxU; obvious) 
|| apply WfEqsØ || apply WfSigØ || (apply WfSigU; obvious)
|| apply WfTyUnit || apply WfTyInt || apply WfTyEmpty
|| (apply WfTyHandler; obvious) || (apply WfTyFun; obvious) 
|| (apply WfTyList; obvious)|| (apply WfTySum; obvious)
|| (apply WfTyProd; obvious) || (apply WfCTy; obvious)
|| auto.

Ltac obvious_vtype := (
(apply TypeV; (
   (apply TypeUnit; obvious)
|| (apply TypeInt; obvious)
|| (apply TypeLeft; obvious_vtype)
|| (apply TypeRight; obvious_vtype)
|| (apply TypePair; obvious_vtype)
|| (apply TypeNil; obvious)
|| (apply TypeCons; obvious_vtype)
|| (apply TypeVar; simpl in *; obvious)
|| obvious)
)
|| obvious).

Ltac vtype_step := (
(apply TypeV; (
   (apply TypeUnit; obvious)
|| (apply TypeInt; obvious)
|| (apply TypeLeft; obvious)
|| (apply TypeRight; obvious)
|| (apply TypePair; obvious)
|| (apply TypeNil; obvious)
|| (apply TypeCons; obvious)
|| (apply TypeFun; obvious)
|| (apply TypeHandler; obvious)
|| (apply TypeVar; simpl in *; obvious)
|| obvious)
)
|| obvious).


Ltac obvious_ctype := (
(apply TypeC; (
  (apply TypeRet; obvious_vtype)
|| (eapply TypeApp; obvious_vtype)
|| (eapply TypeSumMatch; obvious_vtype; obvious_ctype)
|| (eapply TypeProdMatch; obvious_vtype; obvious_ctype)
|| (eapply TypeListMatch; obvious_vtype; obvious_ctype)
|| obvious)
)
|| obvious).

Ltac ctype_step := (
(apply TypeC; (
  (apply TypeRet; obvious)
|| (eapply TypeApp; obvious)
|| (eapply TypeSumMatch; obvious)
|| (eapply TypeProdMatch; obvious)
|| (eapply TypeListMatch; obvious)
|| (eapply TypeDo; obvious)
|| (eapply TypeLetRec; obvious)
|| obvious)
)
|| obvious).

Ltac wft_step := (
   (eapply WfTApp; obvious)
|| (eapply WfTSumMatch; obvious)
|| (eapply WfTProdMatch; obvious)
|| (eapply WfTListMatch; obvious)
|| (eapply WfTDo; obvious)
|| (eapply WfTOp; obvious)
|| obvious).



Lemma dirty_ret Γ A Σ E v:
  wf_sig Σ -> wf_eqs E Σ -> has_vtype Γ v A ->
  has_ctype Γ (Ret v) (CTy A Σ E).
Proof.
intros wfs wfe vty. apply TypeC. inv vty. auto. obvious. inv vty. auto.
eapply TypeCSubsume. instantiate (1:= (CTy A SigØ EqsØ)).
obvious_ctype. all: inv vty; auto. apply STyCTy.
apply vsubtype_refl. auto. apply STySigØ. apply STyEqsØ.
Qed.



Lemma Op_ListMatch v v' c1 c2 c2' id vop vop' Γ Ψ A Σ E Al Aop Bop :
  (* We need to take care of the variables shifting around *)
  c2' = (c_subs2_out (c_shift c2 2 3) (Var 2) (Var 1)) ->
  v = v_shift v' 1 0 ->
  vop' = v_shift vop 2 0 ->
  wf_hyp Γ Ψ ->
  get_op_type Σ id = Some (Aop, Bop) ->
  has_vtype Γ v' (TyList Al) -> (* it does not use the argument of Op *)
  has_vtype Γ vop (Aop) ->
  has_ctype (CtxU Γ Bop) c1 (CTy A Σ E) ->
  has_ctype (CtxU(CtxU(CtxU Γ Bop) Al) (TyList Al)) c2 (CTy A Σ E) -> 
  (* Conclusion *)
  judg Γ Ψ (Ceq (CTy A Σ E) 
    (Op id vop (ListMatch v c1 c2)) 
    (ListMatch v' (Op id vop c1) (Op id vop' c2'))).
Proof.
intros shiftedc2 shiftedv shiftedvop wfhyp gets 
  vtypes voptypes c1types c2types.

assert (wf_vtype Bop) as wfbop.
{ apply get_op_type_wf in gets. destruct gets. auto. inv c1types.
  inv H0. auto. }
assert (wf_ctype (CTy A Σ E)) as wfc  by (inv c1types; auto).
assert (wf_ctx Γ) as wfctx by (inv vtypes; auto).
assert (wf_vtype Al) as wfal by (inv vtypes; inv H0; auto).

(* Check that requirements result in well typed terms *)
assert (has_ctype Γ (Op id vop (ListMatch v c1 c2)) (CTy A Σ E)).
{ subst. inv wfc. ctype_step. eapply TypeOp; eauto.
  ctype_step. apply v_shift_typesafe; eauto. eauto. }
  
assert (has_ctype Γ (ListMatch v' (Op id vop c1) (Op id vop' c2')) (CTy A Σ E)).
{ subst. inv wfc. ctype_step. eauto.
  + ctype_step. eapply TypeOp; eauto.
  + ctype_step. eapply TypeOp; eauto.
    - rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe.
      all: inv vtypes; auto.
    - eapply c_subs_typesafe. 3: reflexivity. instantiate (1:=Al). simpl.
      eapply c_subs_typesafe. 3: reflexivity. instantiate (1:=(TyList Al)).
      simpl. rewrite <-(c_shift_shift 1 1).
      assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
      = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
      { intros. destruct γ; simpl; auto. }
      rewrite <-same. apply c_insert_typesafe; obvious.
      rewrite <-same. apply c_insert_typesafe; obvious.
      obvious_vtype. simpl. omega. obvious_vtype. simpl. omega. }

(* Start actual proof *) 
subst.     
specialize (ηList Γ Ψ v' 0
  (Op id (v_shift vop 1 0) (ListMatch (Var 1) (c_shift c1 1 1) (c_shift c2 1 3)))
  (CTy A Σ E) Al
) as rule.

assert (
  (c_subs (Op id (v_shift vop 1 0)
                  (ListMatch (Var 1) (c_shift c1 1 1) (c_shift c2 1 3))) 0 v')
  = (Op id vop (ListMatch (v_shift v' 1 0) c1 c2))) as sameL.
{ clear rule. simpl_c_subs. f_equal. rewrite v_sub_no_var_same.
  rewrite v_negshift_shift, v_shift_0; aomega. apply v_shift_makes_no_var. 
  f_equal.
  + rewrite v_shift_comm, v_negshift_shift, v_shift_0; aomega.
  + rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0; aomega.
    apply c_shift_makes_no_var.
  + rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0; aomega.
    apply c_shift_makes_no_var. }

rewrite sameL in rule. clear sameL.

assert (
  (ListMatch v'
  (c_subs
     (Op id (v_shift vop 1 0)
        (ListMatch (Var 1) (c_shift c1 1 1) (c_shift c2 1 3))) 0
     Nil)
  (c_subs
     (c_shift
        (Op id (v_shift vop 1 0)
           (ListMatch (Var 1) (c_shift c1 1 1) (c_shift c2 1 3)))
        2 0) (2 + 0) (Cons (Var 1) (Var 0))))
  = (ListMatch v' (Op id vop (ListMatch Nil c1 c2))
      (Op id (v_shift vop 2 0) 
        (ListMatch (Cons (Var 2) (Var 1))
          (c_shift c1 2 1)
          (c_shift c2 2 3))))) as sameR.
{ clear rule. simpl_c_subs. f_equal.
  { f_equal. rewrite v_sub_no_var_same, v_negshift_shift, v_shift_0; aomega.
    apply v_shift_makes_no_var. f_equal.
    + rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0; aomega.
      apply c_shift_makes_no_var.
    + rewrite c_sub_no_var_same, c_negshift_shift, c_shift_0; aomega.
      apply c_shift_makes_no_var. }
  { f_equal.
    + rewrite v_shift_comm, v_sub_no_var_same.
      rewrite v_negshift_shift, v_shift_0; aomega.
      apply v_shift_makes_no_var. omega.
    + f_equal.
      rewrite c_shift_comm, c_sub_no_var_same.
      rewrite c_negshift_shift, c_shift_0; aomega.
      apply c_shift_makes_no_var. omega.

      rewrite (c_shift_comm 1 3), c_sub_no_var_same.
      rewrite c_negshift_shift, c_shift_0; aomega.
      apply c_shift_makes_no_var. omega. } }

rewrite sameR in rule. clear sameR.
apply WfJudg in rule; auto. 3: omega.

Focus 3.
  clear rule.
  assert (ctx_insert Γ 0 (TyList Al) = CtxU Γ (TyList Al)) as same.
  { destruct Γ; simpl; auto. } rewrite same. clear same.
  inv vtypes. inv H2. inv wfc. ctype_step. 
  eapply TypeOp; eauto. apply v_shift_typesafe; obvious.
  ctype_step. instantiate (1:=Al). obvious_vtype.
  assert (ctx_insert (CtxU Γ Bop) 1 (TyList Al) 
    = CtxU (CtxU Γ (TyList Al)) Bop) as same.
  { destruct Γ; simpl; auto. } rewrite <-same. clear same.
  apply c_insert_typesafe; obvious.
  assert (ctx_insert (CtxU (CtxU (CtxU Γ Bop) Al) (TyList Al)) 3 (TyList Al) 
    = CtxU (CtxU (CtxU (CtxU Γ (TyList Al)) Bop) Al) (TyList Al)) as same.
  { destruct Γ; simpl; auto. } rewrite <-same. clear same.
  apply c_insert_typesafe; obvious.

Focus 2.
  clear rule. inv wfc. apply WfCeq.
  { ctype_step. eapply TypeOp; eauto. ctype_step; eauto.
    apply v_shift_typesafe; obvious. }
  { ctype_step. eauto. ctype_step. eapply TypeOp; eauto.
    ctype_step. instantiate (1:=Al). vtype_step. auto.
    ctype_step. eapply TypeOp. eauto.
    rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe; obvious.
    ctype_step. instantiate (1:=Al). obvious_vtype. 
    { rewrite <-(c_shift_shift 1 1).
      assert (forall γ α, ctx_insert (CtxU γ Bop) 1 α 
      = CtxU (CtxU γ α) Bop) as same.
      { intros. destruct γ; simpl; auto. } 
      rewrite <-same. apply c_insert_typesafe; obvious.
      rewrite <-same. apply c_insert_typesafe; obvious. }
    { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
      = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
      { intros. destruct γ; simpl; auto. }
      rewrite <-(c_shift_shift 1 1). rewrite <-same.
      apply c_insert_typesafe; obvious. rewrite <-same.
      apply c_insert_typesafe; obvious. } }
Unfocus.

eapply ceq_trans. eauto. clear rule.
eapply WfJudg; obvious.

{ inv wfc. apply WfCeq.
  ctype_step. eauto. ctype_step. eapply TypeOp; eauto. ctype_step.
  instantiate (1:=Al). obvious_vtype. auto.
  ctype_step. eapply TypeOp; eauto. 
  rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe; obvious.
  ctype_step. instantiate (1:=Al). obvious_vtype.
  { rewrite <-(c_shift_shift 1 1).
    assert (forall γ α, ctx_insert (CtxU γ Bop) 1 α 
    = CtxU (CtxU γ α) Bop) as same.
    { intros. destruct γ; simpl; auto. } 
    rewrite <-same. apply c_insert_typesafe; obvious.
    rewrite <-same. apply c_insert_typesafe; obvious. }
  { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
    = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
    { intros. destruct γ; simpl; auto. }
    rewrite <-(c_shift_shift 1 1). rewrite <-same.
    apply c_insert_typesafe; obvious. rewrite <-same.
    apply c_insert_typesafe; obvious. } 
  
  ctype_step. eauto. ctype_step. eapply TypeOp; eauto.
  ctype_step. eapply TypeOp; eauto.
  rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe; obvious.
  unfold c_subs2_out. do 2 try eapply c_subs_out_typesafe.
  instantiate (2:=Al). instantiate (1:=(TyList Al)).
  2: obvious_vtype. 2: simpl; obvious_vtype.
  { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
    = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
    { intros. destruct γ; simpl; auto. }
    rewrite <-(c_shift_shift 1 1). rewrite <-same.
    apply c_insert_typesafe; obvious. rewrite <-same.
    apply c_insert_typesafe; obvious. } }

eapply CeqListMatch. instantiate (1:=Al).

+ apply veq_refl; obvious.

+ apply WfJudg; obvious.

  { inv wfc. apply WfCeq; ctype_step; eapply TypeOp; eauto.
    ctype_step. instantiate (1:=Al). obvious_vtype. auto. }

  eapply CeqOp. eauto. apply veq_refl; obvious.
  apply WfJudg; obvious. 2: apply wf_hyp_shift_typesafe; obvious.

  { inv wfc. apply WfCeq. 2: obvious. ctype_step.
    instantiate (1:=Al). obvious_vtype. auto. }

  apply βMatchNil.

+ assert (wf_hyp (CtxU (CtxU Γ Al) (TyList Al)) (hyp_shift Ψ 2 0)).
  { rewrite <-(hyp_shift_shift 1). do 2 try apply wf_hyp_shift_typesafe; obvious. }
  apply WfJudg; obvious.

  { inv wfc. apply WfCeq; ctype_step; eapply TypeOp; eauto.
    rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe; obvious.
    2: rewrite <-(v_shift_shift 1). 2: do 2 try apply v_shift_typesafe; obvious.
    ctype_step. instantiate (1:=Al). obvious_vtype.
    { rewrite <-(c_shift_shift 1 1).
      assert (forall γ α, ctx_insert (CtxU γ Bop) 1 α 
      = CtxU (CtxU γ α) Bop) as same.
      { intros. destruct γ; simpl; auto. } 
      rewrite <-same. apply c_insert_typesafe; obvious.
      rewrite <-same. apply c_insert_typesafe; obvious. }
    { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
      = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
      { intros. destruct γ; simpl; auto. }
      rewrite <-(c_shift_shift 1 1). rewrite <-same.
      apply c_insert_typesafe; obvious. rewrite <-same.
      apply c_insert_typesafe; obvious. } 
    { unfold c_subs2_out. do 2 try eapply c_subs_out_typesafe.
      instantiate (2:=Al). instantiate (1:=(TyList Al)).
      2: obvious_vtype. 2: simpl; obvious_vtype.
      { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
        = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
        { intros. destruct γ; simpl; auto. }
        rewrite <-(c_shift_shift 1 1). rewrite <-same.
        apply c_insert_typesafe; obvious. rewrite <-same.
        apply c_insert_typesafe; obvious. } } }

  eapply CeqOp. eauto. apply veq_refl; obvious.
  { rewrite <-(v_shift_shift 1). do 2 try apply v_shift_typesafe; obvious. }

  eapply ceq_trans. apply WfJudg; obvious. 2: apply wf_hyp_shift_typesafe; obvious.
  2: apply βMatchCons.

  { inv wfc. apply WfCeq.
    ctype_step. instantiate (1:=Al). obvious_vtype.
    { rewrite <-(c_shift_shift 1 1).
      assert (forall γ α, ctx_insert (CtxU γ Bop) 1 α 
      = CtxU (CtxU γ α) Bop) as same.
      { intros. destruct γ; simpl; auto. } 
      rewrite <-same. apply c_insert_typesafe; obvious.
      rewrite <-same. apply c_insert_typesafe; obvious. }
    { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
      = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
      { intros. destruct γ; simpl; auto. }
      rewrite <-(c_shift_shift 1 1). rewrite <-same.
      apply c_insert_typesafe; obvious. rewrite <-same.
      apply c_insert_typesafe; obvious. } 
    { unfold c_subs2_out. do 2 try eapply c_subs_out_typesafe.
      instantiate (2:=Al). instantiate (1:=(TyList Al)).
      2: obvious_vtype. 2: simpl; obvious_vtype.
      { assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
        = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
        { intros. destruct γ; simpl; auto. }
        rewrite <-(c_shift_shift 1 1). rewrite <-same.
        apply c_insert_typesafe; obvious. rewrite <-same.
        apply c_insert_typesafe; obvious. } }
    }

  apply ceq_refl; obvious. 2: apply wf_hyp_shift_typesafe; obvious.

  { unfold c_subs2_out.
    eapply c_subs_typesafe. 3: reflexivity. instantiate (1:=Al). simpl.
    eapply c_subs_typesafe. 3: reflexivity. instantiate (1:=(TyList Al)).
    simpl. rewrite <-(c_shift_shift 1 1).
    assert (forall γ α, ctx_insert (CtxU(CtxU(CtxU γ Bop) Al) (TyList Al)) 3 α 
    = CtxU(CtxU(CtxU (CtxU γ α) Bop) Al) (TyList Al)) as same.
    { intros. destruct γ; simpl; auto. }
    rewrite <-same. apply c_insert_typesafe; obvious.
    rewrite <-same. apply c_insert_typesafe; obvious.
    obvious_vtype. simpl. omega. obvious_vtype. simpl. omega. }

Qed.
