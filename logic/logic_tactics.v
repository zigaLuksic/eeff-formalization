Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".
Add LoadPath "???\operational_semantics".
Add LoadPath "???\logic".

Require Export type_lemmas.


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
|| (apply TypeFun; obvious)
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
|| (eapply TypeOp; ((apply vsubtype_refl; obvious) || obvious_vtype || auto))
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

