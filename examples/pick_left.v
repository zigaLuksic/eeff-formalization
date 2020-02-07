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

Require Export syntax_lemmas substitution_lemmas type_lemmas logic_lemmas String.
Open Scope string_scope.

Example sig := (SigU (SigØ) ("choose") TyUnit (TyΣ TyUnit TyUnit)).

Lemma sig_wf:
  wf_sig sig.
Proof.
unfold sig. apply WfSigU.
- apply WfSigØ.
- simpl. auto.
- apply WfTyUnit.
- apply WfTyΣ; apply WfTyUnit.
Qed.

Example eq_idem := (EqsU (EqsØ) CtxØ (TCtxU TCtxØ TyUnit)
  (TApp ("z", 0) Unit)
  (TOp "choose" Unit "y" 
    (TΣMatch (Var ("y", 0)) 
      "_" (TApp ("z", 0) Unit)
      "_" (TApp ("z", 0) Unit)))
).

Lemma eq_idem_wf:
  wf_eqs eq_idem sig.
Proof.
assert (wf_ctx CtxØ) by apply WfCtxØ.
assert (wf_vtype TyUnit) by apply WfTyUnit.
assert (forall Γ, wf_ctx Γ -> has_vtype Γ Unit TyUnit).
{ intros Γ wf. apply TypeV. auto. apply WfTyUnit. apply TypeUnit. }
unfold eq_idem. apply WfEqsU; auto.
- apply WfEqsØ.
- apply WfTCtxU. apply WfTCtxØ. apply WfTyUnit.
- apply sig_wf.
- eapply WfTApp; eauto.
- eapply WfTOp.
  + unfold sig. simpl. reflexivity.
  + auto.
  + eapply WfTΣMatch.
    * apply TypeV. apply WfCtxU. auto. apply WfTyΣ; auto.
      apply WfTyΣ; eauto. apply TypeVar. simpl. auto.
    * eapply WfTApp. apply H1.
      apply WfCtxU. apply WfCtxU. auto. apply WfTyΣ. all: auto.
    * eapply WfTApp. apply H1.
      apply WfCtxU. apply WfCtxU. auto. apply WfTyΣ. all: auto.
Qed.

Example handler :=
  Handler "x" (Ret (Var ("x", 0)))
  (CasesU CasesØ
    "choose" "k" "x" (App (Var ("k", 1)) (Inl Unit))).

Lemma handler_types:
  has_vtype CtxØ handler (TyHandler (CTy TyInt sig eq_idem) (CTy TyInt SigØ EqsØ))
.
assert (wf_ctype (CTy TyInt sig eq_idem)).
{ apply WfCTy. apply WfTyInt. apply sig_wf. apply eq_idem_wf. }
assert (wf_ctype (CTy TyInt SigØ EqsØ)).
{ apply WfCTy. apply WfTyInt. apply WfSigØ. apply WfEqsØ. }
apply TypeV. apply WfCtxØ. apply WfTyHandler; auto.
apply TypeHandler.
+ assert (wf_ctx (CtxU CtxØ TyInt)).
  apply WfCtxU. apply WfCtxØ. apply WfTyInt. 
  apply TypeC; auto.
  apply TypeRet. apply TypeV. auto. apply WfTyInt.
  apply TypeVar. simpl. auto.
+ assert (wf_ctx CtxØ) by apply WfCtxØ.
  apply TypeH; auto. apply sig_wf.
  apply TypeCasesU. 
  - simpl. auto.
  - apply TypeH; auto. apply WfSigØ.
    apply TypeCasesØ.
  - assert (wf_ctx (CtxU (CtxU CtxØ (TyFun (TyΣ TyUnit TyUnit) (CTy TyInt SigØ EqsØ))) TyUnit)).
    { assert (wf_vtype TyUnit) by apply WfTyUnit.
      apply WfCtxU. apply WfCtxU. auto. apply WfTyFun. apply WfTyΣ. all: auto. }
    apply TypeC; auto.
    eapply TypeApp.
    * apply TypeV; auto. inv H2. inv H5. eauto.
      apply TypeVar. simpl. auto.
    * apply TypeV; auto. apply WfTyΣ; apply WfTyUnit.
      apply TypeInl. apply TypeV; auto. apply WfTyUnit.
      apply TypeUnit.
+ apply Respects.
  apply WfCtxØ. apply sig_wf. auto. apply eq_idem_wf.
  apply RespectEqsU.
  apply Respects. apply WfCtxØ. apply sig_wf. auto. apply WfEqsØ.
  apply RespectEqsØ.
  simpl. unfold c_subs2_out. unfold c_subs_out. unfold c_subs. simpl.