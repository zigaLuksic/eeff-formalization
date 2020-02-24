Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic". *)

Require Export type_lemmas logic_lemmas.
Open Scope string_scope.

Ltac obvious := 
     apply WfCtxØ || (apply WfCtxU; obvious) 
  || apply WfTCtxØ  || (apply WfTCtxU; obvious) 
  || apply WfEqsØ || apply WfSigØ || (apply WfSigU; obvious)
  || apply WfTyUnit || apply WfTyInt 
  || (apply WfTyFun; obvious) || (apply WfTyΣ; obvious)
  || (apply WfTyΠ; obvious) || (apply WfCTy; obvious)
  || auto.

Ltac obvious_vtype := ((apply TypeV; ((apply TypeUnit; obvious)
  || (apply TypeInt; obvious)
  || (apply TypeInl; obvious_vtype)
  || (apply TypeInr; obvious_vtype)
  || obvious))
  || obvious).


Example sig := (SigU (SigØ) ("choose") TyUnit (TyΣ TyUnit TyUnit)).


Lemma sig_wf:
  wf_sig sig.
Proof.
unfold sig. obvious.
Qed.


Example eq_idem := (EqsU (EqsØ) CtxØ (TCtxU TCtxØ TyUnit)
  (TApp 0 Unit)
  (TOp "choose" Unit 
    (TΣMatch (Var 0) (TApp 0 Unit) (TApp 0 Unit)))
).


Lemma eq_idem_wf:
  wf_eqs eq_idem sig.
Proof.
assert (forall Γ, wf_ctx Γ -> has_vtype Γ Unit TyUnit).
{ intros Γ wf. apply TypeV; obvious. apply TypeUnit. }
unfold eq_idem. apply WfEqsU; obvious.
- eapply WfTApp; obvious. apply H; obvious. simpl. auto.
- eapply WfTOp; obvious_vtype.
  + unfold sig. simpl. reflexivity.
  + eapply WfTΣMatch.
    * apply TypeV; obvious. apply TypeVar. simpl. auto.
    * eapply WfTApp. obvious_vtype. simpl. auto.
    * eapply WfTApp. obvious_vtype. simpl. auto.
Qed.


Example handler :=
  Handler (Ret (Var 0))
  (CasesU CasesØ
    "choose" (App (Var 1) (Inl Unit))).


Lemma handler_types:
  has_vtype 
    CtxØ handler 
    (TyHandler (CTy TyInt sig eq_idem) (CTy TyInt SigØ EqsØ))
.
specialize eq_idem_wf as eqwf.
apply TypeV; obvious. apply WfTyHandler; obvious.
apply TypeHandler; obvious.
+ apply TypeC; obvious. apply TypeRet. apply TypeV; obvious.
  apply TypeVar. simpl. auto.
+ apply TypeH; obvious. apply TypeCasesU; obvious.
  - apply TypeH; obvious. apply TypeCasesØ.
  - apply TypeC; obvious.
    eapply TypeApp; obvious.
    * apply TypeV; auto. obvious.
      instantiate (1:= TyΣ TyUnit TyUnit). obvious.
      apply TypeVar. simpl. auto.
    * obvious_vtype.
+ apply Respects; obvious.
  apply RespectEqsU.
  apply Respects; obvious. apply RespectEqsØ.
  simpl. unfold c_subs2_out. unfold c_subs_out. unfold c_subs. simpl.
  eapply ceq_sym. eapply ceq_trans. apply operational_in_logic.
  - apply TypeC; obvious.
    eapply TypeApp.
    Focus 2.
      instantiate (1:= TyΣ TyUnit TyUnit).
      obvious_vtype.
    apply TypeV; obvious. apply TypeFun. apply TypeC; obvious.
    eapply TypeΣMatch. obvious_vtype. apply TypeVar. simpl. auto.
    all: eapply TypeC; obvious; eapply TypeApp; obvious.
    * apply TypeV; obvious. apply TypeVar. auto.
    * obvious_vtype.
    * apply TypeV; obvious. apply TypeVar. auto.
    * obvious_vtype.
  - apply Step_App.
  - unfold c_subs_out. unfold c_subs. simpl.
    eapply Ceq; obvious.
    * apply TypeC; obvious. eapply TypeΣMatch; obvious_vtype.
      all: apply TypeC; obvious; eapply TypeApp; obvious_vtype.
      all: apply TypeVar; auto.
    * apply TypeC; obvious. eapply TypeApp; obvious_vtype.
      apply TypeVar; auto.
    * eapply βΣMatch_Inl.
Qed.
