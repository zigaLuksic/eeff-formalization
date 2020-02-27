Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\examples".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\examples". *)

Require Export type_lemmas logic_lemmas logic_tactics.
Open Scope string_scope.

(* ========================================================================== *)

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

Example eq_idem_assoc := (EqsU eq_idem CtxØ
  (TCtxU (TCtxU (TCtxU TCtxØ TyUnit) TyUnit) TyUnit)
  (TOp "choose" Unit 
    (TΣMatch (Var 0) 
      (TApp 0 Unit) 
      (TOp "choose" Unit 
        (TΣMatch (Var 0) (TApp 1 Unit) (TApp 2 Unit)))))
  (TOp "choose" Unit 
    (TΣMatch (Var 0) 
      (TOp "choose" Unit 
        (TΣMatch (Var 0) (TApp 0 Unit) (TApp 1 Unit)))
      (TApp 2 Unit) ))
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


Lemma eq_idem_assoc_wf:
  wf_eqs eq_idem_assoc sig.
Proof.
unfold eq_idem_assoc. apply WfEqsU; obvious. apply eq_idem_wf.
- eapply WfTOp; obvious_vtype.
  unfold sig. simpl. reflexivity.
  eapply WfTΣMatch; obvious_vtype.
  + eapply WfTApp. obvious_vtype. simpl. auto.
  + eapply WfTOp; obvious_vtype.
    unfold sig. simpl. reflexivity.
    eapply WfTΣMatch; obvious_vtype.
    all: eapply WfTApp; obvious_vtype.
- eapply WfTOp; obvious_vtype.
  unfold sig. simpl. reflexivity.
  eapply WfTΣMatch; obvious_vtype.
  + eapply WfTOp; obvious_vtype.
    unfold sig. simpl. reflexivity.
    eapply WfTΣMatch; obvious_vtype.
    all: eapply WfTApp; obvious_vtype.
  + eapply WfTApp. obvious_vtype. simpl. auto.
Qed.


(* ========================================================================== *)

Example cases :=
  (CasesU CasesØ
    "choose" (App (Var 1) (Inl Unit))).

Example handler :=
  Handler (Ret (Var 0)) cases.


Lemma cases_respect D:
  wf_ctype D ->
  respects CtxØ cases sig D eq_idem_assoc.
Proof.
intros wfd.
unfold sig. unfold eq_idem_assoc.
apply Respects; obvious. apply eq_idem_assoc_wf.
apply RespectEqsU. apply Respects; obvious. apply eq_idem_wf.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
{
apply ceq_sym. simpl_c_subs.
assert (has_ctype (CtxU CtxØ (TyFun TyUnit D))
  (App (Fun (ΣMatch (Var 0) (App (Var 2) Unit) (App (Var 2) Unit))) (Inl Unit))
  D ).
{ apply TypeC; obvious. eapply TypeApp. instantiate (1:= TyΣ TyUnit TyUnit).
  2: obvious_vtype. apply TypeV; obvious. apply TypeFun.
  apply TypeC; obvious. eapply TypeΣMatch. obvious_vtype.
  all: obvious_ctype. }
eapply ceq_trans. apply Ceq. auto. 2: apply βApp.
{ simpl_c_subs. apply TypeC; obvious. eapply TypeΣMatch. obvious_vtype.
  all: obvious_ctype. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.
{ apply TypeC; obvious. eapply TypeΣMatch. obvious_vtype.
  all: obvious_ctype. }
all: simpl_c_subs. obvious_ctype. apply ceq_refl. obvious_ctype.
}{
simpl. simpl_c_subs.
eapply ceq_trans. apply Ceq. 3: apply βApp.
{ apply TypeC; obvious. eapply TypeApp. instantiate (1:= TyΣ TyUnit TyUnit).
  + apply TypeV; obvious. apply TypeFun. obvious_ctype. obvious_ctype.
    apply TypeC; obvious. eapply TypeApp. instantiate (1:= TyΣ TyUnit TyUnit).
    - apply TypeV; obvious. apply TypeFun.
      obvious_ctype. all: obvious_ctype.
    - obvious_vtype.
  + obvious_vtype. }
{ simpl_c_subs.
  apply TypeC; obvious. eapply TypeΣMatch. obvious_vtype. obvious_ctype.
  apply TypeC; obvious. eapply TypeApp. instantiate (1:= TyΣ TyUnit TyUnit).
  - apply TypeV; obvious. apply TypeFun.
    apply TypeC; obvious. eapply TypeΣMatch. obvious_vtype.
    all: obvious_ctype.
  - obvious_vtype. }
simpl_c_subs. apply ceq_sym. eapply ceq_trans. apply Ceq. 3: apply βApp.
{ ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step. obvious_ctype.
  - ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step.
    obvious_ctype. obvious_ctype. obvious_ctype. obvious_vtype.
  - obvious_ctype.
  - obvious_vtype. }
{ simpl_c_subs. obvious_ctype. 2: obvious_ctype.
  ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step.
  obvious_ctype; obvious_ctype. obvious_vtype. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.
all: simpl_c_subs.
{ simpl_c_subs. obvious_ctype. 2: obvious_ctype.
  ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step.
  obvious_ctype; obvious_ctype. obvious_vtype. }
{ ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step.
  obvious_ctype; obvious_ctype. obvious_vtype. }
eapply ceq_trans. apply Ceq. 3: apply βApp. all: simpl_c_subs.
{ ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). vtype_step.
  obvious_ctype; obvious_ctype. obvious_vtype. }
{ obvious_ctype; obvious_ctype. }
eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl. all: simpl_c_subs.
{ obvious_ctype; obvious_ctype. }
{ obvious_ctype. }
eapply ceq_sym. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.
{ obvious_ctype. obvious_ctype. ctype_step. instantiate (1:= TyΣ TyUnit TyUnit).
  vtype_step. obvious_ctype; obvious_ctype. obvious_vtype. }
{ simpl_c_subs. obvious_ctype. }
simpl_c_subs. apply ceq_refl. obvious_ctype.
}
Qed.


Lemma handler_types:
  has_vtype 
    CtxØ handler 
    (TyHandler (CTy TyInt sig eq_idem_assoc) (CTy TyInt SigØ EqsØ))
.
specialize eq_idem_assoc_wf as eqwf.
apply TypeV; obvious.
apply TypeHandler; obvious.
+ obvious_ctype.
+ apply TypeH; obvious. apply TypeCasesU; obvious.
  - apply TypeH; obvious. apply TypeCasesØ.
  - ctype_step. instantiate (1:= TyΣ TyUnit TyUnit).
    obvious_vtype. obvious_vtype.
+ apply cases_respect. obvious.
Qed.
