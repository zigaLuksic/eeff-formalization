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

(* ========================================================================== *)

Definition TyBool := (TySum TyUnit TyUnit).

Definition VTrue := Left TyUnit TyUnit Unit.
Definition VFalse := Right TyUnit TyUnit Unit.

Example sig := (SigU (SigØ) ("choose") TyUnit TyBool).


Lemma sig_wf:
  wf_sig sig.
Proof.
unfold sig. obvious.
Qed.


Example eq_idem := (EqsU (EqsØ) CtxØ (TCtxU TCtxØ TyUnit)
  (TApp 0 Unit)
  (TOp "choose" TyUnit TyBool Unit
    (TSumMatch (Var 0) (TApp 0 Unit) (TApp 0 Unit)))
).

Example eq_idem_assoc := (EqsU eq_idem CtxØ
  (TCtxU (TCtxU (TCtxU TCtxØ TyUnit) TyUnit) TyUnit)
  (TOp "choose" TyUnit TyBool Unit 
    (TSumMatch (Var 0) 
      (TApp 0 Unit) 
      (TOp "choose" TyUnit TyBool Unit 
        (TSumMatch (Var 0) (TApp 1 Unit) (TApp 2 Unit)))))
  (TOp "choose" TyUnit TyBool Unit 
    (TSumMatch (Var 0) 
      (TOp "choose" TyUnit TyBool Unit 
        (TSumMatch (Var 0) (TApp 0 Unit) (TApp 1 Unit)))
      (TApp 2 Unit) ))
).

Lemma eq_idem_wf:
  wf_eqs eq_idem sig.
Proof.
unfold eq_idem. unfold TyBool. apply WfEqsU; obvious.
- eapply WfTApp; obvious. obvious_vtype. simpl. auto.
- eapply WfTOp; obvious_vtype.
  + unfold sig. simpl. reflexivity.
  + eapply vsubtype_refl. obvious.
  + eapply vsubtype_refl. obvious.
  + eapply WfTSumMatch.
    * apply TypeV; obvious_vtype. apply TypeVar. simpl. auto.
    * eapply WfTApp. obvious_vtype. simpl. auto.
    * eapply WfTApp. obvious_vtype. simpl. auto.
Qed.


Lemma eq_idem_assoc_wf:
  wf_eqs eq_idem_assoc sig.
Proof.
unfold eq_idem_assoc. unfold TyBool. apply WfEqsU; obvious. apply eq_idem_wf.
- eapply WfTOp; obvious_vtype.
  unfold sig. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl; obvious. }
  eapply WfTSumMatch; obvious_vtype.
  + eapply WfTApp. obvious_vtype. simpl. auto.
  + eapply WfTOp; obvious_vtype.
    unfold sig. simpl. reflexivity.
    { apply vsubtype_refl. obvious. }
    { apply vsubtype_refl; obvious. }
    eapply WfTSumMatch; obvious_vtype.
    all: eapply WfTApp; obvious_vtype.
- eapply WfTOp; obvious_vtype.
  unfold sig. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl; obvious. }
  eapply WfTSumMatch; obvious_vtype.
  + eapply WfTOp; obvious_vtype.
    unfold sig. simpl. reflexivity.
    { apply vsubtype_refl. obvious. }
    { apply vsubtype_refl; obvious. }
    eapply WfTSumMatch; obvious_vtype.
    all: eapply WfTApp; obvious_vtype.
  + eapply WfTApp. obvious_vtype. simpl. auto.
Qed.


(* ========================================================================== *)

Example cases D :=
  (CasesU (CasesØ D)
    "choose" TyUnit TyBool (App (Var 0) VTrue)).


Lemma cases_respect D:
  wf_ctype D ->
  respects CtxØ (cases D) sig D eq_idem_assoc.
Proof.
intros wfd.
unfold sig. unfold eq_idem_assoc.
apply Respects; obvious. apply eq_idem_assoc_wf.
apply RespectEqsU. apply Respects; obvious. apply eq_idem_wf.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.

{(* IDEMPOTENCY *)
simpl_c_subs. simpl_c_subs.

apply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2: apply βApp.
all: simpl_c_subs. apply WfCeq. 

{ ctype_step. instantiate (1:=TyBool). obvious_vtype.
  obvious_ctype. obvious_vtype. }
{ obvious_ctype. }

eapply ceq_trans. apply WfJudg; obvious. 2: apply βMatchLeft.
all: simpl_c_subs. apply WfCeq.

{ obvious_ctype. }
{ obvious_ctype. } 

apply ceq_refl. obvious_ctype. obvious.
}

{(* ASSOCIATIVITY *)
simpl_c_subs. simpl_c_subs.

(* Clean Right*)
apply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2: apply βApp.
all: simpl_c_subs. apply WfCeq.

{ ctype_step. instantiate (1:=TyBool). obvious_vtype. ctype_step. simpl.
  obvious_vtype. ctype_step. instantiate (1:=TyBool).
  obvious_vtype. obvious_ctype. obvious_vtype. obvious_ctype. obvious_vtype. }
{ ctype_step. obvious_vtype. ctype_step. instantiate (1:=TyBool).
  obvious_vtype. obvious_ctype. obvious_vtype. obvious_ctype. }

 eapply ceq_trans. apply WfJudg; obvious. 2: apply βMatchLeft.
all: simpl_c_subs. apply WfCeq.

{ ctype_step. obvious_vtype. ctype_step. instantiate (1:=TyBool).
  obvious_vtype. obvious_ctype. obvious_vtype. obvious_ctype. }
{ ctype_step. instantiate (1:=TyBool). obvious_vtype. obvious_ctype.
  obvious_vtype. }

eapply ceq_trans. apply WfJudg; obvious. 2: apply βApp.
all: simpl_c_subs. apply WfCeq.

{ ctype_step. instantiate (1:=TyBool). obvious_vtype. obvious_ctype.
  obvious_vtype. }
{ obvious_ctype. }

eapply ceq_trans. apply WfJudg; obvious. 2: apply βMatchLeft.
all: simpl_c_subs. apply WfCeq.

{ obvious_ctype. }
{ obvious_ctype. }

(* Clean Left *)
apply ceq_sym. eapply ceq_trans. apply WfJudg; obvious. 2: apply βApp.
all: simpl_c_subs. apply WfCeq.

{ ctype_step. instantiate (1:=TyBool). obvious_vtype. ctype_step.
  obvious_vtype. ctype_step. 2: obvious_vtype. obvious_vtype. 
  ctype_step. instantiate (1:=TyBool). obvious_vtype. obvious_ctype. 
  obvious_vtype. obvious_vtype. }
{ ctype_step. obvious_vtype. ctype_step. 2: obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:=TyBool). obvious_vtype. obvious_ctype. 
  obvious_vtype. }

eapply ceq_trans. apply WfJudg; obvious. 2: apply βMatchLeft.
all: simpl_c_subs. apply WfCeq.

{ ctype_step. obvious_vtype. ctype_step. 2: obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:=TyBool). obvious_vtype. obvious_ctype. 
  obvious_vtype. }
{ obvious_ctype. }

apply ceq_refl; obvious_ctype.
}
Qed.
