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

Definition Bool := (TyΣ TyUnit TyUnit).

Definition TConditional b T1 T2 := TΣMatch b T1 T2.


Example sig := (SigU (SigØ) ("choose") TyUnit Bool).


Lemma sig_wf:
  wf_sig sig.
Proof.
unfold sig. obvious.
Qed.


Example eq_idem := (EqsU (EqsØ) CtxØ (TCtxU TCtxØ TyUnit)
  (TApp 0 Unit)
  (TOp "choose" Unit 
    (TConditional (Var 0) (TApp 0 Unit) (TApp 0 Unit)))
).

Example eq_idem_assoc := (EqsU eq_idem CtxØ
  (TCtxU (TCtxU (TCtxU TCtxØ TyUnit) TyUnit) TyUnit)
  (TOp "choose" Unit 
    (TConditional (Var 0) 
      (TApp 0 Unit) 
      (TOp "choose" Unit 
        (TConditional (Var 0) (TApp 1 Unit) (TApp 2 Unit)))))
  (TOp "choose" Unit 
    (TConditional (Var 0) 
      (TOp "choose" Unit 
        (TConditional (Var 0) (TApp 0 Unit) (TApp 1 Unit)))
      (TApp 2 Unit) ))
).

Lemma eq_idem_wf:
  wf_eqs eq_idem sig.
Proof.
unfold eq_idem. unfold sig. apply WfEqsU; obvious.
all: do 4 wft_step; simpl; auto; obvious_vtype.
Qed.


Lemma eq_idem_assoc_wf:
  wf_eqs eq_idem_assoc sig.
Proof.
unfold eq_idem_assoc. apply WfEqsU; obvious. apply eq_idem_wf.
all: do 5 (wft_step); simpl; auto; obvious_vtype.
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
apply Respects. 4: apply eq_idem_assoc_wf. all: obvious.
apply RespectEqsU. apply Respects. 4: apply eq_idem_wf. all: obvious.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
{
simpl. apply ceq_sym. simpl_c_subs.
eapply ceq_trans. apply Ceq. 3: apply βApp.

{ ctype_step. instantiate (1:= TyΣ TyUnit TyUnit). 2: obvious_vtype.
  vtype_step. obvious_ctype; obvious_ctype. }
{ simpl_c_subs. obvious_ctype; obvious_ctype. }

simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.

{ obvious_ctype; obvious_ctype. }
{ simpl_c_subs. obvious_ctype. }

simpl_c_subs. apply ceq_refl. obvious_ctype.
}
{
simpl. simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp.

{ ctype_step. instantiate (1:= Bool). 2: obvious_vtype.
  vtype_step. ctype_step. obvious_vtype. obvious_ctype. ctype_step.
  instantiate (1:= Bool). 2: obvious_vtype. vtype_step. obvious_ctype. }
{ simpl_c_subs. ctype_step. obvious_vtype. obvious_ctype. ctype_step.
  instantiate (1:= Bool). 2:obvious_vtype. vtype_step. obvious_ctype. }

simpl_c_subs. apply ceq_sym. eapply ceq_trans. apply Ceq. 3: apply βApp.

{ ctype_step. instantiate (1:= Bool). vtype_step. ctype_step. obvious_vtype.
  3: obvious_vtype. 2: obvious_ctype. ctype_step. instantiate (1:= Bool).
  vtype_step. obvious_ctype. obvious_vtype. }
{ simpl_c_subs. ctype_step. obvious_vtype. 2: obvious_ctype. ctype_step.
  instantiate (1:= Bool). vtype_step. obvious_ctype. obvious_vtype. }

simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.

{ simpl_c_subs. ctype_step. obvious_vtype. 2: obvious_ctype. ctype_step.
  instantiate (1:= Bool). vtype_step. obvious_ctype. obvious_vtype. }
{ simpl_c_subs. ctype_step. instantiate (1:= Bool). vtype_step.
  obvious_ctype. obvious_vtype. }

simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp. all: simpl_c_subs.

{ ctype_step. instantiate (1:= Bool). vtype_step.
  obvious_ctype. obvious_vtype. }
{ obvious_ctype. }

eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl. all: simpl_c_subs.

{ obvious_ctype; obvious_ctype. }
{ obvious_ctype. }

eapply ceq_sym. eapply ceq_trans. apply Ceq. 3: apply βΣMatch_Inl.

{ ctype_step. obvious_vtype. obvious_ctype. ctype_step.
  instantiate (1:= Bool). vtype_step. obvious_ctype. obvious_vtype. }
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
vtype_step.
+ obvious_ctype.
+ apply TypeH; obvious. apply TypeCasesU; obvious.
  - apply TypeH; obvious. apply TypeCasesØ.
  - ctype_step. instantiate (1:= Bool).
    obvious_vtype. obvious_vtype.
+ apply cases_respect. obvious.
Qed.
