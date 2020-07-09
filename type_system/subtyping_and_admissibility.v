Add LoadPath "???\syntax".
Require Import syntax.


(* ==================== Subtyping ==================== *)

Inductive vsubtype : vtype -> vtype -> Prop :=
| STyUnit : vsubtype TyUnit TyUnit
| STyInt : vsubtype TyInt TyInt
| STyEmpty : vsubtype TyEmpty TyEmpty
| STySum A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> 
    vsubtype (TySum A B) (TySum A' B')
| STyProd A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> 
    vsubtype (TyProd A B) (TyProd A' B')
| STyList A A' :
    vsubtype A A' ->
    vsubtype (TyList A) (TyList A')
| STyFun A A' C C' : 
    vsubtype A' A -> csubtype C C' -> 
    vsubtype (TyFun A C) (TyFun A' C')
| STyHandler C C' D D': 
    csubtype C' C -> csubtype D D' -> 
    vsubtype (TyHandler C D) (TyHandler C' D')

with csubtype : ctype -> ctype -> Prop  :=
| STyCTy A A' Σ Σ' E E': 
    vsubtype A A' -> sig_subtype Σ Σ' -> eqs_subtype E E' ->
    csubtype (CTy A Σ E) (CTy A' Σ' E')

with sig_subtype : sig -> sig -> Prop :=
| STySigØ Σ: sig_subtype SigØ Σ
| STySigU Σ Σ' op A B A' B' : 
    sig_subtype Σ Σ' -> get_op_type Σ' op = Some (A', B') -> 
    vsubtype A A' -> vsubtype B' B ->
    sig_subtype (SigU Σ op A B) Σ'

with eqs_subtype : eqs -> eqs -> Prop :=
| STyEqsØ E: eqs_subtype EqsØ E
| STyEqsU E E' Γ Z T1 T2 : 
    eqs_subtype E E' -> has_eq E' Γ Z T1 T2 ->
    eqs_subtype (EqsU E Γ Z T1 T2) E'
.


Inductive ctx_subtype : ctx -> ctx -> Prop :=
| STyCtxØ : ctx_subtype CtxØ CtxØ
| STyCtxU Γ Γ' A A' : 
    ctx_subtype Γ Γ' -> vsubtype A A' -> 
    ctx_subtype (CtxU Γ A) (CtxU Γ' A')
.

Inductive hyp_subset : hypotheses -> hypotheses -> Prop :=
| SubsetHypØ Ψ : hyp_subset HypØ Ψ
| SubsetHypU Ψ φ Ψ' : 
    hyp_subset Ψ Ψ' ->
    has_hypothesis Ψ' φ ->
    hyp_subset (HypU Ψ φ) Ψ'.


(* ==================== Admissibility ==================== *)

Inductive var_admissible : nat -> formula -> Prop :=
| AdmissNotPresent n φ :
    form_no_var φ n ->
    var_admissible n φ
| AdmissVeq n A v1 v2 :
    var_admissible n (Veq A v1 v2)
| AdmissCeq n C c1 c2 :
    var_admissible n (Ceq C c1 c2)
| AdmissHeq n Σ D h1 h2 :
    var_admissible n (Heq Σ D h1 h2)
| AdmissTruth n:
    var_admissible n Truth
| AdmissFalsity n:
    var_admissible n Falsity
| AdmissAnd n φ1 φ2:
    var_admissible n φ1 ->
    var_admissible n φ2 ->
    var_admissible n (And φ1 φ2)
| AdmissOr n φ1 φ2:
    var_admissible n φ1 ->
    var_admissible n φ2 ->
    var_admissible n (Or φ1 φ2)
| AdmissImplies n φ1 φ2:
    form_no_var φ1 n ->
    var_admissible n φ2 ->
    var_admissible n (Implies φ1 φ2)
| AdmissForall n A φ:
    var_admissible (1+n) φ ->
    var_admissible n (Forall A φ).