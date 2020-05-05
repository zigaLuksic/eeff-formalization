(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Import syntax.


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
