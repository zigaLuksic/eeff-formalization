Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
Require Import syntax.


Inductive vsubtype : vtype -> vtype -> Prop :=
| SubtypeUnit : vsubtype TyUnit TyUnit
| SubtypeInt : vsubtype TyInt TyInt
| SubtypeTyØ : vsubtype TyØ TyØ
| SubtypeTyΣ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> 
    vsubtype (TyΣ A B) (TyΣ A' B')
| SubtypeTyΠ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> 
    vsubtype (TyΠ A B) (TyΠ A' B')
| SubtypeTyFun A A' C C' : 
    vsubtype A' A -> csubtype C C' -> 
    vsubtype (TyFun A C) (TyFun A' C')
| SubtypeTyHandler C C' D D': 
    csubtype C' C -> csubtype D D' -> 
    vsubtype (TyHandler C D) (TyHandler C' D')

with csubtype : ctype -> ctype -> Prop  :=
| SubtypeCTy A A' Σ Σ' E E': 
    vsubtype A A' -> sig_subtype Σ Σ' -> eqs_subtype E E' ->
    csubtype (CTy A Σ E) (CTy A' Σ' E')

with sig_subtype : sig -> sig -> Prop :=
| SubtypeSigØ Σ: sig_subtype SigØ Σ
| SubtypeSigU Σ Σ' op A B A' B' : 
    sig_subtype Σ Σ' -> get_op_type Σ' op = Some (A', B') -> 
    vsubtype A A' -> vsubtype B' B ->
    sig_subtype (SigU Σ op A B) Σ'

with eqs_subtype : eqs -> eqs -> Prop :=
| SubtypeEqsØ E: eqs_subtype EqsØ E
| SubtypeEqsU E E' Γ Z T1 T2 : 
    eqs_subtype E E' -> has_eq E' Γ Z T1 T2 ->
    eqs_subtype (EqsU E Γ Z T1 T2) E'
.


Inductive ctx_subtype : ctx -> ctx -> Prop :=
| SubtypeCtxØ : ctx_subtype CtxØ CtxØ
| SubtypeCtxU Γ Γ' A A' : 
    ctx_subtype Γ Γ' -> vsubtype A A' -> 
    ctx_subtype (CtxU Γ A) (CtxU Γ' A')
.
