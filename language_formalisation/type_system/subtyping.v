Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Import syntax.


Inductive vsubtype : vtype -> vtype -> Prop :=
| VsubtyUnit : vsubtype TyUnit TyUnit
| VsubtyInt : vsubtype TyInt TyInt
| VsubtyTyØ : vsubtype TyØ TyØ
| VsubtyTyΣ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΣ A B) (TyΣ A' B')
| VsubtyTyΠ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΠ A B) (TyΠ A' B')
| VsubtyFun A A' C C' : 
    vsubtype A' A -> csubtype C C' -> vsubtype (TyFun A C) (TyFun A' C')
| VsubtyHandler C C' D D': 
    csubtype C' C -> csubtype D D' -> vsubtype (TyHandler C D) (TyHandler C' D')

with csubtype : ctype -> ctype -> Prop  :=
| Csubty A A' Σ Σ' E E': 
    vsubtype A A' -> sig_subtype Σ Σ' -> eqs_subtype E E' ->
    csubtype (CTy A Σ E) (CTy A' Σ' E')

with sig_subtype : sig -> sig -> Prop :=
| SigØsubty Σ: sig_subtype SigØ Σ
| SigUsubty Σ Σ' op A B A' B' : 
    sig_subtype Σ Σ' -> 
    get_op_type Σ op = None -> get_op_type Σ' op = Some (A', B') -> 
    vsubtype A' A -> vsubtype B B' ->
    sig_subtype (SigU Σ op A B) Σ'

with eqs_subtype : eqs -> eqs -> Prop :=
| EqsØsubty E: eqs_subtype EqsØ E
| EqsUsubty E E' Γ Z T1 T2 : 
    eqs_subtype E E' -> eqs_contain_eq E' Γ Z T1 T2 ->
    eqs_subtype (EqsU E Γ Z T1 T2) E'
.

Inductive ctx_subtype : ctx -> ctx -> Prop :=
| CtxØsubty : ctx_subtype CtxØ CtxØ
| CtxUsubty Γ Γ' A A' : 
    ctx_subtype Γ Γ' -> vsubtype A A' -> ctx_subtype (CtxU Γ A) (CtxU Γ' A')
.
