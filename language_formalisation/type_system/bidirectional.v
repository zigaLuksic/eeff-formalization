(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Import syntax.

Inductive vsynth : ctx -> val -> vtype -> Type :=
| SynthUnit Γ : vsynth Γ Unit TyUnit 
| SynthInt Γ n : vsynth Γ (Int n) TyInt
| SynthVar Γ id A :
    get_vtype Γ id = Some A ->
    vsynth Γ (Var id) A
| SynthPair Γ v1 v2 A B :
    vsynth Γ v1 A ->
    vsynth Γ v2 B ->
    vsynth Γ (Pair v1 v2) (TyΠ A B)
| SynthVAnnot Γ v A :
    vcheck Γ v A ->
    vsynth Γ (VAnnot v A) A
with csynth : ctx -> comp -> ctype -> Type :=
| SynthRet Γ v A : 
    vsynth Γ v A ->
    csynth Γ (Ret v) (CTy A SigØ EqsØ)
| SynthΠMatch Γ v A B x y c C :
    vsynth Γ v (TyΠ A B) ->
    csynth (CtxU (CtxU Γ A) B) c C ->
    csynth Γ (ΠMatch v (x, y) c) C
| SynthApp Γ v1 v2 A C :
    vsynth Γ v1 (TyFun A C) ->
    vcheck Γ v2 A ->
    csynth Γ (App v1 v2) C
| SynthHandle Γ v c C D :
    vsynth Γ v (TyHandler C D) ->
    ccheck Γ c C ->
    csynth Γ (Handle v c) D
| SynthCAnnot Γ c C :
    ccheck Γ c C ->
    csynth Γ (CAnnot c C) C
| SynthLetRec Γ f x A C c1 c2 D:
    ccheck (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    csynth (CtxU Γ (TyFun A C)) c2 D ->
    csynth Γ (LetRec f x (TyFun A C) c1 c2) D
(* with hsynth : ctx -> hcases -> sig -> ctype -> Type := *)
with vcheck : ctx -> val -> vtype -> Type :=
| CheckVBySynth Γ v A : vsynth Γ v A -> vcheck Γ v A
| CheckInl Γ v A B :
    vcheck Γ v A ->
    vcheck Γ (Inl v) (TyΣ A B)
| CheckInr Γ v A B :
    vcheck Γ v B ->
    vcheck Γ (Inr v) (TyΣ A B)
| CheckFun Γ x c A C :
    ccheck (CtxU Γ A) c C ->
    vcheck Γ (Fun x c) (TyFun A C)
| CheckHandler Γ x c_ret h A sig eqs D :
    ccheck (CtxU Γ A) c_ret D ->
    hcheck Γ h sig D ->
    vcheck Γ (Handler x c_ret h) (TyHandler (CTy A sig eqs) D)
with ccheck : ctx -> comp -> ctype -> Type :=
| CheckCBySynth Γ c C C' : csynth Γ c C' -> C = C' -> ccheck Γ c C
| CheckΣMatch Γ v A B xl cl xr cr C :
    vsynth Γ v (TyΣ A B) ->
    ccheck (CtxU Γ A) cl C ->
    ccheck (CtxU Γ B) cr C ->
    ccheck Γ (ΣMatch v xl cl xr cr) C
| CheckOp Γ op_id v y c A_op B_op A Σ eqs :
    get_op_type Σ op_id = Some (A_op, B_op) ->
    vcheck Γ v A_op ->
    ccheck (CtxU Γ B_op) c (CTy A Σ eqs) ->
    ccheck Γ (Op op_id v y c) (CTy A Σ eqs)
with hcheck : ctx -> hcases -> sig -> ctype -> Type :=
| CheckCasesØ Γ D : hcheck Γ CasesØ SigØ D
| CheckCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_op_case h op_id = None ->
    hcheck Γ h Σ D ->
    ccheck (CtxU (CtxU Γ (TyFun B_op D)) A_op) c_op D ->
    hcheck 
      Γ (CasesU h op_id x k c_op)
      (SigU Σ op_id A_op B_op) D
.