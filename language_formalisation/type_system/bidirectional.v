Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import syntax.

Inductive vsynth : ctx -> val -> vtype -> Type :=
| SynthUnit Γ : vsynth Γ Unit TyUnit 
| SynthInt Γ n : vsynth Γ (Int n) TyInt
| SynthVar Γ id α :
    get_vtype Γ id = Some α ->
    vsynth Γ (Var id) α
| SynthPair Γ v1 v2 α β :
    vsynth Γ v1 α ->
    vsynth Γ v2 β ->
    vsynth Γ (Pair v1 v2) (TyΠ α β)
| SynthVAnnot Γ v α :
    vcheck Γ v α ->
    vsynth Γ (VAnnot v α) α
with csynth : ctx -> comp -> ctype -> Type :=
| SynthRet Γ v α : csynth Γ (Ret v) (CTy α SigØ EqsØ)
| SynthPMatch Γ v α β x y c ctyC :
    vsynth Γ v (TyΠ α β) ->
    csynth (CtxU x α (CtxU y β Γ)) c ctyC ->
    csynth Γ c ctyC
| SynthApp Γ v1 v2 α ctyC :
    vsynth Γ v1 (TyFun α ctyC) ->
    vcheck Γ v2 α ->
    csynth Γ (App v1 v2) ctyC
| SynthHandle Γ v c ctyC ctyD :
    vsynth Γ v (TyHandler ctyC ctyD) ->
    ccheck Γ c ctyC ->
    csynth Γ (Handle v c) ctyC
| SynthCAnnot Γ c ctyC :
    ccheck Γ c ctyC ->
    csynth Γ (CAnnot c ctyC) ctyC
(* with hsynth : ctx -> hcases -> sig -> ctype -> Type := *)
with vcheck : ctx -> val -> vtype -> Type :=
| CheckVBySynth Γ v α α' :
    vsynth Γ v α' ->
    α = α' ->
    vcheck Γ v α
| CheckInl Γ v α β :
    vcheck Γ v α ->
    vcheck Γ (Inl v) (TyΣ α β)
| CheckInr Γ v α β :
    vcheck Γ v β ->
    vcheck Γ (Inr v) (TyΣ α β)
| CheckPair Γ v1 v2 α β :
    vcheck Γ v1 α ->
    vcheck Γ v2 β ->
    vcheck Γ (Pair v1 v2) (TyΠ α β)
| CheckFun Γ x c α tyC :
    ccheck (CtxU x α Γ) c tyC ->
    vcheck Γ (Fun x c) (TyFun α tyC)
| CheckHandler Γ x c_ret h α sig eqs ctyD :
    ccheck (CtxU x α Γ) c_ret ctyD ->
    hcheck Γ h sig ctyD ->
    vcheck Γ (Handler x c_ret h) (TyHandler (CTy α sig eqs) ctyD)
with ccheck : ctx -> comp -> ctype -> Type :=
| CheckCBySynth Γ c ctyC ctyC' :
    csynth Γ c ctyC' ->
    ctyC = ctyC' ->
    ccheck Γ c ctyC
| CheckSMatch Γ v α β xl cl xr cr ctyC :
    vsynth Γ v (TyΣ α β) ->
    ccheck (CtxU xl α Γ) cl ctyC ->
    ccheck (CtxU xr β Γ) cr ctyC ->
    ccheck Γ (ΣMatch v xl cl xr cr) ctyC
| CheckOp Γ op_id v y c α_op β_op α sig eqs :
    get_op_type sig op_id = Some (α_op, β_op) ->
    vcheck Γ v α_op ->
    ccheck (CtxU y β_op Γ) c (CTy α sig eqs) ->
    ccheck Γ (Op op_id v y c) (CTy α sig eqs)
with hcheck : ctx -> hcases -> sig -> ctype -> Type :=
| CheckCasesØ Γ ctyD : hcheck Γ CasesØ SigØ ctyD
| CheckCasesU Γ h op_id x k c_op α_op β_op sig ctyD :
    find_op_case h op_id = None ->
    hcheck Γ h sig ctyD ->
    ccheck
      (CtxU x α_op (CtxU k (TyFun β_op ctyD) Γ))
      c_op ctyD ->
    hcheck 
      Γ (CasesU h op_id x k c_op)
      (SigU op_id α_op β_op sig) ctyD
.