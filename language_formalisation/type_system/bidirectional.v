Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import syntax.

Inductive vtysynth : ctx -> val -> vtype -> Type :=
| SynthUnit Γ : vtysynth Γ Unit TyUnit 
| SynthInt Γ n : vtysynth Γ (Int n) TyInt
| SynthVar Γ id α :
    get_vtype Γ id = Some α ->
    vtysynth Γ (Var id) α
| SynthPair Γ v1 v2 α β :
    vtysynth Γ v1 α ->
    vtysynth Γ v2 β ->
    vtysynth Γ (Pair v1 v2) (TyΠ α β)
| SynthVAnnot Γ v α :
    vtycheck Γ v α ->
    vtysynth Γ (VAnnot v α) α
with ctysynth : ctx -> comp -> ctype -> Type :=
| SynthRet Γ v α : ctysynth Γ (Ret v) (CTy α SigØ EqsØ)
| SynthPMatch Γ v α β x y c ctyC :
    vtysynth Γ v (TyΠ α β) ->
    ctysynth (CtxU x α (CtxU y β Γ)) c ctyC ->
    ctysynth Γ c ctyC
| SynthApp Γ v1 v2 α ctyC :
    vtysynth Γ v1 (TyFun α ctyC) ->
    vtycheck Γ v2 α ->
    ctysynth Γ (App v1 v2) ctyC
| SynthHandle Γ v c ctyC ctyD :
    vtysynth Γ v (TyHandler ctyC ctyD) ->
    ctycheck Γ c ctyC ->
    ctysynth Γ (Handle v c) ctyC
| SynthCAnnot Γ c ctyC :
    ctycheck Γ c ctyC ->
    ctysynth Γ (CAnnot c ctyC) ctyC
(* with htysynth : ctx -> hcases -> sig -> ctype -> Type := *)
with vtycheck : ctx -> val -> vtype -> Type :=
| CheckVBySynth Γ v α α' :
    vtysynth Γ v α' ->
    α = α' ->
    vtycheck Γ v α
| CheckInl Γ v α β :
    vtycheck Γ v α ->
    vtycheck Γ (Inl v) (TyΣ α β)
| CheckInr Γ v α β :
    vtycheck Γ v β ->
    vtycheck Γ (Inr v) (TyΣ α β)
| CheckPair Γ v1 v2 α β :
    vtycheck Γ v1 α ->
    vtycheck Γ v2 β ->
    vtycheck Γ (Pair v1 v2) (TyΠ α β)
| CheckFun Γ x c α tyC :
    ctycheck (CtxU x α Γ) c tyC ->
    vtycheck Γ (Fun x c) (TyFun α tyC)
| CheckHandler Γ x c_ret h α sig eqs ctyD :
    ctycheck (CtxU x α Γ) c_ret ctyD ->
    htycheck Γ h sig ctyD ->
    vtycheck Γ (Handler x c_ret h) (TyHandler (CTy α sig eqs) ctyD)
with ctycheck : ctx -> comp -> ctype -> Type :=
| CheckCBySynth Γ c ctyC ctyC' :
    ctysynth Γ c ctyC' ->
    ctyC = ctyC' ->
    ctycheck Γ c ctyC
| CheckSMatch Γ v α β xl cl xr cr ctyC :
    vtysynth Γ v (TyΣ α β) ->
    ctycheck (CtxU xl α Γ) cl ctyC ->
    ctycheck (CtxU xr β Γ) cr ctyC ->
    ctycheck Γ (ΣMatch v xl cl xr cr) ctyC
| CheckOp Γ op_id v y c α_op β_op α sig eqs :
    get_op_type sig op_id = Some (α_op, β_op) ->
    vtycheck Γ v α_op ->
    ctycheck (CtxU y β_op Γ) c (CTy α sig eqs) ->
    ctycheck Γ (Op op_id v y c) (CTy α sig eqs)
with htycheck : ctx -> hcases -> sig -> ctype -> Type :=
| CheckCasesØ Γ ctyD : htycheck Γ CasesØ SigØ ctyD
| CheckCasesU Γ h op_id x k c_op α_op β_op sig ctyD :
    find_op_case h op_id = None ->
    htycheck Γ h sig ctyD ->
    ctycheck
      (CtxU x α_op (CtxU k (TyFun β_op ctyD) Γ))
      c_op ctyD ->
    htycheck 
      Γ (CasesU h op_id x k c_op)
      (SigU op_id α_op β_op sig) ctyD
.