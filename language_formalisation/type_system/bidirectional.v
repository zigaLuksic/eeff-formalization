Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import syntax.

Inductive vtysynth : ctx -> val -> vtype -> Type :=
| SynthUnit ctx : vtysynth ctx Unit TyUnit 
| SynthInt ctx n : vtysynth ctx (Int n) TyInt
| SynthVar ctx id tyA :
    get_vtype ctx id = Some tyA ->
    vtysynth ctx (Var id) tyA
| SynthPair ctx v1 v2 tyA tyB :
    vtysynth ctx v1 tyA ->
    vtysynth ctx v2 tyB ->
    vtysynth ctx (Pair v1 v2) (TyProd tyA tyB)
| SynthVAnnot ctx v tyA :
    vtycheck ctx v tyA ->
    vtysynth ctx (VAnnot v tyA) tyA
with ctysynth : ctx -> comp -> ctype -> Type :=
| SynthRet ctx v tyA : ctysynth ctx (Ret v) (CTy tyA SigNil EqsNil)
| SynthPMatch ctx v tyA tyB x y c ctyC :
    vtysynth ctx v (TyProd tyA tyB) ->
    ctysynth (CtxCons x tyA (CtxCons y tyB ctx)) c ctyC ->
    ctysynth ctx c ctyC
| SynthApp ctx v1 v2 tyA ctyC :
    vtysynth ctx v1 (TyFun tyA ctyC) ->
    vtycheck ctx v2 tyA ->
    ctysynth ctx (App v1 v2) ctyC
| SynthHandle ctx v c ctyC ctyD :
    vtysynth ctx v (TyHandler ctyC ctyD) ->
    ctycheck ctx c ctyC ->
    ctysynth ctx (Handle v c) ctyC
| SynthCAnnot ctx c ctyC :
    ctycheck ctx c ctyC ->
    ctysynth ctx (CAnnot c ctyC) ctyC
(* with htysynth : ctx -> hcases -> sig -> ctype -> Type := *)
with vtycheck : ctx -> val -> vtype -> Type :=
| CheckVBySynth ctx v tyA tyA' :
    vtysynth ctx v tyA' ->
    tyA = tyA' ->
    vtycheck ctx v tyA
| CheckInl ctx v tyA tyB :
    vtycheck ctx v tyA ->
    vtycheck ctx (Inl v) (TySum tyA tyB)
| CheckInr ctx v tyA tyB :
    vtycheck ctx v tyB ->
    vtycheck ctx (Inr v) (TySum tyA tyB)
| CheckPair ctx v1 v2 tyA tyB :
    vtycheck ctx v1 tyA ->
    vtycheck ctx v2 tyB ->
    vtycheck ctx (Pair v1 v2) (TyProd tyA tyB)
| CheckFun ctx x c tyA tyC :
    ctycheck (CtxCons x tyA ctx) c tyC ->
    vtycheck ctx (Fun x c) (TyFun tyA tyC)
| CheckHandler ctx x c_ret h tyA sig eqs ctyD :
    ctycheck (CtxCons x tyA ctx) c_ret ctyD ->
    htycheck ctx h sig ctyD ->
    vtycheck ctx (Handler x c_ret h) (TyHandler (CTy tyA sig eqs) ctyD)
with ctycheck : ctx -> comp -> ctype -> Type :=
| CheckCBySynth ctx c ctyC ctyC' :
    ctysynth ctx c ctyC' ->
    ctyC = ctyC' ->
    ctycheck ctx c ctyC
| CheckSMatch ctx v tyA tyB xl cl xr cr ctyC :
    vtysynth ctx v (TySum tyA tyB) ->
    ctycheck (CtxCons xl tyA ctx) cl ctyC ->
    ctycheck (CtxCons xr tyB ctx) cr ctyC ->
    ctycheck ctx (SMatch v xl cl xr cr) ctyC
| CheckOp ctx op_id v y c tyA_op tyB_op tyA sig eqs :
    get_op_type sig op_id = Some (tyA_op, tyB_op) ->
    vtycheck ctx v tyA_op ->
    ctycheck (CtxCons y tyB_op ctx) c (CTy tyA sig eqs) ->
    ctycheck ctx (Op op_id v y c) (CTy tyA sig eqs)
with htycheck : ctx -> hcases -> sig -> ctype -> Type :=
| CheckNoCases ctx ctyD : htycheck ctx NoCases SigNil ctyD
| CheckOpCases ctx h op_id x k c_op tyA_op tyB_op sig ctyD :
    find_op_case h op_id = None ->
    htycheck ctx h sig ctyD ->
    ctycheck
      (CtxCons x tyA_op (CtxCons k (TyFun tyB_op ctyD) ctx))
      c_op ctyD ->
    htycheck 
      ctx (OpCases h op_id x k c_op)
      (SigCons op_id tyA_op tyB_op sig) ctyD
.