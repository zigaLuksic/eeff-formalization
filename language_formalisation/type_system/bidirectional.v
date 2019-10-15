(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Import syntax.

Inductive ann_val : Type :=
| Ann_Var : var_id -> ann_val
| Ann_Unit : ann_val
| Ann_Int : Z.t -> ann_val
| Ann_Inl : ann_val -> ann_val
| Ann_Inr : ann_val -> ann_val
| Ann_Pair : ann_val -> ann_val -> ann_val
| Ann_Fun : var_name -> ann_comp -> ann_val
| Ann_Handler : var_name -> ann_comp -> ann_hcases -> ann_val
| Ann_Val : ann_val -> vtype -> ann_val

with ann_comp : Type :=
| Ann_Ret : ann_val -> ann_comp
| Ann_ΠMatch :
    ann_val -> var_name * var_name -> ann_comp -> ann_comp (* x~1 y~0 *)
| Ann_ΣMatch :
    ann_val -> var_name -> ann_comp -> var_name -> ann_comp -> ann_comp
| Ann_App : ann_val -> ann_val -> ann_comp
| Ann_Op : op_id -> ann_val -> var_name -> ann_comp -> ann_comp (* x~1 k~0 *)
| Ann_LetRec :
    var_name -> var_name -> vtype
    -> ann_comp -> ann_comp -> ann_comp (* f~0 x~1 *)
| Ann_DoBind : var_name -> ann_comp -> ann_comp -> ann_comp
| Ann_Handle : ann_val -> ann_comp -> ann_comp
| Ann_Comp : ann_comp -> ctype -> ann_comp

with ann_hcases : Type :=
| Ann_CasesØ : ann_hcases
| Ann_CasesU :
    ann_hcases -> op_id -> var_name -> var_name -> ann_comp -> ann_hcases
.

Fixpoint find_op_ann_case (h : ann_hcases) (op : op_id) 
  : option (var_name * var_name * ann_comp) :=
  match h with
  | Ann_CasesØ => None
  | Ann_CasesU h_others op' x_op k_op c_op =>
      if op == op' then Some (x_op, k_op, c_op)
      else find_op_ann_case h_others op
  end.

Inductive vsynth : ctx -> ann_val -> vtype -> Prop :=
| SynthUnit Γ : vsynth Γ Ann_Unit TyUnit 
| SynthInt Γ n : vsynth Γ (Ann_Int n) TyInt
| SynthVar Γ name num A :
    get_vtype Γ num = Some A ->
    vsynth Γ (Ann_Var (name, num)) A
| SynthPair Γ v1 v2 A B :
    vsynth Γ v1 A ->
    vsynth Γ v2 B ->
    vsynth Γ (Ann_Pair v1 v2) (TyΠ A B)
| SynthVAnnot Γ v A :
    vcheck Γ v A ->
    vsynth Γ (Ann_Val v A) A

with csynth : ctx -> ann_comp -> ctype -> Prop :=
| SynthRet Γ v A : 
    vsynth Γ v A ->
    csynth Γ (Ann_Ret v) (CTy A SigØ EqsØ)
| SynthΠMatch Γ v A B x y c C :
    vsynth Γ v (TyΠ A B) ->
    csynth (CtxU (CtxU Γ A) B) c C ->
    csynth Γ (Ann_ΠMatch v (x, y) c) C
| SynthApp Γ v1 v2 A C :
    vsynth Γ v1 (TyFun A C) ->
    vcheck Γ v2 A ->
    csynth Γ (Ann_App v1 v2) C
| SynthHandle Γ v c C D :
    vsynth Γ v (TyHandler C D) ->
    ccheck Γ c C ->
    csynth Γ (Ann_Handle v c) D
| SynthCAnnot Γ c C :
    ccheck Γ c C ->
    csynth Γ (Ann_Comp c C) C
| SynthLetRec Γ f x A C c1 c2 D:
    ccheck (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    csynth (CtxU Γ (TyFun A C)) c2 D ->
    csynth Γ (Ann_LetRec f x (TyFun A C) c1 c2) D

with vcheck : ctx -> ann_val -> vtype -> Prop :=
| CheckVBySynth Γ v A : vsynth Γ v A -> vcheck Γ v A
| CheckInl Γ v A B :
    vcheck Γ v A ->
    vcheck Γ (Ann_Inl v) (TyΣ A B)
| CheckInr Γ v A B :
    vcheck Γ v B ->
    vcheck Γ (Ann_Inr v) (TyΣ A B)
| CheckFun Γ x c A C :
    ccheck (CtxU Γ A) c C ->
    vcheck Γ (Ann_Fun x c) (TyFun A C)
| CheckHandler Γ x c_ret h A Σ eqs D :
    ccheck (CtxU Γ A) c_ret D ->
    hcheck Γ h Σ D ->
    vcheck Γ (Ann_Handler x c_ret h) (TyHandler (CTy A Σ eqs) D)

with ccheck : ctx -> ann_comp -> ctype -> Prop :=
| CheckCBySynth Γ c C : csynth Γ c C -> ccheck Γ c C
| CheckΣMatch Γ v A B xl cl xr cr C :
    vsynth Γ v (TyΣ A B) ->
    ccheck (CtxU Γ A) cl C ->
    ccheck (CtxU Γ B) cr C ->
    ccheck Γ (Ann_ΣMatch v xl cl xr cr) C
| CheckDoBind Γ x c1 c2 A B Σ eqs :
    csynth Γ c1 (CTy A Σ eqs) ->
    ccheck (CtxU Γ A) c2 (CTy B Σ eqs) ->
    ccheck Γ (Ann_DoBind x c1 c2) (CTy B Σ eqs)
| CheckOp Γ op_id v y c A_op B_op A Σ eqs :
    get_op_type Σ op_id = Some (A_op, B_op) ->
    vcheck Γ v A_op ->
    ccheck (CtxU Γ B_op) c (CTy A Σ eqs) ->
    ccheck Γ (Ann_Op op_id v y c) (CTy A Σ eqs)

with hcheck : ctx -> ann_hcases -> sig -> ctype -> Prop :=
| CheckCasesØ Γ D : hcheck Γ Ann_CasesØ SigØ D
| CheckCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_op_ann_case h op_id = None ->
    hcheck Γ h Σ D ->
    ccheck (CtxU (CtxU Γ (TyFun B_op D)) A_op) c_op D ->
    hcheck 
      Γ (Ann_CasesU h op_id x k c_op)
      (SigU Σ op_id A_op B_op) D
.