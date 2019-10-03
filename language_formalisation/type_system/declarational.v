Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
Require Import syntax syntax_lemmas bidirectional.

Inductive has_vtype : ctx -> val -> vtype -> Prop :=
| TypeUnit Γ : has_vtype Γ Unit TyUnit 
| TypeInt Γ n : has_vtype Γ (Int n) TyInt
| TypeVar Γ name num A :
    get_vtype Γ num = Some A ->
    has_vtype Γ (Var (name, num)) A
| TypePair Γ v1 v2 A B :
    has_vtype Γ v1 A ->
    has_vtype Γ v2 B ->
    has_vtype Γ (Pair v1 v2) (TyΠ A B)
| TypeInl Γ v A B :
    has_vtype Γ v A ->
    has_vtype Γ (Inl v) (TyΣ A B)
| TypeInr Γ v A B :
    has_vtype Γ v B ->
    has_vtype Γ (Inr v) (TyΣ A B)
| TypeFun Γ x c A C :
    has_ctype (CtxU Γ A) c C ->
    has_vtype Γ (Fun x c) (TyFun A C)
| TypeHandler Γ x c_ret h A sig eqs D :
    has_ctype (CtxU Γ A) c_ret D ->
    has_htype Γ h sig D ->
    has_vtype Γ (Handler x c_ret h) (TyHandler (CTy A sig eqs) D)
with has_ctype : ctx -> comp -> ctype -> Prop :=
| TypeRet Γ v A : 
    has_vtype Γ v A ->
    has_ctype Γ (Ret v) (CTy A SigØ EqsØ)
| TypeΠMatch Γ v A B x y c C :
    has_vtype Γ v (TyΠ A B) ->
    has_ctype (CtxU (CtxU Γ A) B) c C ->
    has_ctype Γ (ΠMatch v (x, y) c) C
| TypeApp Γ v1 v2 A C :
    has_vtype Γ v1 (TyFun A C) ->
    has_vtype Γ v2 A ->
    has_ctype Γ (App v1 v2) C
| TypeHandle Γ v c C D :
    has_vtype Γ v (TyHandler C D) ->
    has_ctype Γ c C ->
    has_ctype Γ (Handle v c) D
| TypeLetRec Γ f x A C c1 c2 D:
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    has_ctype (CtxU Γ (TyFun A C)) c2 D ->
    has_ctype Γ (LetRec f x c1 c2) D
| TypeΣMatch Γ v A B xl cl xr cr C :
    has_vtype Γ v (TyΣ A B) ->
    has_ctype (CtxU Γ A) cl C ->
    has_ctype (CtxU Γ B) cr C ->
    has_ctype Γ (ΣMatch v xl cl xr cr) C
| TypeOp Γ op_id v y c A_op B_op A Σ eqs :
    get_op_type Σ op_id = Some (A_op, B_op) ->
    has_vtype Γ v A_op ->
    has_ctype (CtxU Γ B_op) c (CTy A Σ eqs) ->
    has_ctype Γ (Op op_id v y c) (CTy A Σ eqs)
with has_htype : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeCasesØ Γ D : has_htype Γ CasesØ SigØ D
| TypeCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_op_case h op_id = None ->
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ (TyFun B_op D)) A_op) c_op D ->
    has_htype 
      Γ (CasesU h op_id x k c_op)
      (SigU Σ op_id A_op B_op) D
.
