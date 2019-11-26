(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export syntax syntax_lemmas subtyping substitution.

(* ==================== Template Handling ==================== *)

(* We increase context length so that we don't have to shift h. *)
Fixpoint handle_t Γ_len Z_len h T :=
  match T with
  | TApp x v => App (Var x) (Sub.v_shift v Z_len 0)
  | TAbsurd v => Absurd (Sub.v_shift v Z_len 0)
  | TΠMatch v x y T => 
      ΠMatch (Sub.v_shift v Z_len 0) x y 
        (handle_t (2+Γ_len) Z_len h T)
  | TΣMatch v x T1 y T2 => 
      ΣMatch (Sub.v_shift v Z_len 0)
        x (handle_t (1+Γ_len) Z_len h T1) 
        y (handle_t (1+Γ_len) Z_len h T2)
  | TOp op v y T =>
      match find_case h op with 
      | Some (x, k, c_op) => 
          (c_subs2_out (Sub.c_shift c_op (Γ_len + Z_len) 0) 
            (Fun y (handle_t (1+Γ_len) Z_len h T)) 
            (Sub.v_shift v Z_len 0))
      | None => Op op v y (handle_t (1+Γ_len) Z_len h T)
      end
  end.

(* ==================== Wellformed Judgements ==================== *)

Inductive wf_vtype : vtype -> Prop :=
| WfUnit : wf_vtype TyUnit 
| WfInt : wf_vtype TyInt
| WfEmpty : wf_vtype TyØ
| WfTyΣ A B: wf_vtype A -> wf_vtype B -> wf_vtype (TyΣ A B)
| WfTyΠ A B : wf_vtype A -> wf_vtype B -> wf_vtype (TyΠ A B)
| WfTyFun A C : wf_vtype A -> wf_ctype C -> wf_vtype (TyFun A C)
| WfTyHandler C D : wf_ctype C -> wf_ctype D -> wf_vtype (TyHandler C D)

with wf_ctype : ctype -> Prop :=
| WfCTy A Σ E : wf_vtype A -> wf_sig Σ -> wf_eqs E Σ -> wf_ctype (CTy A Σ E)
    
with wf_sig : sig -> Prop :=
| WfSigØ : wf_sig SigØ
| WfSigU Σ op Aop Bop: 
    wf_sig Σ -> get_op_type Σ op = None ->
    wf_vtype Aop -> wf_vtype Bop -> wf_sig (SigU Σ op Aop Bop)

with wf_ctx : ctx -> Prop :=
| WfCtxØ : wf_ctx CtxØ
| WfCtxU Γ A : wf_ctx Γ -> wf_vtype A -> wf_ctx (CtxU Γ A)

with wf_tctx : tctx -> Prop :=
| WfTCtxØ : wf_tctx TCtxØ
| WfTCtxU Γ A : wf_tctx Γ -> wf_vtype A -> wf_tctx (TCtxU Γ A)

with wf_t : ctx -> tctx -> tmpl -> sig -> Prop :=
| WfTApp Γ Z name num v A Σ : 
    has_vtype Γ v A -> get_ttype Z num = Some A ->
    wf_t Γ Z (TApp (name, num) v) Σ
| WfTAbsurd Γ Z v Σ :
    has_vtype Γ v TyØ -> wf_t Γ Z (TAbsurd v) Σ 
| WfTΠMatch Γ Z v A B x y T Σ :
    has_vtype Γ v (TyΠ A B) -> wf_t (CtxU (CtxU Γ A) B) Z T Σ -> 
    wf_t Γ Z (TΠMatch v x y T) Σ
| WfTΣMatch Γ Z v x A Tl y B Tr Σ :
    has_vtype Γ v (TyΣ A B) -> wf_t (CtxU Γ A) Z Tl Σ -> 
    wf_t (CtxU Γ B) Z Tr Σ -> wf_t Γ Z (TΣMatch v x Tl y Tr) Σ
| WfTOp Γ Z op A_op B_op v y T Σ :
    get_op_type Σ op = Some (A_op, B_op) -> has_vtype Γ v A_op ->
    wf_t (CtxU Γ B_op) Z T Σ -> wf_t Γ Z (TOp op v y T) Σ

with wf_eqs : eqs -> sig -> Prop :=
| WfEqsØ Σ : wf_eqs EqsØ Σ
| WfEqsU E Γ Z T1 T2 Σ: 
    wf_eqs E Σ -> wf_ctx Γ -> wf_tctx Z -> wf_sig Σ ->
    wf_t Γ Z T1 Σ -> wf_t Γ Z T2 Σ -> 
    wf_eqs (EqsU E Γ Z T1 T2) Σ

(* ==================== Type Judgements ==================== *)

with has_vtype : ctx -> val -> vtype -> Prop :=
| TypeV Γ v A : wf_ctx Γ ->  wf_vtype A -> has_vtype' Γ v A -> has_vtype Γ v A

with has_vtype' : ctx -> val -> vtype -> Prop :=
| TypeUnit Γ : has_vtype' Γ Unit TyUnit 
| TypeInt Γ n : has_vtype' Γ (Int n) TyInt
| TypeVar Γ x n A :
    get_vtype Γ n = Some A ->
    has_vtype' Γ (Var (x, n)) A
| TypePair Γ v1 v2 A B :
    has_vtype Γ v1 A ->
    has_vtype Γ v2 B ->
    has_vtype' Γ (Pair v1 v2) (TyΠ A B)
| TypeInl Γ v A B :
    has_vtype Γ v A ->
    has_vtype' Γ (Inl v) (TyΣ A B)
| TypeInr Γ v A B :
    has_vtype Γ v B ->
    has_vtype' Γ (Inr v) (TyΣ A B)
| TypeFun Γ x c A C :
    has_ctype (CtxU Γ A) c C ->
    has_vtype' Γ (Fun x c) (TyFun A C)
| TypeHandler Γ x c_ret h A Σ E D :
    has_ctype (CtxU Γ A) c_ret D ->
    has_htype Γ h Σ D -> respects Γ h Σ D E ->
    has_vtype' Γ (Handler x c_ret h) (TyHandler (CTy A Σ E) D)
| TypeVSubtype Γ v A A' :
    has_vtype Γ v A -> vsubtype A A' -> has_vtype' Γ v A'

with has_ctype : ctx -> comp -> ctype -> Prop :=
| TypeC Γ c C : wf_ctx Γ -> wf_ctype C -> has_ctype' Γ c C -> has_ctype Γ c C

with has_ctype' : ctx -> comp -> ctype -> Prop :=
| TypeRet Γ v A : 
    has_vtype Γ v A ->
    has_ctype' Γ (Ret v) (CTy A SigØ EqsØ)
| TypeAbsurd Γ v C :
    has_vtype Γ v TyØ -> has_ctype' Γ (Absurd v) C
| TypeΠMatch Γ v A B x y c C :
    has_vtype Γ v (TyΠ A B) ->
    has_ctype (CtxU (CtxU Γ A) B) c C ->
    has_ctype' Γ (ΠMatch v x y c) C
| TypeΣMatch Γ v A B xl cl xr cr C :
    has_vtype Γ v (TyΣ A B) ->
    has_ctype (CtxU Γ A) cl C ->
    has_ctype (CtxU Γ B) cr C ->
    has_ctype' Γ (ΣMatch v xl cl xr cr) C
| TypeDoBind Γ x c1 c2 A B Σ E :
    has_ctype Γ c1 (CTy A Σ E) ->
    has_ctype (CtxU Γ A) c2 (CTy B Σ E) ->
    has_ctype' Γ (DoBind x c1 c2) (CTy B Σ E)
| TypeApp Γ v1 v2 A C :
    has_vtype Γ v1 (TyFun A C) ->
    has_vtype Γ v2 A ->
    has_ctype' Γ (App v1 v2) C
| TypeHandle Γ v c C D :
    has_vtype Γ v (TyHandler C D) ->
    has_ctype Γ c C ->
    has_ctype' Γ (Handle v c) D
| TypeLetRec Γ f x A C c1 c2 D:
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    has_ctype (CtxU Γ (TyFun A C)) c2 D ->
    has_ctype' Γ (LetRec f x c1 c2) D
| TypeOp Γ op_id v y c A_op B_op A Σ E :
    get_op_type Σ op_id = Some (A_op, B_op) ->
    has_vtype Γ v A_op ->
    has_ctype (CtxU Γ B_op) c (CTy A Σ E) ->
    has_ctype' Γ (Op op_id v y c) (CTy A Σ E)
| TypeCSubtype Γ c C C' :
    has_ctype Γ c C -> csubtype C C' -> has_ctype' Γ c C'

with has_htype : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeH Γ h Σ D : 
    wf_ctx Γ -> wf_sig Σ -> wf_ctype D -> has_htype' Γ h Σ D -> 
    has_htype Γ h Σ D

with has_htype' : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeCasesØ Γ D : has_htype' Γ CasesØ SigØ D
| TypeCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_case h op_id = None ->
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ (TyFun B_op D)) A_op) c_op D ->
    has_htype' Γ (CasesU h op_id x k c_op) (SigU Σ op_id A_op B_op) D

(* ==================== Logic Judgements ==================== *)

with respects : ctx -> hcases -> sig -> ctype -> eqs -> Prop :=
| Respects Γ h Σ D E :
    wf_ctx Γ -> wf_sig Σ -> wf_ctype D -> wf_eqs E Σ ->
    respects' Γ h Σ D E -> 
    respects Γ h Σ D E 

with respects' : ctx -> hcases -> sig -> ctype -> eqs -> Prop :=
| RespectEqsØ Γ h Σ D : respects' Γ h Σ D EqsØ
| RespectEqsU Γ h Σ D E Γ' Z T1 T2 :
    respects Γ h Σ D E -> 
    ceq D (join_ctx_tctx (join_ctxs Γ Γ') Z D)
      (handle_t (ctx_len Γ') (tctx_len Z) h T1) 
      (handle_t (ctx_len Γ') (tctx_len Z) h T2) ->
    respects' Γ h Σ D (EqsU E Γ' Z T1 T2)

with veq : vtype -> ctx -> val -> val -> Prop := 
| Veq A Γ v1 v2 : wf_vtype A -> wf_ctx Γ -> veq' A Γ v1 v2 -> veq A Γ v1 v2

with veq': vtype -> ctx -> val -> val -> Prop :=
| VRefl A Γ v1 v2 : v1 = v2 -> veq' A Γ v1 v2
| VSym A Γ v1 v2 : veq A Γ v1 v2 -> veq' A Γ v2 v1
| VTrans A Γ v1 v2 v3 : veq A Γ v1 v2 -> veq A Γ v2 v3 -> veq' A Γ v1 v3
| EqPair A B Γ v1 v1' v2 v2' :
    veq A Γ v1 v1' -> veq A Γ v2 v2' -> 
    veq' (TyΠ A B) Γ (Pair v1 v2) (Pair v1' v2')

with ceq : ctype -> ctx -> comp -> comp -> Prop := 
| Ceq C Γ c1 c2 : wf_ctype C -> wf_ctx Γ -> ceq' C Γ c1 c2 -> ceq C Γ c1 c2

with ceq' : ctype -> ctx -> comp -> comp -> Prop := 
| CRefl C Γ c1 c2 : c1 = c2 -> ceq' C Γ c1 c2
| CSym A Γ c1 c2 : ceq A Γ c1 c2 -> ceq' A Γ c2 c1
| CTrans C Γ c1 c2 c3 : ceq C Γ c1 c2 -> ceq C Γ c2 c3 -> ceq' C Γ c1 c3
.
