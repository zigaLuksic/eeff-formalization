(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export syntax subtyping substitution.

(* ==================== Template Handling ==================== *)

(* We increase context length so that we don't have to shift h. *)
Fixpoint handle_t D Γ_len Z_len h T :=
  match T with
  | TApp n v => App (Var (Γ_len+n)) v
  | TAbsurd v => Absurd D v
  | TProdMatch v T => 
      ProdMatch v (handle_t D (2+Γ_len) Z_len h T)
  | TSumMatch v T1 T2 => 
      SumMatch v
        (handle_t D (1+Γ_len) Z_len h T1) 
        (handle_t D (1+Γ_len) Z_len h T2)
  | TListMatch v T1 T2 =>
      ListMatch v
        (handle_t D Γ_len Z_len h T1)
        (handle_t D (2+Γ_len) Z_len h T2)
  | TDo c T =>
      Do c (handle_t D (1+Γ_len) Z_len h T)
  | TOp op A B v T =>
      match get_case h op with 
      | Some c_op =>
          c_subs2_out (c_shift c_op (Γ_len + Z_len) 2) 
            v (Fun B (handle_t D (1+Γ_len) Z_len h T))
      | None => 
          (* You shouldn't be here *)
          Op op A B v (handle_t D (1+Γ_len) Z_len h T) 
      end
  end.


Fixpoint tmpl_to_comp C Γ_len T :=
  match T with
  | TApp n v => App (Var (Γ_len+n)) v
  | TAbsurd v => Absurd C v
  | TProdMatch v T => 
      ProdMatch v (tmpl_to_comp C (2+Γ_len) T)
  | TSumMatch v T1 T2 => 
      SumMatch v
        (tmpl_to_comp C (1+Γ_len) T1) 
        (tmpl_to_comp C (1+Γ_len) T2)
  | TListMatch v T1 T2 => 
      ListMatch v
        (tmpl_to_comp C Γ_len T1) 
        (tmpl_to_comp C (2+Γ_len) T2)
  | TDo c T =>
      Do c (tmpl_to_comp C (1+Γ_len) T)
  | TOp op A B v T =>
      Op op A B v (tmpl_to_comp C (1+Γ_len) T)
  end.

(* ==================== Welljudged Judgements ==================== *)

Inductive wf_vtype : vtype -> Prop :=
| WfTyUnit : wf_vtype TyUnit 
| WfTyInt : wf_vtype TyInt
| WfTyEmpty : wf_vtype TyEmpty
| WfTySum A B: wf_vtype A -> wf_vtype B -> wf_vtype (TySum A B)
| WfTyProd A B : wf_vtype A -> wf_vtype B -> wf_vtype (TyProd A B)
| WfTyList A : wf_vtype A -> wf_vtype (TyList A)
| WfTyFun A C : wf_vtype A -> wf_ctype C -> wf_vtype (TyFun A C)
| WfTyHandler C D : wf_ctype C -> wf_ctype D -> wf_vtype (TyHandler C D)

with wf_ctype : ctype -> Prop :=
| WfCTy A Σ E : wf_vtype A -> wf_sig Σ -> wf_eqs E Σ -> wf_ctype (CTy A Σ E)
    
with wf_sig : sig -> Prop :=
| WfSigØ : wf_sig SigØ
| WfSigU Σ op Aop Bop: 
    wf_sig Σ -> get_op_type Σ op = None ->
    wf_vtype Aop -> wf_vtype Bop ->
    wf_sig (SigU Σ op Aop Bop)

with wf_ctx : ctx -> Prop :=
| WfCtxØ : wf_ctx CtxØ
| WfCtxU Γ A : wf_ctx Γ -> wf_vtype A -> wf_ctx (CtxU Γ A)

with wf_tctx : tctx -> Prop :=
| WfTCtxØ : wf_tctx TCtxØ
| WfTCtxU Γ A : wf_tctx Γ -> wf_vtype A -> wf_tctx (TCtxU Γ A)

with wf_t : ctx -> tctx -> tmpl -> sig -> Prop :=
| WfTApp Γ Z n v A Σ : 
    has_vtype Γ v A -> get_ttype Z n = Some A ->
    wf_t Γ Z (TApp n v) Σ
| WfTAbsurd Γ Z v Σ :
    has_vtype Γ v TyEmpty -> 
    wf_t Γ Z (TAbsurd v) Σ 
| WfTProdMatch Γ Z v T A B Σ :
    has_vtype Γ v (TyProd A B) -> wf_t (CtxU (CtxU Γ A) B) Z T Σ -> 
    wf_t Γ Z (TProdMatch v T) Σ
| WfTSumMatch Γ Z v T1 T2 A B Σ :
    has_vtype Γ v (TySum A B) -> 
    wf_t (CtxU Γ A) Z T1 Σ -> wf_t (CtxU Γ B) Z T2 Σ -> 
    wf_t Γ Z (TSumMatch v T1 T2) Σ
| WfTListMatch Γ Z v T1 T2 A Σ :
    has_vtype Γ v (TyList A) -> 
    wf_t Γ Z T1 Σ -> wf_t (CtxU (CtxU Γ A) (TyList A)) Z T2 Σ ->  
    wf_t Γ Z (TListMatch v T1 T2) Σ
| WfTDo Γ Z c T A Σ :
    has_ctype Γ c (CTy A SigØ EqsØ) ->
    wf_t (CtxU Γ A) Z T Σ ->
    wf_t  Γ Z (TDo c T) Σ
| WfTOp Γ Z op Aop Bop v T A B Σ :
    get_op_type Σ op = Some (A, B) -> 
    vsubtype Aop A -> vsubtype B Bop ->
    wf_vtype Aop -> wf_vtype Bop ->
    has_vtype Γ v Aop ->
    wf_t (CtxU Γ Bop) Z T Σ ->
    wf_t Γ Z (TOp op Aop Bop v T) Σ

with wf_eqs : eqs -> sig -> Prop :=
| WfEqsØ Σ : wf_eqs EqsØ Σ
| WfEqsU E Γ Z T1 T2 Σ: 
    wf_eqs E Σ -> wf_ctx Γ -> wf_tctx Z -> wf_sig Σ ->
    wf_t Γ Z T1 Σ -> wf_t Γ Z T2 Σ -> 
    wf_eqs (EqsU E Γ Z T1 T2) Σ


(* ==================== Type Judgements ==================== *)

with has_vtype : ctx -> val -> vtype -> Prop :=
| TypeV Γ v A : 
    wf_ctx Γ ->  wf_vtype A ->
    has_vtype' Γ v A ->
    has_vtype Γ v A

with has_vtype' : ctx -> val -> vtype -> Prop :=
| TypeUnit Γ : 
    has_vtype' Γ Unit TyUnit 
| TypeInt Γ n : 
    has_vtype' Γ (Int n) TyInt
| TypeVar Γ n A :
    get_vtype Γ n = Some A ->
    has_vtype' Γ (Var n) A
| TypePair Γ v1 v2 A B :
    has_vtype Γ v1 A ->
    has_vtype Γ v2 B ->
    has_vtype' Γ (Pair v1 v2) (TyProd A B)
| TypeLeft Γ v A B :
    has_vtype Γ v A ->
    has_vtype' Γ (Left A B v) (TySum A B)
| TypeRight Γ v A B :
    has_vtype Γ v B ->
    has_vtype' Γ (Right A B v) (TySum A B)
| TypeNil Γ A :
    has_vtype' Γ (Nil A) (TyList A)
| TypeCons Γ v vs A :
    has_vtype Γ v A ->
    has_vtype Γ vs (TyList A) ->
    has_vtype' Γ (Cons v vs) (TyList A)
| TypeFun Γ c A C :
    has_ctype (CtxU Γ A) c C ->
    has_vtype' Γ (Fun A c) (TyFun A C)
| TypeHandler Γ cr h A Σ E D :
    has_ctype (CtxU Γ A) cr D ->
    has_htype Γ h Σ D -> 
    respects Γ h Σ D E ->
    has_vtype' Γ (Handler A cr h) (TyHandler (CTy A Σ E) D)
| TypeVSubsume Γ v A A' :
    has_vtype Γ v A ->
    vsubtype A A' -> 
    has_vtype' Γ v A'

with has_ctype : ctx -> comp -> ctype -> Prop :=
| TypeC Γ c C :
    wf_ctx Γ -> wf_ctype C ->
    has_ctype' Γ c C ->
    has_ctype Γ c C

with has_ctype' : ctx -> comp -> ctype -> Prop :=
| TypeRet Γ v A : 
    has_vtype Γ v A ->
    has_ctype' Γ (Ret v) (CTy A SigØ EqsØ)
| TypeAbsurd Γ v C :
    has_vtype Γ v TyEmpty -> 
    has_ctype' Γ (Absurd C v) C
| TypeProdMatch Γ v A B c C :
    has_vtype Γ v (TyProd A B) ->
    has_ctype (CtxU (CtxU Γ A) B) c C ->
    has_ctype' Γ (ProdMatch v c) C
| TypeSumMatch Γ v A B c1 c2 C :
    has_vtype Γ v (TySum A B) ->
    has_ctype (CtxU Γ A) c1 C ->
    has_ctype (CtxU Γ B) c2 C ->
    has_ctype' Γ (SumMatch v c1 c2) C
| TypeListMatch Γ v A c1 c2 C :
    has_vtype Γ v (TyList A) ->
    has_ctype Γ c1 C ->
    has_ctype (CtxU (CtxU Γ A) (TyList A)) c2 C ->
    has_ctype' Γ (ListMatch v c1 c2) C
| TypeDo Γ c1 c2 A B Σ E :
    has_ctype Γ c1 (CTy A Σ E) ->
    has_ctype (CtxU Γ A) c2 (CTy B Σ E) ->
    has_ctype' Γ (Do c1 c2) (CTy B Σ E)
| TypeApp Γ v1 v2 A C :
    has_vtype Γ v1 (TyFun A C) ->
    has_vtype Γ v2 A ->
    has_ctype' Γ (App v1 v2) C
| TypeHandle Γ v c C D :
    has_vtype Γ v (TyHandler C D) ->
    has_ctype Γ c C ->
    has_ctype' Γ (Handle v c) D
| TypeLetRec Γ A C c1 c2 D:
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    has_ctype (CtxU Γ (TyFun A C)) c2 D ->
    has_ctype' Γ (LetRec A C c1 c2) D
| TypeOp Γ op v c Aop Bop Aop' Bop' A Σ E :
    get_op_type Σ op = Some (Aop', Bop') -> 
    vsubtype Aop Aop' -> vsubtype Bop' Bop ->
    has_vtype Γ v Aop ->
    has_ctype (CtxU Γ Bop) c (CTy A Σ E) ->
    has_ctype' Γ (Op op Aop Bop v c) (CTy A Σ E)
| TypeCSubsume Γ c C C' :
    has_ctype Γ c C -> 
    csubtype C C' -> 
    has_ctype' Γ c C'

with has_htype : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeH Γ h Σ D : 
    wf_ctx Γ -> wf_sig Σ -> wf_ctype D ->
    has_htype' Γ h Σ D -> 
    has_htype Γ h Σ D

with has_htype' : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeCasesØ Γ D : has_htype' Γ (CasesØ D) SigØ D
| TypeCasesU Γ h op c A B Σ D :
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ A) (TyFun B D)) c D ->
    has_htype' Γ (CasesU h op A B c) (SigU Σ op A B) D

(* ==================== Logic Judgements ==================== *)

with respects : ctx -> hcases -> sig -> ctype -> eqs -> Prop :=
| Respects Γ h Σ D E :
    wf_ctx Γ -> wf_sig Σ -> wf_ctype D -> wf_eqs E Σ ->
    has_htype Γ h Σ D ->  respects' Γ h Σ D E -> 
    respects Γ h Σ D E 

with respects' : ctx -> hcases -> sig -> ctype -> eqs -> Prop :=
| RespectEqsØ Γ h Σ D : respects' Γ h Σ D EqsØ
| RespectEqsU Γ h Σ D E Γ' Z T1 T2 :
    respects Γ' h Σ D E -> 
    ceq D (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
      (handle_t D (ctx_len Γ) (tctx_len Z) h T1) 
      (handle_t D (ctx_len Γ) (tctx_len Z) h T2) ->
    respects' Γ' h Σ D (EqsU E Γ Z T1 T2)

with veq : vtype -> ctx -> val -> val -> Prop := 
| Veq A Γ v1 v2 : 
  has_vtype Γ v1 A -> has_vtype Γ v2 A ->
  veq' A Γ v1 v2 -> 
  veq A Γ v1 v2

with veq': vtype -> ctx -> val -> val -> Prop :=
| VeqSym A Γ v1 v2 : 
    veq A Γ v1 v2 -> 
    veq' A Γ v2 v1
| VeqTrans A Γ v1 v2 v3 : 
    veq A Γ v1 v2 -> veq A Γ v2 v3 -> 
    veq' A Γ v1 v3
| VeqVar i A A' Γ :
    get_vtype Γ i = Some A' -> 
    vsubtype A' A -> (* Extra subtyping *)
    veq' A Γ (Var i) (Var i)
| VeqUnit Γ:
    veq' TyUnit Γ Unit Unit
| VeqInt Γ n:
    veq' TyInt Γ (Int n) (Int n)
| VeqPair A B Γ v1 v1' v2 v2' :
    veq A Γ v1 v1' ->
    veq B Γ v2 v2' -> 
    veq' (TyProd A B) Γ (Pair v1 v2) (Pair v1' v2')
| VeqLeft A A1 A2 B B1 B2 Γ v v' :
    veq A Γ v v' ->
    veq' (TySum A B) Γ (Left A1 B1 v) (Left A2 B2 v')
| VeqRight A A1 A2 B B1 B2 Γ v v' :
    veq B Γ v v' ->
    veq' (TySum A B) Γ (Right A1 B1 v) (Right A2 B2 v')
| VeqNil A A1 A2 Γ :
    veq' (TyList A) Γ (Nil A1) (Nil A2)
| VeqCons A Γ v v' vs vs':
    veq A Γ v v' ->
    veq (TyList A) Γ vs vs' ->
    veq' (TyList A) Γ (Cons v vs) (Cons v' vs')
| VeqFun A A1 A2 C Γ c c':
    ceq C (CtxU Γ A) c c' ->
    veq' (TyFun A C) Γ (Fun A1 c) (Fun A2 c')
| VeqHandler A A1 A2 Σ Σ' E D D' Γ c c' h h':
    ceq D' (CtxU Γ A) c c' ->
    heq Σ' D' Γ h h' ->
    respects Γ h Σ' D' E -> respects Γ h' Σ' D' E ->
    sig_subtype Σ Σ' -> csubtype D' D -> (* Extra subtyping *)
    veq' (TyHandler (CTy A Σ E) D) Γ (Handler A1 c h) (Handler A2 c' h')
| ηUnit Γ v:
    veq' TyUnit Γ v Unit
| ηFun A A' C Γ f:
    veq' (TyFun A C) Γ (Fun A' (App (v_shift f 1 0) (Var 0))) f


with ceq : ctype -> ctx -> comp -> comp -> Prop := 
| Ceq C Γ c1 c2 : 
    has_ctype Γ c1 C -> has_ctype Γ c2 C ->
    ceq' C Γ c1 c2 -> 
    ceq C Γ c1 c2

with ceq' : ctype -> ctx -> comp -> comp -> Prop := 
| CeqSym C Γ c1 c2 : 
    ceq C Γ c1 c2 -> 
    ceq' C Γ c2 c1
| CeqTrans C Γ c1 c2 c3 : 
    ceq C Γ c1 c2 ->
    ceq C Γ c2 c3 -> 
    ceq' C Γ c1 c3
| CeqRet A Σ E Γ v v' : 
    veq A Γ v v' -> 
    ceq' (CTy A Σ E) Γ (Ret v) (Ret v')
| CeqAbsurd C C1 C2 Γ v v' :
    ceq' C Γ (Absurd C1 v) (Absurd C2 v')
| CeqProdMatch Γ C v v' A B c c':
    veq (TyProd A B) Γ v v' ->
    ceq C (CtxU (CtxU Γ A) B) c c' ->
    ceq' C Γ (ProdMatch v c) (ProdMatch v' c')
| CeqSumMatch Γ C v v' A B c1 c1' c2 c2':
    veq (TySum A B) Γ v v' ->
    ceq C (CtxU Γ A) c1 c1' ->
    ceq C (CtxU Γ B) c2 c2' ->
    ceq' C Γ (SumMatch v c1 c2) (SumMatch v' c1' c2')
| CeqListMatch Γ C v v' A c1 c1' c2 c2':
    veq (TyList A) Γ v v' ->
    ceq C Γ c1 c1' ->
    ceq C (CtxU (CtxU Γ A) (TyList A)) c2 c2' ->
    ceq' C Γ (ListMatch v c1 c2) (ListMatch v' c1' c2')
| CeqDo A B Σ E Γ c1 c1' c2 c2':
    ceq (CTy A Σ E) Γ c1 c1' ->
    ceq (CTy B Σ E) (CtxU Γ A) c2 c2' ->
    ceq' (CTy B Σ E) Γ (Do c1 c2) (Do c1' c2')
| CeqApp Γ v1 v1' v2 v2' A C:
    veq (TyFun A C) Γ v1 v1' ->
    veq A Γ v2 v2' ->
    ceq' C Γ (App v1 v2) (App v1' v2')
| CeqHandle Γ v v' c c' C D:
    veq (TyHandler C D) Γ v v' ->
    ceq C Γ c c' ->
    ceq' D Γ (Handle v c) (Handle v' c')
| CeqLetRec Γ c1 c1' c2 c2' A C D:
    ceq C (CtxU (CtxU Γ A) (TyFun A C)) c1 c1' ->
    ceq D (CtxU Γ (TyFun A C)) c2 c2' ->
    ceq' D Γ (LetRec A C c1 c2) (LetRec A C c1' c2')
| CeqOp Γ op v v' c c' A A' Aop B B' Bop Ac Σ E:
    get_op_type Σ op = Some (Aop, Bop) ->
    veq Aop Γ v v' ->
    ceq (CTy Ac Σ E) (CtxU Γ Bop) c c' ->
    ceq' (CTy Ac Σ E) Γ (Op op A B v c) (Op op A' B' v' c')
| OOTB A Σ E C Γ' I Γ Z T1 T2 c1 c2:
    (* Extra subtyping *)
    csubtype (CTy A Σ E) C -> wf_ctype (CTy A Σ E) ->
    has_eq E Γ Z T1 T2 ->
    wf_inst Γ' I (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) ->
    c_inst (tmpl_to_comp (CTy A Σ E) (ctx_len Γ) T1) I = c1 ->
    c_inst (tmpl_to_comp (CTy A Σ E) (ctx_len Γ) T2) I = c2 ->
    ceq' C Γ' c1 c2
| βMatchPair v1 v2 c C Γ: 
    ceq' C Γ
      (ProdMatch (Pair v1 v2) c) 
      (c_subs2_out c v1 v2)
| βMatchLeft v c1 c2 C A B Γ:
    ceq' C Γ
      (SumMatch (Left A B v) c1 c2)
      (c_subs_out c1 v)
| βMatchRight v c1 c2 C A B Γ:
    ceq' C Γ 
      (SumMatch (Right A B v) c1 c2)
      (c_subs_out c2 v)
| βMatchNil c1 c2 A C Γ:
    ceq' C Γ
      (ListMatch (Nil A) c1 c2)
      c1
| βMatchCons v vs c1 c2 C Γ:
    ceq' C Γ
      (ListMatch (Cons v vs) c1 c2)
      (c_subs2_out c2 v vs)
| βApp c v A C Γ:
    ceq' C Γ (App (Fun A c) v) (c_subs_out c v)
| βLetRec c1 c2 A C D Γ:
    ceq' D Γ
      (LetRec A C c1 c2)
      (c_subs_out c2 (Fun A (LetRec A C (c_shift c1 1 2) c1)))
| βDoRet v c C Γ:
    ceq' C Γ (Do (Ret v) c) (c_subs_out c v)
| βDoOp op v c1 c2 Aop Bop C Γ:
    ceq' C Γ
      (Do (Op op Aop Bop v c1) c2)
      (Op op Aop Bop v (Do c1 (c_shift c2 1 1)))
| βHandleRet c_r h v A C Γ:
    ceq' C Γ
      (Handle (Handler A c_r h) (Ret v))
      (c_subs_out c_r v)
| βHandleOp c_r h op Aop Bop v c_k c_op A C Γ:
    get_case h op = Some c_op ->
    ceq' C Γ
      (Handle (Handler A c_r h) (Op op Aop Bop v c_k))
      (c_subs2_out c_op
        v (Fun Bop (Handle (v_shift (Handler A c_r h) 1 0) c_k)) )
| ηEmpty Γ v n c C C':
    (* Extra subtyping *)
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyEmpty)) c C ->
    ceq' C' Γ (c_subs c n v) (Absurd C v)
| ηPair Γ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyProd A B)) c C ->
    ceq' C Γ (c_subs c n v)
      (ProdMatch v (c_subs (c_shift c 2 0) (2+n) (Pair (Var 1) (Var 0))))
| ηSum Γ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TySum A B)) c C ->
    ceq' C Γ (c_subs c n v) 
      (SumMatch v 
        (c_subs (c_shift c 1 0) (1+n) (Left A B (Var 0))) 
        (c_subs (c_shift c 1 0) (1+n) (Right A B (Var 0))))
| ηList Γ v n c C A:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyList A)) c C ->
    ceq' C Γ (c_subs c n v) 
      (ListMatch v 
        (c_subs c n (Nil A)) 
        (c_subs (c_shift c 2 0) (2+n) (Cons (Var 1) (Var 0))))
| ηDo Γ c C:
    ceq' C Γ (Do c (Ret (Var 0))) c

with heq : sig -> ctype -> ctx -> hcases -> hcases -> Prop :=
| Heq Σ Σ1 Σ2 D Γ h1 h2 : 
    wf_sig Σ -> sig_subtype Σ Σ1 -> sig_subtype Σ Σ2 ->
    has_htype Γ h1 Σ1 D -> has_htype Γ h2 Σ2 D ->
    heq' Σ D Γ h1 h2 -> 
    heq Σ D Γ h1 h2
    
with heq' : sig -> ctype -> ctx -> hcases -> hcases -> Prop :=
| HeqSigØ D Γ h1 h2: 
    heq' SigØ D Γ h1 h2
| HeqSigU Σ op A B D Γ h1 c1 h2 c2:
    get_case h1 op = Some c1 ->
    get_case h2 op = Some c2 ->
    ceq D (CtxU (CtxU Γ A) (TyFun B D)) c1 c2 ->
    heq Σ D Γ h1 h2 ->
    heq' (SigU Σ op A B) D Γ h1 h2

with wf_inst : ctx -> instantiation -> ctx -> Prop :=
| WfInstØ Γcheck : wf_ctx Γcheck -> wf_inst Γcheck InstØ CtxØ
| WfInstU Γcheck I v Γ A : 
  has_vtype Γcheck v A ->
  wf_inst Γcheck I Γ ->
  wf_inst Γcheck (InstU I v) (CtxU Γ A) 
.
