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

with wf_form : ctx -> formula -> Prop :=
| WfVeq Γ A v1 v2 :
    has_vtype Γ v1 A -> has_vtype Γ v2 A ->
    wf_form Γ (Veq A v1 v2)
| WfCeq Γ C c1 c2 :
    has_ctype Γ c1 C -> has_ctype Γ c2 C ->
    wf_form Γ (Ceq C c1 c2)
| WfHeq Γ Σ Σ1 Σ2 D h1 h2 :
    wf_sig Σ -> sig_subtype Σ Σ1 -> sig_subtype Σ Σ2 ->
    has_htype Γ h1 Σ1 D -> has_htype Γ h2 Σ2 D ->
    wf_form Γ (Heq Σ D h1 h2)
| WfTruth Γ : 
    wf_ctx Γ ->
    wf_form Γ Truth
| WfFalsity Γ :
    wf_ctx Γ ->
    wf_form Γ Falsity
| WfAnd φ1 φ2 Γ : 
    wf_form Γ φ1 -> wf_form Γ φ2 ->
    wf_form Γ (And φ1 φ2)
| WfOr φ1 φ2 Γ :
    wf_form Γ φ1 -> wf_form Γ φ2 ->
    wf_form Γ (Or φ1 φ2)
| WfImplies φ1 φ2 Γ :
    wf_form Γ φ1 -> wf_form Γ φ2 ->
    wf_form Γ (Implies φ1 φ2)
| WfForall A φ Γ :
    wf_vtype A -> wf_form (CtxU Γ A) φ ->
    wf_form Γ (Forall A φ)
| WfExists A φ Γ :
    wf_vtype A -> wf_form (CtxU Γ A) φ ->
    wf_form Γ (Exists A φ)

with wf_hyp : ctx -> hypotheses -> Prop :=
| WfHypØ Γ:
    wf_hyp Γ HypØ
| WfHypU Γ Ψ j:
    wf_hyp Γ Ψ ->
    wf_form Γ j ->
    wf_hyp Γ (HypU Ψ j)

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
    (* This is needed for the safety theorem. *)
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
    respects' Γ h Σ D E -> 
    respects Γ h Σ D E 

with respects' : ctx -> hcases -> sig -> ctype -> eqs -> Prop :=
| RespectEqsØ Γ h Σ D : respects' Γ h Σ D EqsØ
| RespectEqsU Γ h Σ D E Γ' Z T1 T2 :
    respects Γ' h Σ D E -> 
    judg (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) HypØ
      (Ceq D
        (handle_t D (ctx_len Γ) (tctx_len Z) h T1) 
        (handle_t D (ctx_len Γ) (tctx_len Z) h T2) ) ->
    respects' Γ' h Σ D (EqsU E Γ Z T1 T2)

with judg : ctx -> hypotheses -> formula -> Prop :=
| WfJudg Γ Ψ φ :
    wf_ctx Γ ->
    wf_form Γ φ ->
    wf_hyp Γ Ψ ->
    judg' Γ Ψ φ ->
    judg Γ Ψ φ

with judg' : ctx -> hypotheses -> formula -> Prop :=
(* - - - - - - - - - - - - - - -  Values - - - - - - - - - - - - - - -  *)
| VeqSym Γ Ψ A v1 v2 : 
    judg Γ Ψ (Veq A v1 v2) -> 
    judg' Γ Ψ (Veq A v2 v1)
| VeqTrans Γ Ψ A v1 v2 v3 : 
    judg Γ Ψ (Veq A v1 v2) -> 
    judg Γ Ψ (Veq A v2 v3) -> 
    judg' Γ Ψ (Veq A v1 v3)
| VeqVar i A Γ Ψ :
    get_vtype Γ i = Some A ->
    judg' Γ Ψ (Veq A (Var i) (Var i))
| VeqUnit Γ Ψ:
    judg' Γ Ψ (Veq TyUnit Unit Unit)
| VeqInt Γ Ψ n:
    judg' Γ Ψ (Veq TyInt (Int n) (Int n))
| VeqPair A B Γ Ψ v1 v1' v2 v2' :
    judg Γ Ψ (Veq A v1 v1') ->
    judg Γ Ψ (Veq B v2 v2') -> 
    judg' Γ Ψ (Veq (TyProd A B) (Pair v1 v2) (Pair v1' v2'))
| VeqLeft A A1 A2 B B1 B2 Γ Ψ v v' :
    judg Γ Ψ (Veq A v v') ->
    vsubtype A1 A -> vsubtype A2 A -> vsubtype B1 B -> vsubtype B2 B ->
    judg' Γ Ψ (Veq (TySum A B) (Left A1 B1 v) (Left A2 B2 v'))
| VeqRight A A1 A2 B B1 B2 Γ Ψ v v' :
    judg Γ Ψ (Veq B v v') ->
    vsubtype A1 A -> vsubtype A2 A -> vsubtype B1 B -> vsubtype B2 B ->
    judg' Γ Ψ (Veq (TySum A B) (Right A1 B1 v) (Right A2 B2 v'))
| VeqNil A A1 A2 Γ Ψ :
    vsubtype A1 A -> vsubtype A2 A ->
    judg' Γ Ψ (Veq (TyList A) (Nil A1) (Nil A2))
| VeqCons A Γ Ψ v v' vs vs':
    judg Γ Ψ (Veq A v v') ->
    judg Γ Ψ (Veq (TyList A) vs vs') ->
    judg' Γ Ψ (Veq (TyList A) (Cons v vs) (Cons v' vs'))
| VeqFun A A1 A2 C Γ Ψ c c':
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq C c c') ->
    vsubtype A A1 -> vsubtype A A2 ->
    judg' Γ Ψ (Veq (TyFun A C) (Fun A1 c) (Fun A2 c'))
| VeqHandler A A1 A2 Σ E D Γ Ψ c c' h h':
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq D c c') ->
    judg Γ Ψ (Heq Σ D h h') ->
    vsubtype A A1 -> vsubtype A A2 ->
    judg' Γ Ψ (Veq (TyHandler (CTy A Σ E) D) (Handler A1 c h) (Handler A2 c' h'))
| VeqSubsume Γ Ψ A A' v1 v2 :
    judg Γ Ψ (Veq A v1 v2) ->
    vsubtype A A' ->
    judg' Γ Ψ (Veq A' v1 v2)
| ηUnit Γ Ψ v:
    judg' Γ Ψ (Veq TyUnit v Unit)
| ηFun A C Γ Ψ f:
    judg' Γ Ψ (Veq (TyFun A C) (Fun A (App (v_shift f 1 0) (Var 0))) f)
(* - - - - - - - - - - - - - - -  Computations - - - - - - - - - - - - - - -  *)
| CeqSym Γ Ψ C c1 c2 : 
    judg Γ Ψ (Ceq C c1 c2) -> 
    judg' Γ Ψ (Ceq C c2 c1)
| CeqTrans Γ Ψ C c1 c2 c3 : 
    judg Γ Ψ (Ceq C c1 c2) ->
    judg Γ Ψ (Ceq C c2 c3) -> 
    judg' Γ Ψ (Ceq C c1 c3)
| CeqRet A Σ E Γ Ψ v v' : 
    judg Γ Ψ (Veq A v v') -> 
    judg' Γ Ψ (Ceq (CTy A Σ E) (Ret v) (Ret v'))
| CeqAbsurd Γ Ψ C C1 C2 v v' :
    csubtype C1 C -> csubtype C2 C ->
    judg' Γ Ψ (Ceq C (Absurd C1 v) (Absurd C2 v'))
| CeqProdMatch Γ Ψ C v v' A B c c':
    judg Γ Ψ (Veq (TyProd A B) v v') ->
    judg (CtxU (CtxU Γ A) B) (hyp_shift Ψ 2 0) (Ceq C c c') ->
    judg' Γ Ψ (Ceq C (ProdMatch v c) (ProdMatch v' c'))
| CeqSumMatch Γ Ψ C v v' A B c1 c1' c2 c2':
    judg Γ Ψ (Veq (TySum A B) v v') ->
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq C c1 c1') ->
    judg (CtxU Γ B) (hyp_shift Ψ 1 0) (Ceq C c2 c2') ->
    judg' Γ Ψ (Ceq C (SumMatch v c1 c2) (SumMatch v' c1' c2'))
| CeqListMatch Γ Ψ C v v' A c1 c1' c2 c2':
    judg Γ Ψ (Veq (TyList A) v v') ->
    judg Γ Ψ (Ceq C c1 c1') ->
    judg (CtxU (CtxU Γ A) (TyList A)) (hyp_shift Ψ 2 0) (Ceq C c2 c2') ->
    judg' Γ Ψ (Ceq C (ListMatch v c1 c2) (ListMatch v' c1' c2'))
| CeqDo A B Σ E Γ Ψ c1 c1' c2 c2':
    judg Γ Ψ (Ceq (CTy A Σ E) c1 c1') ->
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq (CTy B Σ E) c2 c2') ->
    judg' Γ Ψ (Ceq (CTy B Σ E) (Do c1 c2) (Do c1' c2'))
| CeqApp Γ Ψ v1 v1' v2 v2' A C:
    judg Γ Ψ (Veq (TyFun A C) v1 v1') ->
    judg Γ Ψ (Veq A v2 v2') ->
    judg' Γ Ψ (Ceq C (App v1 v2) (App v1' v2'))
| CeqHandle Γ Ψ v v' c c' C D:
    judg Γ Ψ (Veq (TyHandler C D) v v') ->
    judg Γ Ψ (Ceq C c c') ->
    judg' Γ Ψ (Ceq D (Handle v c) (Handle v' c'))
| CeqLetRec Γ Ψ c1 c1' c2 c2' A C D:
    judg (CtxU (CtxU Γ A) (TyFun A C)) (hyp_shift Ψ 2 0) (Ceq C c1 c1') ->
    judg (CtxU Γ (TyFun A C)) (hyp_shift Ψ 1 0) (Ceq D c2 c2') ->
    judg' Γ Ψ (Ceq D (LetRec A C c1 c2) (LetRec A C c1' c2'))
| CeqOp Γ Ψ op v v' c c' A A' B B' Aop Bop Ac Σ E:
    get_op_type Σ op = Some (Aop, Bop) ->
    vsubtype A Aop -> vsubtype A' Aop -> vsubtype Bop B -> vsubtype Bop B' ->
    judg Γ Ψ (Veq Aop v v') ->
    judg (CtxU Γ Bop) (hyp_shift Ψ 1 0) (Ceq (CTy Ac Σ E) c c') ->
    judg' Γ Ψ (Ceq (CTy Ac Σ E) (Op op A B v c) (Op op A' B' v' c'))
| CeqSubsume Γ Ψ C C' c1 c2 :
    judg Γ Ψ (Ceq C c1 c2) ->
    csubtype C C' ->
    judg' Γ Ψ (Ceq C' c1 c2)
| OOTB A Σ E Γ' Ψ I Γ Z T1 T2 c1 c2:
    has_eq E Γ Z T1 T2 ->
    wf_inst Γ' I (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) ->
    c_inst (tmpl_to_comp (CTy A Σ E) (ctx_len Γ) T1) I = c1 ->
    c_inst (tmpl_to_comp (CTy A Σ E) (ctx_len Γ) T2) I = c2 ->
    judg' Γ' Ψ (Ceq (CTy A Σ E) c1 c2)
| βMatchPair v1 v2 c C Γ Ψ: 
    judg' Γ Ψ 
    (Ceq  C
      (ProdMatch (Pair v1 v2) c) 
      (c_subs2_out c v1 v2) )
| βMatchLeft v c1 c2 C A B Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (SumMatch (Left A B v) c1 c2)
      (c_subs_out c1 v) )
| βMatchRight v c1 c2 C A B Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (SumMatch (Right A B v) c1 c2)
      (c_subs_out c2 v) )
| βMatchNil c1 c2 C A Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ListMatch (Nil A) c1 c2)
      c1 )
| βMatchCons v vs c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ListMatch (Cons v vs) c1 c2)
      (c_subs2_out c2 v vs) )
| βApp c v A C Γ Ψ:
    judg' Γ Ψ (Ceq C (App (Fun A c) v) (c_subs_out c v))
| βLetRec c1 c2 A C D Γ Ψ:
    judg' Γ Ψ 
    (Ceq D
      (LetRec A C c1 c2)
      (c_subs_out c2 (Fun A (LetRec A C (c_shift c1 1 2) c1))) )
| βDoRet v c C Γ Ψ:
    judg' Γ Ψ (Ceq C (Do (Ret v) c) (c_subs_out c v))
| βDoOp op A B v c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (Do (Op op A B v c1) c2)
      (Op op A B v (Do c1 (c_shift c2 1 1))) )
| βHandleRet c_r h v A C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (Handle (Handler A c_r h) (Ret v))
      (c_subs_out c_r v) )
| βHandleOp A c_r h op Aop Bop  v c_k c_op C Γ Ψ:
    get_case h op = Some c_op ->
    judg' Γ Ψ 
    (Ceq C
      (Handle (Handler A c_r h) (Op op Aop Bop v c_k))
      (c_subs2_out c_op
        v (Fun Bop (Handle (v_shift (Handler A c_r h) 1 0) c_k)) ) )
| ηEmpty Γ Ψ v n c C C':
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyEmpty)) c C' ->
    csubtype C C' ->
    judg' Γ Ψ (Ceq C' (c_subs c n v) (Absurd C v) )
| ηPair Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyProd A B)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (ProdMatch v (c_subs (c_shift c 2 0) (2+n) (Pair (Var 1) (Var 0)))) )
| ηSum Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TySum A B)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (SumMatch v 
        (c_subs (c_shift c 1 0) (1+n) (Left A B (Var 0))) 
        (c_subs (c_shift c 1 0) (1+n) (Right A B (Var 0)))) )
| ηList Γ Ψ v n c C A:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyList A)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (ListMatch v 
        (c_subs c n (Nil A)) 
        (c_subs (c_shift c 2 0) (2+n) (Cons (Var 1) (Var 0)))) )
| ηDo Γ Ψ c C:
    judg' Γ Ψ (Ceq C (Do c (Ret (Var 0))) c)
| DoLoop Γ Ψ c A C D:
    judg' Γ Ψ (Ceq D 
      (Do (LetRec A C (App (Var 0) Unit) (App (Var 0) Unit) ) c) 
      (LetRec A C (App (Var 0) Unit) (App (Var 0) Unit) ) )
| HandleLoop Γ Ψ v A C D:
    judg' Γ Ψ (Ceq D 
      (Handle v (LetRec A C (App (Var 0) Unit) (App (Var 0) Unit))) 
      (LetRec A C (App (Var 0) Unit) (App (Var 0) Unit)) )
(* - - - - - - - - - - - - - - -  Cases - - - - - - - - - - - - - - -  *)
| HeqSym Γ Ψ Σ D h1 h2 : 
    judg Γ Ψ (Heq Σ D h1 h2) -> 
    judg' Γ Ψ (Heq Σ D h2 h1)
| HeqTrans Γ Ψ Σ D h1 h2 h3 : 
    judg Γ Ψ (Heq Σ D h1 h2) ->
    judg Γ Ψ (Heq Σ D h2 h3) -> 
    judg' Γ Ψ (Heq Σ D h1 h3)
| HeqSigØ D Γ Ψ h1 h2: 
    judg' Γ Ψ (Heq SigØ D h1 h2)
| HeqSigU Σ op A B D Γ Ψ h1 c1 h2 c2:
    get_case h1 op = Some c1 ->
    get_case h2 op = Some c2 ->
    judg (CtxU (CtxU Γ A) (TyFun B D)) (hyp_shift Ψ 2 0) (Ceq D c1 c2) ->
    judg Γ Ψ (Heq Σ D h1 h2) ->
    judg' Γ Ψ (Heq (SigU Σ op A B) D h1 h2)
| HeqExtend Γ Ψ op h1 h2 c1 c2 A A1 A2 B B1 B2 Σ D:
    judg Γ Ψ (Heq Σ D h1 h2) ->
    get_case h1 op = None -> get_case h2 op = None ->
    judg (CtxU (CtxU Γ A) (TyFun B D)) (hyp_shift Ψ 2 0) (Ceq D c1 c2) ->
    judg' Γ Ψ (Heq (SigU Σ op A B) D 
      (CasesU h1 op A1 B1 c1) (CasesU h2 op A2 B2 c2))
(* - - - - - - - - - - - - - - -  General - - - - - - - - - - - - - - -  *)
| IsHyp Γ Ψ φ:
    has_hypothesis Ψ φ ->
    judg' Γ Ψ φ
| TruthIn Γ Ψ :
    judg' Γ Ψ Truth
| FalsityEl Γ Ψ φ:
    judg Γ Ψ Falsity ->
    judg' Γ Ψ φ
| AndIn Γ Ψ φ1 φ2:
    judg Γ Ψ φ1 ->
    judg Γ Ψ φ2 ->
    judg' Γ Ψ (And φ1 φ2)
| AndElLeft Γ Ψ φ1 φ2:
    judg Γ Ψ (And φ1 φ2) ->
    judg' Γ Ψ φ1
| AndElRight Γ Ψ φ1 φ2:
    judg Γ Ψ (And φ1 φ2) ->
    judg' Γ Ψ φ2
| OrLefteft Γ Ψ φ1 φ2:
    judg Γ Ψ φ1 ->
    judg' Γ Ψ (Or φ1 φ2)
| OrRightight Γ Ψ φ1 φ2:
    judg Γ Ψ φ1 ->
    judg' Γ Ψ (Or φ1 φ2)
| OrEl Γ Ψ φ1 φ2 Φ:
    judg Γ Ψ (Or φ1 φ2) ->
    judg Γ Ψ (Implies φ1 Φ) ->
    judg Γ Ψ (Implies φ2 Φ) ->
    judg' Γ Ψ (Implies (Or φ1 φ2) Φ)
| ImpliesIn Γ Ψ φ1 φ2:
    judg Γ (HypU Ψ φ1) φ2 ->
    judg' Γ Ψ (Implies φ1 φ2)
| ImpliesEl Γ Ψ φ1 φ2:
    judg Γ Ψ φ1 ->
    judg Γ Ψ (Implies φ1 φ2) ->
    judg' Γ Ψ φ2
| ForallIn Γ Ψ φ A:
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) φ ->
    judg' Γ Ψ (Forall A φ)
| ForallEl Γ Ψ φ v A:
    judg Γ Ψ (Forall A φ) ->
    has_vtype Γ v A ->
    judg' Γ Ψ (form_subs φ 0 v)
| ExistsIn Γ Ψ φ v A:
    has_vtype Γ v A ->
    judg Γ Ψ (form_subs φ 0 v) ->
    judg' Γ Ψ (Exists A φ)
| ExistsEl Γ Ψ φ Φ A:
    judg Γ Ψ (Exists A φ) ->
    judg (CtxU Γ A) (HypU (hyp_shift Ψ 1 0) φ) (form_shift Φ 1 0) ->
    judg' Γ Ψ Φ
| CompInduction Γ Ψ A Σ E φ :
    (* Base case *)
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) 
      (form_subs (form_shift φ 1 0) 1 (Fun TyUnit (Ret (Var 1)))) ->
    (* Operation case *)
    (forall op Aop Bop,
      get_op_type Σ op = Some (Aop, Bop) ->
      judg
        (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) 
        (HypU (hyp_shift Ψ 2 0)  
          (Forall Bop 
            (form_subs (form_shift φ 3 0) 3 
              (Fun TyUnit (App (Var 2) (Var 1))))))
        (form_subs (form_shift φ 2 0) 2 
          (Fun TyUnit (Op op Aop Bop (Var 2) (App (Var 2) (Var 0)))))
    ) ->
    (* Nontermination case *)
    judg Γ Ψ 
      (form_subs φ 0 
        (Fun TyUnit (LetRec TyUnit (CTy A Σ E)
          (App (Var 0) Unit)
          (App (Var 0) Unit) ))
      ) ->
    (* Conclusion *)
    judg' Γ Ψ (Forall (TyFun TyUnit (CTy A Σ E)) φ)


with wf_inst : ctx -> instantiation -> ctx -> Prop :=
| WfInstØ Γcheck : wf_ctx Γcheck -> wf_inst Γcheck InstØ CtxØ
| WfInstU Γcheck I v Γ A : 
  has_vtype Γcheck v A ->
  wf_inst Γcheck I Γ ->
  wf_inst Γcheck (InstU I v) (CtxU Γ A) 
. 
