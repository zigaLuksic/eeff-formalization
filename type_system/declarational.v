(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export syntax subtyping substitution.

(* ==================== Template Handling ==================== *)

(* We increase context length so that we don't have to shift h. *)
Fixpoint handle_t Γ_len Z_len h T :=
  match T with
  | TApp n v => App (Var (Γ_len+n)) v
  | TAbsurd v => Absurd v
  | TΠMatch v T => 
      ΠMatch v (handle_t (2+Γ_len) Z_len h T)
  | TΣMatch v T1 T2 => 
      ΣMatch v
        (handle_t (1+Γ_len) Z_len h T1) 
        (handle_t (1+Γ_len) Z_len h T2)
  | TListMatch v T1 T2 =>
      ListMatch v
        (handle_t Γ_len Z_len h T1)
        (handle_t (2+Γ_len) Z_len h T2)
  | TLetBind c T =>
      DoBind c (handle_t (1+Γ_len) Z_len h T)
  | TOp op v T =>
      match get_case h op with 
      | Some c_op =>
          c_subs2_out (c_shift c_op (Γ_len + Z_len) 2) 
            v (Fun (handle_t (1+Γ_len) Z_len h T))
      | None => 
          (* You shouldn't be here *)
          Op op v (handle_t (1+Γ_len) Z_len h T) 
      end
  end.


Fixpoint tmpl_to_comp Γ_len T :=
  match T with
  | TApp n v => App (Var (Γ_len+n)) v
  | TAbsurd v => Absurd v
  | TΠMatch v T => 
      ΠMatch v (tmpl_to_comp (2+Γ_len) T)
  | TΣMatch v T1 T2 => 
      ΣMatch v
        (tmpl_to_comp (1+Γ_len) T1) 
        (tmpl_to_comp (1+Γ_len) T2)
  | TListMatch v T1 T2 => 
      ListMatch v
        (tmpl_to_comp Γ_len T1) 
        (tmpl_to_comp (2+Γ_len) T2)
  | TLetBind c T =>
      DoBind c (tmpl_to_comp (1+Γ_len) T)
  | TOp op v T =>
      Op op v (tmpl_to_comp (1+Γ_len) T)
  end.

(* ==================== Welljudged Judgements ==================== *)

Inductive wf_vtype : vtype -> Prop :=
| WfTyUnit : wf_vtype TyUnit 
| WfTyInt : wf_vtype TyInt
| WfTyEmpty : wf_vtype TyØ
| WfTyΣ A B: wf_vtype A -> wf_vtype B -> wf_vtype (TyΣ A B)
| WfTyΠ A B : wf_vtype A -> wf_vtype B -> wf_vtype (TyΠ A B)
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
    has_vtype Γ v TyØ -> 
    wf_t Γ Z (TAbsurd v) Σ 
| WfTΠMatch Γ Z v T A B Σ :
    has_vtype Γ v (TyΠ A B) -> wf_t (CtxU (CtxU Γ A) B) Z T Σ -> 
    wf_t Γ Z (TΠMatch v T) Σ
| WfTΣMatch Γ Z v T1 T2 A B Σ :
    has_vtype Γ v (TyΣ A B) -> 
    wf_t (CtxU Γ A) Z T1 Σ -> wf_t (CtxU Γ B) Z T2 Σ -> 
    wf_t Γ Z (TΣMatch v T1 T2) Σ
| WfTListMatch Γ Z v T1 T2 A Σ :
    has_vtype Γ v (TyList A) -> 
    wf_t Γ Z T1 Σ -> wf_t (CtxU (CtxU Γ A) (TyList A)) Z T2 Σ ->  
    wf_t Γ Z (TListMatch v T1 T2) Σ
| WfTLetBind Γ Z c T A Σ :
    has_ctype Γ c (CTy A SigØ EqsØ) ->
    wf_t (CtxU Γ A) Z T Σ ->
    wf_t  Γ Z (TLetBind c T) Σ
| WfTOp Γ Z op v T Aop Bop Σ :
    get_op_type Σ op = Some (Aop, Bop) -> has_vtype Γ v Aop ->
    wf_t (CtxU Γ Bop) Z T Σ ->
    wf_t Γ Z (TOp op v T) Σ

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
    has_vtype' Γ (Pair v1 v2) (TyΠ A B)
| TypeInl Γ v A B :
    has_vtype Γ v A ->
    has_vtype' Γ (Inl v) (TyΣ A B)
| TypeInr Γ v A B :
    has_vtype Γ v B ->
    has_vtype' Γ (Inr v) (TyΣ A B)
| TypeListNil Γ A :
    has_vtype' Γ ListNil (TyList A)
| TypeListCons Γ v vs A :
    has_vtype Γ v A ->
    has_vtype Γ vs (TyList A) ->
    has_vtype' Γ (ListCons v vs) (TyList A)
| TypeFun Γ c A C :
    has_ctype (CtxU Γ A) c C ->
    has_vtype' Γ (Fun c) (TyFun A C)
| TypeHandler Γ cr h A Σ E D :
    has_ctype (CtxU Γ A) cr D ->
    has_htype Γ h Σ D -> 
    respects Γ h Σ D E ->
    has_vtype' Γ (Handler cr h) (TyHandler (CTy A Σ E) D)
| TypeVSubtype Γ v A A' :
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
    has_vtype Γ v TyØ -> 
    has_ctype' Γ (Absurd v) C
| TypeΠMatch Γ v A B c C :
    has_vtype Γ v (TyΠ A B) ->
    has_ctype (CtxU (CtxU Γ A) B) c C ->
    has_ctype' Γ (ΠMatch v c) C
| TypeΣMatch Γ v A B c1 c2 C :
    has_vtype Γ v (TyΣ A B) ->
    has_ctype (CtxU Γ A) c1 C ->
    has_ctype (CtxU Γ B) c2 C ->
    has_ctype' Γ (ΣMatch v c1 c2) C
| TypeListMatch Γ v A c1 c2 C :
    has_vtype Γ v (TyList A) ->
    has_ctype Γ c1 C ->
    has_ctype (CtxU (CtxU Γ A) (TyList A)) c2 C ->
    has_ctype' Γ (ListMatch v c1 c2) C
| TypeDoBind Γ c1 c2 A B Σ E :
    has_ctype Γ c1 (CTy A Σ E) ->
    has_ctype (CtxU Γ A) c2 (CTy B Σ E) ->
    has_ctype' Γ (DoBind c1 c2) (CTy B Σ E)
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
    has_ctype' Γ (LetRec c1 c2) D
| TypeOp Γ op v c Aop Bop A Σ E :
    get_op_type Σ op = Some (Aop, Bop) ->
    has_vtype Γ v Aop ->
    has_ctype (CtxU Γ Bop) c (CTy A Σ E) ->
    has_ctype' Γ (Op op v c) (CTy A Σ E)
| TypeCSubtype Γ c C C' :
    has_ctype Γ c C -> 
    csubtype C C' -> 
    has_ctype' Γ c C'

with has_htype : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeH Γ h Σ D : 
    wf_ctx Γ -> wf_sig Σ -> wf_ctype D ->
    has_htype' Γ h Σ D -> 
    has_htype Γ h Σ D

with has_htype' : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeCasesØ Γ D : has_htype' Γ CasesØ SigØ D
| TypeCasesU Γ h op cop Aop Bop Σ D :
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ Aop) (TyFun Bop D)) cop D ->
    has_htype' Γ (CasesU h op cop) (SigU Σ op Aop Bop) D

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
        (handle_t (ctx_len Γ) (tctx_len Z) h T1) 
        (handle_t (ctx_len Γ) (tctx_len Z) h T2) ) ->
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
    judg' Γ Ψ (Veq (TyΠ A B) (Pair v1 v2) (Pair v1' v2'))
| VeqInl A B Γ Ψ v v' :
    judg Γ Ψ (Veq A v v') ->
    judg' Γ Ψ (Veq (TyΣ A B) (Inl v) (Inl v'))
| VeqInr A B Γ Ψ v v' :
    judg Γ Ψ (Veq B v v') ->
    judg' Γ Ψ (Veq (TyΣ A B) (Inr v) (Inr v'))
| VeqListNil A Γ Ψ :
    judg' Γ Ψ (Veq (TyList A) ListNil ListNil)
| VeqListCons A Γ Ψ v v' vs vs':
    judg Γ Ψ (Veq A v v') ->
    judg Γ Ψ (Veq (TyList A) vs vs') ->
    judg' Γ Ψ (Veq (TyList A) (ListCons v vs) (ListCons v' vs'))
| VeqFun A C Γ Ψ c c':
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq C c c') ->
    judg' Γ Ψ (Veq (TyFun A C) (Fun c) (Fun c'))
| VeqHandler A Σ E D Γ Ψ c c' h h':
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq D c c') ->
    judg Γ Ψ (Heq Σ D h h') ->
    judg' Γ Ψ (Veq (TyHandler (CTy A Σ E) D) (Handler c h) (Handler c' h'))
| VeqSubtype Γ Ψ A A' v1 v2 :
    judg Γ Ψ (Veq A v1 v2) ->
    vsubtype A A' ->
    judg' Γ Ψ (Veq A' v1 v2)
| ηUnit Γ Ψ v:
    judg' Γ Ψ (Veq TyUnit v Unit)
| ηFun A C Γ Ψ f:
    judg' Γ Ψ (Veq (TyFun A C) (Fun (App (v_shift f 1 0) (Var 0))) f)
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
| CeqAbsurd Γ Ψ C v v' :
    judg' Γ Ψ (Ceq C (Absurd v) (Absurd v'))
| CeqΠMatch Γ Ψ C v v' A B c c':
    judg Γ Ψ (Veq (TyΠ A B) v v') ->
    judg (CtxU (CtxU Γ A) B) (hyp_shift Ψ 2 0) (Ceq C c c') ->
    judg' Γ Ψ (Ceq C (ΠMatch v c) (ΠMatch v' c'))
| CeqΣMatch Γ Ψ C v v' A B c1 c1' c2 c2':
    judg Γ Ψ (Veq (TyΣ A B) v v') ->
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq C c1 c1') ->
    judg (CtxU Γ B) (hyp_shift Ψ 1 0) (Ceq C c2 c2') ->
    judg' Γ Ψ (Ceq C (ΣMatch v c1 c2) (ΣMatch v' c1' c2'))
| CeqListMatch Γ Ψ C v v' A c1 c1' c2 c2':
    judg Γ Ψ (Veq (TyList A) v v') ->
    judg Γ Ψ (Ceq C c1 c1') ->
    judg (CtxU (CtxU Γ A) (TyList A)) (hyp_shift Ψ 2 0) (Ceq C c2 c2') ->
    judg' Γ Ψ (Ceq C (ListMatch v c1 c2) (ListMatch v' c1' c2'))
| CeqDoBind A B Σ E Γ Ψ c1 c1' c2 c2':
    judg Γ Ψ (Ceq (CTy A Σ E) c1 c1') ->
    judg (CtxU Γ A) (hyp_shift Ψ 1 0) (Ceq (CTy B Σ E) c2 c2') ->
    judg' Γ Ψ (Ceq (CTy B Σ E) (DoBind c1 c2) (DoBind c1' c2'))
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
    judg' Γ Ψ (Ceq D (LetRec c1 c2) (LetRec c1' c2'))
| CeqOp Γ Ψ op v v' c c' Aop Bop A Σ E:
    get_op_type Σ op = Some (Aop, Bop) ->
    judg Γ Ψ (Veq Aop v v') ->
    judg (CtxU Γ Bop) (hyp_shift Ψ 1 0) (Ceq (CTy A Σ E) c c') ->
    judg' Γ Ψ (Ceq (CTy A Σ E) (Op op v c) (Op op v' c'))
| CeqSubtype Γ Ψ C C' c1 c2 :
    judg Γ Ψ (Ceq C c1 c2) ->
    csubtype C C' ->
    judg' Γ Ψ (Ceq C' c1 c2)
| OOTB A Σ E Γ' Ψ I Γ Z T1 T2 c1 c2:
    has_eq E Γ Z T1 T2 ->
    wf_inst Γ' I (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) ->
    c_inst (tmpl_to_comp (ctx_len Γ) T1) I = c1 ->
    c_inst (tmpl_to_comp (ctx_len Γ) T2) I = c2 ->
    judg' Γ' Ψ (Ceq (CTy A Σ E) c1 c2)
| βΠMatch v1 v2 c C Γ Ψ: 
    judg' Γ Ψ 
    (Ceq  C
      (ΠMatch (Pair v1 v2) c) 
      (c_subs2_out c v1 v2) )
| βΣMatch_Inl v c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ΣMatch (Inl v) c1 c2)
      (c_subs_out c1 v) )
| βΣMatch_Inr v c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ΣMatch (Inr v) c1 c2)
      (c_subs_out c2 v) )
| βListMatch_Nil c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ListMatch ListNil c1 c2)
      c1 )
| βListMatch_Cons v vs c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (ListMatch (ListCons v vs) c1 c2)
      (c_subs2_out c2 v vs) )
| βApp c v C Γ Ψ:
    judg' Γ Ψ (Ceq C (App (Fun c) v) (c_subs_out c v))
| βLetRec c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (LetRec c1 c2)
      (c_subs_out c2 (Fun (LetRec (c_shift c1 1 2) c1))) )
| βDoBind_Ret v c C Γ Ψ:
    judg' Γ Ψ (Ceq C (DoBind (Ret v) c) (c_subs_out c v))
| βDoBind_Op op v c1 c2 C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (DoBind (Op op v c1) c2)
      (Op op v (DoBind c1 (c_shift c2 1 1))) )
| βHandle_Ret c_r h v C Γ Ψ:
    judg' Γ Ψ 
    (Ceq C
      (Handle (Handler c_r h) (Ret v))
      (c_subs_out c_r v) )
| βHandle_Op c_r h op v c_k c_op C Γ Ψ:
    get_case h op = Some c_op ->
    judg' Γ Ψ 
    (Ceq C
      (Handle (Handler c_r h) (Op op v c_k))
      (c_subs2_out c_op
        v (Fun (Handle (v_shift (Handler c_r h) 1 0) c_k)) ) )
| ηEmpty Γ Ψ v n c C:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyØ)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v) (Absurd v) )
| ηPair Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΠ A B)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (ΠMatch v (c_subs (c_shift c 2 0) (2+n) (Pair (Var 1) (Var 0)))) )
| ηSum Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΣ A B)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (ΣMatch v 
        (c_subs (c_shift c 1 0) (1+n) (Inl (Var 0))) 
        (c_subs (c_shift c 1 0) (1+n) (Inr (Var 0)))) )
| ηList Γ Ψ v n c C A:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyList A)) c C ->
    judg' Γ Ψ (Ceq C (c_subs c n v)
      (ListMatch v 
        (c_subs c n ListNil) 
        (c_subs (c_shift c 2 0) (2+n) (ListCons (Var 1) (Var 0)))) )
| ηDoBind Γ Ψ c C:
    judg' Γ Ψ (Ceq C (DoBind c (Ret (Var 0))) c)
| DoLoop Γ Ψ c C:
    judg' Γ Ψ (Ceq C 
      (DoBind (LetRec (App (Var 0) Unit) (App (Var 0) Unit) ) c) 
      (LetRec (App (Var 0) Unit) (App (Var 0) Unit) ) )
| HandleLoop Γ Ψ v C:
    judg' Γ Ψ (Ceq C 
      (Handle v (LetRec (App (Var 0) Unit) (App (Var 0) Unit))) 
      (LetRec (App (Var 0) Unit) (App (Var 0) Unit)) )
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
| HeqExtend Γ Ψ op h1 h2 c1 c2 A B Σ D:
    judg Γ Ψ (Heq Σ D h1 h2) ->
    get_case h1 op = None -> get_case h2 op = None ->
    judg (CtxU (CtxU Γ A) (TyFun B D)) (hyp_shift Ψ 2 0) (Ceq D c1 c2) ->
    judg' Γ Ψ (Heq (SigU Σ op A B) D (CasesU h1 op c1) (CasesU h2 op c2))
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
| OrInLeft Γ Ψ φ1 φ2:
    judg Γ Ψ φ1 ->
    judg' Γ Ψ (Or φ1 φ2)
| OrInRight Γ Ψ φ1 φ2:
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
      (form_subs (form_shift φ 1 0) 1 (Fun (Ret (Var 1)))) ->
    (* Operation case *)
    (forall op Aop Bop,
      get_op_type Σ op = Some (Aop, Bop) ->
      judg
        (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) 
        (HypU (hyp_shift Ψ 2 0)  
          (Forall Bop 
            (form_subs (form_shift φ 3 0) 3 
              (Fun (App (Var 2) (Var 1))))))
        (form_subs (form_shift φ 2 0) 2 
          (Fun (Op op (Var 2) (App (Var 2) (Var 0)))))
    ) ->
    (* Nontermination case *)
    judg Γ Ψ 
      (form_subs φ 0 
        (Fun (LetRec 
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
