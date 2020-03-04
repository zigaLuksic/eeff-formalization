Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
Require Export syntax subtyping substitution.

(* ==================== Trying to implement formulae ==================== *)

Inductive judgement : Type :=
  | Veq : vtype -> val -> val -> judgement
  | Ceq : ctype -> comp -> comp -> judgement
  | Heq : sig -> ctype -> hcases -> hcases -> judgement.

Inductive hypotheses : Type :=
  | HypØ : hypotheses
  | HypU : hypotheses -> judgement -> hypotheses.

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
              (Fun (handle_t (1+Γ_len) Z_len h T)) v
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

(* ==================== Wellformed Judgements ==================== *)

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

with wf_judgement : ctx -> judgement -> Prop :=
| WfVeq Γ A v1 v2 :
    has_vtype Γ v1 A -> has_vtype Γ v2 A ->
    wf_judgement Γ (Veq A v1 v2)
| WfCeq Γ C c1 c2 :
    has_ctype Γ c1 C -> has_ctype Γ c2 C ->
    wf_judgement Γ (Ceq C c1 c2)
| WfHeq Γ Σ Σ1 Σ2 D h1 h2 :
    wf_sig Σ -> sig_subtype Σ Σ1 -> sig_subtype Σ Σ2 ->
    has_htype Γ h1 Σ1 D -> has_htype Γ h2 Σ2 D ->
    wf_judgement Γ (Heq Σ D h1 h2)

with wf_hypotheses : ctx -> hypotheses -> Prop :=
| WfHypØ Γ:
    wf_ctx Γ ->
    wf_hypotheses Γ HypØ
| WfHypU Γ Ψ j:
    wf_hypotheses Γ Ψ ->
    wf_judgement Γ j ->
    wf_hypotheses Γ (HypU Ψ j)

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
    get_case h op = None ->
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ (TyFun Bop D)) Aop) cop D ->
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
    form (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) HypØ
      (Ceq D
        (handle_t (ctx_len Γ) (tctx_len Z) h T1) 
        (handle_t (ctx_len Γ) (tctx_len Z) h T2) ) ->
    respects' Γ' h Σ D (EqsU E Γ Z T1 T2)

with form : ctx -> hypotheses -> judgement -> Prop :=
| WfForm Γ Ψ judg :
    wf_judgement Γ judg ->
    wf_hypotheses Γ Ψ ->
    form' Γ Ψ judg ->
    form Γ Ψ judg

with form' : ctx -> hypotheses -> judgement -> Prop :=

| VeqSym Γ Ψ A v1 v2 : 
    form Γ Ψ (Veq A v1 v2) -> 
    form' Γ Ψ (Veq A v2 v1)
| VeqTrans Γ Ψ A v1 v2 v3 : 
    form Γ Ψ (Veq A v1 v2) -> 
    form Γ Ψ (Veq A v2 v3) -> 
    form' Γ Ψ (Veq A v1 v3)
| VeqVar i A A' Γ Ψ :
    get_vtype Γ i = Some A' ->
    vsubtype A' A ->
    form' Γ Ψ (Veq A (Var i) (Var i))
| VeqUnit Γ Ψ:
    form' Γ Ψ (Veq TyUnit Unit Unit)
| VeqInt Γ Ψ n:
    form' Γ Ψ (Veq TyInt (Int n) (Int n))
| VeqPair A B Γ Ψ v1 v1' v2 v2' :
    form Γ Ψ (Veq A v1 v1') ->
    form Γ Ψ (Veq B v2 v2') -> 
    form' Γ Ψ (Veq (TyΠ A B) (Pair v1 v2) (Pair v1' v2'))
| VeqInl A B Γ Ψ v v' :
    form Γ Ψ (Veq A v v') ->
    form' Γ Ψ (Veq (TyΣ A B) (Inl v) (Inl v'))
| VeqInr A B Γ Ψ v v' :
    form Γ Ψ (Veq B v v') ->
    form' Γ Ψ (Veq (TyΣ A B) (Inr v) (Inr v'))
| VeqListNil A Γ Ψ :
    form' Γ Ψ (Veq (TyList A) ListNil ListNil)
| VeqListCons A Γ Ψ v v' vs vs':
    form Γ Ψ (Veq A v v') ->
    form Γ Ψ (Veq (TyList A) vs vs') ->
    form' Γ Ψ (Veq (TyList A) (ListCons v vs) (ListCons v' vs'))
| VeqFun A C Γ Ψ c c':
    form (CtxU Γ A) Ψ (Ceq C c c') ->
    form' Γ Ψ (Veq (TyFun A C) (Fun c) (Fun c'))
| VeqHandler A Σ E D D' Γ Ψ c c' h h':
    form (CtxU Γ A) Ψ (Ceq D c c') ->
    form Γ Ψ (Heq Σ D' h h') ->
    csubtype D' D ->
    form' Γ Ψ (Veq (TyHandler (CTy A Σ E) D) (Handler c h) (Handler c' h'))
| ηUnit Γ Ψ v:
    form' Γ Ψ (Veq TyUnit v Unit)
| ηFun A C Γ Ψ f:
    form' Γ Ψ (Veq (TyFun A C) (Fun (App (v_shift f 1 0) (Var 0))) f)

| CeqSym Γ Ψ C c1 c2 : 
    form Γ Ψ (Ceq C c1 c2) -> 
    form' Γ Ψ (Ceq C c2 c1)
| CeqTrans Γ Ψ C c1 c2 c3 : 
    form Γ Ψ (Ceq C c1 c2) ->
    form Γ Ψ (Ceq C c2 c3) -> 
    form' Γ Ψ (Ceq C c1 c3)
| CeqRet A Σ E Γ Ψ v v' : 
    form Γ Ψ (Veq A v v') -> 
    form' Γ Ψ (Ceq (CTy A Σ E) (Ret v) (Ret v'))
| CeqAbsurd Γ Ψ C v v' :
    form Γ Ψ (Veq TyØ v v') ->
    form' Γ Ψ (Ceq C (Absurd v) (Absurd v'))
| CeqΠMatch Γ Ψ C v v' A B c c':
    form Γ Ψ (Veq (TyΠ A B) v v') ->
    form (CtxU (CtxU Γ A) B) Ψ (Ceq C c c') ->
    form' Γ Ψ (Ceq C (ΠMatch v c) (ΠMatch v' c'))
| CeqΣMatch Γ Ψ C v v' A B c1 c1' c2 c2':
    form Γ Ψ (Veq (TyΣ A B) v v') ->
    form (CtxU Γ A) Ψ (Ceq C c1 c1') ->
    form (CtxU Γ B) Ψ (Ceq C c2 c2') ->
    form' Γ Ψ (Ceq C (ΣMatch v c1 c2) (ΣMatch v' c1' c2'))
| CeqListMatch Γ Ψ C v v' A c1 c1' c2 c2':
    form Γ Ψ (Veq (TyList A) v v') ->
    form Γ Ψ (Ceq C c1 c1') ->
    form (CtxU (CtxU Γ A) (TyList A)) Ψ (Ceq C c2 c2') ->
    form' Γ Ψ (Ceq C (ListMatch v c1 c2) (ListMatch v' c1' c2'))
| CeqDoBind A B Σ E Γ Ψ c1 c1' c2 c2':
    form Γ Ψ (Ceq (CTy A Σ E) c1 c1') ->
    form (CtxU Γ A) Ψ (Ceq (CTy B Σ E) c2 c2') ->
    form' Γ Ψ (Ceq (CTy B Σ E) (DoBind c1 c2) (DoBind c1' c2'))
| CeqApp Γ Ψ v1 v1' v2 v2' A C:
    form Γ Ψ (Veq (TyFun A C) v1 v1') ->
    form Γ Ψ (Veq A v2 v2') ->
    form' Γ Ψ (Ceq C (App v1 v2) (App v1' v2'))
| CeqHandle Γ Ψ v v' c c' C D:
    form Γ Ψ (Veq (TyHandler C D) v v') ->
    form Γ Ψ (Ceq C c c') ->
    form' Γ Ψ (Ceq D (Handle v c) (Handle v' c'))
| CeqLetRec Γ Ψ c1 c1' c2 c2' A C D:
    form (CtxU (CtxU Γ A) (TyFun A C)) Ψ (Ceq C c1 c1') ->
    form (CtxU Γ (TyFun A C)) Ψ (Ceq D c2 c2') ->
    form' Γ Ψ (Ceq D (LetRec c1 c2) (LetRec c1' c2'))
| CeqOp Γ Ψ op v v' c c' Aop Bop A Σ E:
    get_op_type Σ op = Some (Aop, Bop) ->
    form Γ Ψ (Veq Aop v v') ->
    form (CtxU Γ Bop) Ψ (Ceq (CTy A Σ E) c c') ->
    form' Γ Ψ (Ceq (CTy A Σ E) (Op op v c) (Op op v' c'))
| OOTB A Σ E Γ' Ψ I Γ Z T1 T2 c1 c2:
    has_eq E Γ Z T1 T2 ->
    wf_inst Γ' I (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) ->
    c_inst (tmpl_to_comp (ctx_len Γ) T1) I = c1 ->
    c_inst (tmpl_to_comp (ctx_len Γ) T2) I = c2 ->
    form' Γ' Ψ (Ceq (CTy A Σ E) c1 c2)
| βΠMatch v1 v2 c C Γ Ψ: 
    form' Γ Ψ 
    (Ceq  C
      (ΠMatch (Pair v1 v2) c) 
      (c_subs2_out c v1 v2) )
| βΣMatch_Inl v c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (ΣMatch (Inl v) c1 c2)
      (c_subs_out c1 v) )
| βΣMatch_Inr v c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (ΣMatch (Inr v) c1 c2)
      (c_subs_out c2 v) )
| βListMatch_Nil c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (ListMatch ListNil c1 c2)
      c1 )
| βListMatch_Cons v vs c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (ListMatch (ListCons v vs) c1 c2)
      (c_subs2_out c2 v vs) )
| βApp c v C Γ Ψ:
    form' Γ Ψ (Ceq C (App (Fun c) v) (c_subs_out c v))
| βLetRec c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (LetRec c1 c2)
      (c_subs_out c2 (Fun (LetRec (c_shift c1 1 2) c1))) )
| βDoBind_Ret v c C Γ Ψ:
    form' Γ Ψ (Ceq C (DoBind (Ret v) c) (c_subs_out c v))
| βDoBind_Op op v c1 c2 C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (DoBind (Op op v c1) c2)
      (Op op v (DoBind c1 (c_shift c2 1 1))) )
| βHandle_Ret c_r h v C Γ Ψ:
    form' Γ Ψ 
    (Ceq C
      (Handle (Handler c_r h) (Ret v))
      (c_subs_out c_r v) )
| βHandle_Op c_r h op v c_k c_op C Γ Ψ:
    get_case h op = Some c_op ->
    form' Γ Ψ 
    (Ceq C
      (Handle (Handler c_r h) (Op op v c_k))
      (c_subs2_out c_op
        (Fun (Handle (v_shift (Handler c_r h) 1 0) c_k))
        v ) )
| ηPair Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΠ A B)) c C ->
    form' Γ Ψ (Ceq C (c_subs c n v)
      (ΠMatch v (c_subs (c_shift c 2 0) (2+n) (Pair (Var 1) (Var 0)))) )
| ηSum Γ Ψ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΣ A B)) c C ->
    form' Γ Ψ (Ceq C (c_subs c n v)
      (ΣMatch v 
        (c_subs (c_shift c 1 0) (1+n) (Inl (Var 0))) 
        (c_subs (c_shift c 1 0) (1+n) (Inr (Var 0)))) )
| ηList Γ Ψ v n c C A:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyList A)) c C ->
    form' Γ Ψ (Ceq C (c_subs c n v)
      (ListMatch v 
        (c_subs c n ListNil) 
        (c_subs (c_shift c 2 0) (2+n) (ListCons (Var 1) (Var 0)))) )
| ηDoBind Γ Ψ c C:
    form' Γ Ψ (Ceq C (DoBind c (Ret (Var 0))) c)

| HeqSigØ D Γ Ψ h1 h2: 
    form' Γ Ψ (Heq SigØ D h1 h2)
| HeqSigU Σ op A B D Γ Ψ h1 c1 h2 c2:
    get_case h1 op = Some c1 ->
    get_case h2 op = Some c2 ->
    form (CtxU (CtxU Γ (TyFun B D)) A) Ψ (Ceq D c1 c2) ->
    form Γ Ψ (Heq Σ D h1 h2) ->
    form' Γ Ψ (Heq (SigU Σ op A B) D h1 h2)

with wf_inst : ctx -> instantiation -> ctx -> Prop :=
| WfInstØ Γcheck : wf_ctx Γcheck -> wf_inst Γcheck InstØ CtxØ
| WfInstU Γcheck I v Γ A : 
  has_vtype Γcheck v A ->
  wf_inst Γcheck I Γ ->
  wf_inst Γcheck (InstU I v) (CtxU Γ A) 
. 
