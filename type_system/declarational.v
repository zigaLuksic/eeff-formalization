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
    ceq D (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
      (handle_t (ctx_len Γ) (tctx_len Z) h T1) 
      (handle_t (ctx_len Γ) (tctx_len Z) h T2) ->
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
    vsubtype A' A ->
    veq' A Γ (Var i) (Var i)
| VeqUnit Γ:
    veq' TyUnit Γ Unit Unit
| VeqInt Γ n:
    veq' TyInt Γ (Int n) (Int n)
| VeqPair A B Γ v1 v1' v2 v2' :
    veq A Γ v1 v1' ->
    veq B Γ v2 v2' -> 
    veq' (TyΠ A B) Γ (Pair v1 v2) (Pair v1' v2')
| VeqInl A B Γ v v' :
    veq A Γ v v' ->
    veq' (TyΣ A B) Γ (Inl v) (Inl v')
| VeqInr A B Γ v v' :
    veq B Γ v v' ->
    veq' (TyΣ A B) Γ (Inr v) (Inr v')
| VeqListNil A Γ :
    veq' (TyList A) Γ ListNil ListNil
| VeqListCons A Γ v v' vs vs':
    veq A Γ v v' ->
    veq (TyList A) Γ vs vs' ->
    veq' (TyList A) Γ (ListCons v vs) (ListCons v' vs')
| VeqFun A C Γ c c':
    ceq C (CtxU Γ A) c c' ->
    veq' (TyFun A C) Γ (Fun c) (Fun c')
| VeqHandler A Σ E D D' Γ c c' h h':
    ceq D (CtxU Γ A) c c' ->
    heq Σ D' Γ h h' ->
    csubtype D' D ->
    veq' (TyHandler (CTy A Σ E) D) Γ (Handler c h) (Handler c' h')
| ηUnit Γ v:
    veq' TyUnit Γ v Unit
| ηFun A C Γ f:
    veq' (TyFun A C) Γ (Fun (App (v_shift f 1 0) (Var 0))) f


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
| CeqAbsurd C Γ v v' :
    ceq' C Γ (Absurd v) (Absurd v')
| CeqΠMatch Γ C v v' A B c c':
    veq (TyΠ A B) Γ v v' ->
    ceq C (CtxU (CtxU Γ A) B) c c' ->
    ceq' C Γ (ΠMatch v c) (ΠMatch v' c')
| CeqΣMatch Γ C v v' A B c1 c1' c2 c2':
    veq (TyΣ A B) Γ v v' ->
    ceq C (CtxU Γ A) c1 c1' ->
    ceq C (CtxU Γ B) c2 c2' ->
    ceq' C Γ (ΣMatch v c1 c2) (ΣMatch v' c1' c2')
| CeqListMatch Γ C v v' A c1 c1' c2 c2':
    veq (TyList A) Γ v v' ->
    ceq C Γ c1 c1' ->
    ceq C (CtxU (CtxU Γ A) (TyList A)) c2 c2' ->
    ceq' C Γ (ListMatch v c1 c2) (ListMatch v' c1' c2')
| CeqDoBind A B Σ E Γ c1 c1' c2 c2':
    ceq (CTy A Σ E) Γ c1 c1' ->
    ceq (CTy B Σ E) (CtxU Γ A) c2 c2' ->
    ceq' (CTy B Σ E) Γ (DoBind c1 c2) (DoBind c1' c2')
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
    ceq' D Γ (LetRec c1 c2) (LetRec c1' c2')
| CeqOp Γ op v v' c c' Aop Bop A Σ E:
    get_op_type Σ op = Some (Aop, Bop) ->
    veq Aop Γ v v' ->
    ceq (CTy A Σ E) (CtxU Γ Bop) c c' ->
    ceq' (CTy A Σ E) Γ (Op op v c) (Op op v' c')
| OOTB A Σ E Γ' I Γ Z T1 T2 c1 c2:
    has_eq E Γ Z T1 T2 ->
    wf_inst Γ' I (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) ->
    c_inst (tmpl_to_comp (ctx_len Γ) T1) I = c1 ->
    c_inst (tmpl_to_comp (ctx_len Γ) T2) I = c2 ->
    ceq' (CTy A Σ E) Γ' c1 c2
| βΠMatch v1 v2 c C Γ: 
    ceq' C Γ
      (ΠMatch (Pair v1 v2) c) 
      (c_subs2_out c v1 v2)
| βΣMatch_Inl v c1 c2 C Γ:
    ceq' C Γ
      (ΣMatch (Inl v) c1 c2)
      (c_subs_out c1 v)
| βΣMatch_Inr v c1 c2 C Γ:
    ceq' C Γ 
      (ΣMatch (Inr v) c1 c2)
      (c_subs_out c2 v)
| βListMatch_Nil c1 c2 C Γ:
    ceq' C Γ
      (ListMatch ListNil c1 c2)
      c1
| βListMatch_Cons v vs c1 c2 C Γ:
    ceq' C Γ
      (ListMatch (ListCons v vs) c1 c2)
      (c_subs2_out c2 v vs)
| βApp c v C Γ:
    ceq' C Γ (App (Fun c) v) (c_subs_out c v)
| βLetRec c1 c2 C Γ:
    ceq' C Γ
      (LetRec c1 c2)
      (c_subs_out c2 (Fun (LetRec (c_shift c1 1 2) c1)))
| βDoBind_Ret v c C Γ:
    ceq' C Γ (DoBind (Ret v) c) (c_subs_out c v)
| βDoBind_Op op v c1 c2 C Γ:
    ceq' C Γ
      (DoBind (Op op v c1) c2)
      (Op op v (DoBind c1 (c_shift c2 1 1)))
| βHandle_Ret c_r h v C Γ:
    ceq' C Γ
      (Handle (Handler c_r h) (Ret v))
      (c_subs_out c_r v)
| βHandle_Op c_r h op v c_k c_op C Γ:
    get_case h op = Some c_op ->
    ceq' C Γ
      (Handle (Handler c_r h) (Op op v c_k))
      (c_subs2_out c_op
        (Fun (Handle (v_shift (Handler c_r h) 1 0) c_k))
        v )
| ηEmpty Γ v n c C:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyØ)) c C ->
    ceq' C Γ (c_subs c n v) (Absurd v)
| ηPair Γ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΠ A B)) c C ->
    ceq' C Γ (c_subs c n v)
      (ΠMatch v (c_subs (c_shift c 2 0) (2+n) (Pair (Var 1) (Var 0))))
| ηSum Γ v n c C A B:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyΣ A B)) c C ->
    ceq' C Γ (c_subs c n v) 
      (ΣMatch v 
        (c_subs (c_shift c 1 0) (1+n) (Inl (Var 0))) 
        (c_subs (c_shift c 1 0) (1+n) (Inr (Var 0))))
| ηList Γ v n c C A:
    n <= ctx_len Γ ->
    has_ctype (ctx_insert Γ n (TyList A)) c C ->
    ceq' C Γ (c_subs c n v) 
      (ListMatch v 
        (c_subs c n ListNil) 
        (c_subs (c_shift c 2 0) (2+n) (ListCons (Var 1) (Var 0))))
| ηDoBind Γ c C:
    ceq' C Γ (DoBind c (Ret (Var 0))) c

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
    ceq D (CtxU (CtxU Γ (TyFun B D)) A) c1 c2 ->
    heq Σ D Γ h1 h2 ->
    heq' (SigU Σ op A B) D Γ h1 h2

with wf_inst : ctx -> instantiation -> ctx -> Prop :=
| WfInstØ Γcheck : wf_ctx Γcheck -> wf_inst Γcheck InstØ CtxØ
| WfInstU Γcheck I v Γ A : 
  has_vtype Γcheck v A ->
  wf_inst Γcheck I Γ ->
  wf_inst Γcheck (InstU I v) (CtxU Γ A) 
.
