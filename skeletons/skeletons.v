(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export declarational.

(* ==================== Syntax ==================== *)

Inductive sk_vtype : Type :=
| SkTyUnit : sk_vtype
| SkTyInt : sk_vtype
| SkTyØ : sk_vtype
| SkTyΣ : sk_vtype -> sk_vtype -> sk_vtype
| SkTyΠ : sk_vtype -> sk_vtype -> sk_vtype
| SkTyList : sk_vtype -> sk_vtype
| SkTyFun : sk_vtype -> sk_ctype -> sk_vtype
| SkTyHandler : sk_ctype -> sk_ctype -> sk_vtype

with sk_ctype : Type :=
| SkCTy : sk_vtype -> sk_ctype
.

Inductive sk_val : Type :=
| SkVar : nat -> sk_val
| SkUnit : sk_val
| SkInt : Z.t -> sk_val
| SkInl : sk_val -> sk_val
| SkInr : sk_val -> sk_val
| SkPair : sk_val -> sk_val -> sk_val
| SkListNil : sk_val
| SkListCons : sk_val -> sk_val -> sk_val
| SkFun : sk_comp -> sk_val
| SkHandler : sk_comp -> sk_hcases -> sk_val

with sk_comp : Type :=
| SkRet : sk_val -> sk_comp
| SkAbsurd : sk_val -> sk_comp
| SkΠMatch : sk_val -> sk_comp -> sk_comp
| SkΣMatch : sk_val -> sk_comp -> sk_comp -> sk_comp
| SkListMatch : sk_val -> sk_comp -> sk_comp -> sk_comp
| SkApp : sk_val -> sk_val -> sk_comp
| SkOp : op_id -> sk_vtype -> sk_vtype -> sk_val -> sk_comp -> sk_comp
| SkLetRec : sk_comp -> sk_comp -> sk_comp
| SkDoBind : sk_comp -> sk_comp -> sk_comp
| SkHandle : sk_val -> sk_comp -> sk_comp

with sk_hcases : Type :=
| SkCasesØ : sk_hcases
| SkCasesU : sk_hcases -> op_id -> sk_vtype -> sk_vtype -> sk_comp -> sk_hcases
.

Inductive sk_ctx : Type :=
| SkCtxØ : sk_ctx
| SkCtxU : sk_ctx -> sk_vtype -> sk_ctx
.

Fixpoint get_sk_vtype Γ i :=
  match Γ, i with
  | SkCtxØ , _=> None
  | SkCtxU Γ' A, 0 => Some A
  | SkCtxU Γ' A, S i' =>  get_sk_vtype Γ' i'
  end.

(* ==================== Type Judgements ==================== *)

Inductive has_sk_vtype : sk_ctx -> sk_val -> sk_vtype -> Prop :=
| SkTypeUnit Γ : 
    has_sk_vtype Γ SkUnit SkTyUnit 
| SkTypeInt Γ n : 
    has_sk_vtype Γ (SkInt n) SkTyInt
| SkTypeVar Γ n A :
    get_sk_vtype Γ n = Some A ->
    has_sk_vtype Γ (SkVar n) A
| SkTypePair Γ v1 v2 A B :
    has_sk_vtype Γ v1 A ->
    has_sk_vtype Γ v2 B ->
    has_sk_vtype Γ (SkPair v1 v2) (SkTyΠ A B)
| SkTypeInl Γ v A B :
    has_sk_vtype Γ v A ->
    has_sk_vtype Γ (SkInl v) (SkTyΣ A B)
| SkTypeInr Γ v A B :
    has_sk_vtype Γ v B ->
    has_sk_vtype Γ (SkInr v) (SkTyΣ A B)
| SkTypeListNil Γ A :
    has_sk_vtype Γ SkListNil (SkTyList A)
| SkTypeListCons Γ v vs A :
    has_sk_vtype Γ v A ->
    has_sk_vtype Γ vs (SkTyList A) ->
    has_sk_vtype Γ (SkListCons v vs) (SkTyList A)
| SkTypeFun Γ c A C :
    has_sk_ctype (SkCtxU Γ A) c C ->
    has_sk_vtype Γ (SkFun c) (SkTyFun A C)
| SkTypeHandler Γ cr h A D :
    has_sk_ctype (SkCtxU Γ A) cr D ->
    has_sk_htype Γ h D -> 
    has_sk_vtype Γ (SkHandler cr h) (SkTyHandler (SkCTy A) D)

with has_sk_ctype : sk_ctx -> sk_comp -> sk_ctype -> Prop :=
| SkTypeRet Γ v A : 
    has_sk_vtype Γ v A ->
    has_sk_ctype Γ (SkRet v) (SkCTy A)
| SkTypeAbsurd Γ v C :
    has_sk_vtype Γ v SkTyØ -> 
    has_sk_ctype Γ (SkAbsurd v) C
| SkTypeΠMatch Γ v A B c C :
    has_sk_vtype Γ v (SkTyΠ A B) ->
    has_sk_ctype (SkCtxU (SkCtxU Γ A) B) c C ->
    has_sk_ctype Γ (SkΠMatch v c) C
| SkTypeΣMatch Γ v A B c1 c2 C :
    has_sk_vtype Γ v (SkTyΣ A B) ->
    has_sk_ctype (SkCtxU Γ A) c1 C ->
    has_sk_ctype (SkCtxU Γ B) c2 C ->
    has_sk_ctype Γ (SkΣMatch v c1 c2) C
| SkTypeListMatch Γ v A c1 c2 C :
    has_sk_vtype Γ v (SkTyList A) ->
    has_sk_ctype Γ c1 C ->
    has_sk_ctype (SkCtxU (SkCtxU Γ A) (SkTyList A)) c2 C ->
    has_sk_ctype Γ (SkListMatch v c1 c2) C
| SkTypeDoBind Γ c1 c2 A B :
    has_sk_ctype Γ c1 (SkCTy A) ->
    has_sk_ctype (SkCtxU Γ A) c2 (SkCTy B) ->
    has_sk_ctype Γ (SkDoBind c1 c2) (SkCTy B)
| SkTypeApp Γ v1 v2 A C :
    has_sk_vtype Γ v1 (SkTyFun A C) ->
    has_sk_vtype Γ v2 A ->
    has_sk_ctype Γ (SkApp v1 v2) C
| SkTypeHandle Γ v c C D :
    has_sk_vtype Γ v (SkTyHandler C D) ->
    has_sk_ctype Γ c C ->
    has_sk_ctype Γ (SkHandle v c) D
| SkTypeLetRec Γ A C c1 c2 D:
    has_sk_ctype (SkCtxU (SkCtxU Γ A) (SkTyFun A C)) c1 C ->
    has_sk_ctype (SkCtxU Γ (SkTyFun A C)) c2 D ->
    has_sk_ctype Γ (SkLetRec c1 c2) D
| SkTypeOp Γ op v c Aop Bop A :
    has_sk_vtype Γ v Aop ->
    has_sk_ctype (SkCtxU Γ Bop) c (SkCTy A) ->
    has_sk_ctype Γ (SkOp op Aop Bop v c) (SkCTy A)

with has_sk_htype : sk_ctx -> sk_hcases -> sk_ctype -> Prop :=
| SkTypeCasesØ Γ D : has_sk_htype Γ SkCasesØ D
| SkTypeCasesU Γ h op cop Aop Bop D :
    has_sk_htype Γ h D ->
    has_sk_ctype (SkCtxU (SkCtxU Γ Aop) (SkTyFun Bop D)) cop D ->
    has_sk_htype Γ (SkCasesU h op Aop Bop cop) D
.


(* ==================== Necromancy ==================== *)

Fixpoint skeletize_vtype A :=
  match A with
  | TyUnit => SkTyUnit
  | TyInt => SkTyInt
  | TyØ => SkTyØ
  | TyΣ A B => SkTyΣ (skeletize_vtype A) (skeletize_vtype B)
  | TyΠ A B => SkTyΠ (skeletize_vtype A) (skeletize_vtype B)
  | TyList A => SkTyList (skeletize_vtype A)
  | TyFun A C => SkTyFun (skeletize_vtype A) (skeletize_ctype C)
  | TyHandler C D => SkTyHandler (skeletize_ctype C) (skeletize_ctype D)
  end
with skeletize_ctype C :=
  match C with
  | CTy A Σ E => SkCTy (skeletize_vtype A)
  end
.

Fixpoint skeletize_ctx Γ :=
  match Γ with
  | CtxØ => SkCtxØ
  | CtxU Γ A => SkCtxU (skeletize_ctx Γ) (skeletize_vtype A)
  end.

(* The variable 'p' is the proof term. We do that to avoid constructing proof
   terms by hand. This might complicate things later on, since it breaks
   proof dependency by introducing new proofs. *)

Inductive v_ann : forall Γ v A, has_vtype Γ v A -> sk_val -> Prop :=
| AnnVar Γ n A p:
    get_vtype Γ n = Some A ->
    v_ann Γ (Var n) A p (SkVar n)
| AnnUnit Γ p: 
    v_ann Γ Unit TyUnit p SkUnit
| AnnInt Γ n p: 
    v_ann Γ (Int n) TyInt p (SkInt n)
| AnnPair Γ v1 v2 A B v1' v2' p1 p2 p:
    v_ann Γ v1 A p1 v1' -> v_ann Γ v2 B p2 v2' ->
    v_ann Γ (Pair v1 v2) (TyΠ A B) p (SkPair v1' v2')
| AnnInl Γ v A B v' pl p:
    v_ann Γ v A pl v' ->
    v_ann Γ (Inl v) (TyΣ A B) p (SkInl v')
| AnnInr Γ v A B v' pr p:
    v_ann Γ v B pr v' ->
    v_ann Γ (Inr v) (TyΣ A B) p (SkInr v')
| AnnListNil Γ A p:
    v_ann Γ ListNil (TyList A) p (SkListNil)
| AnnListCons Γ v1 v2 A v1' v2' p1 p2 p:
    v_ann Γ v1 A p1 v1' -> v_ann Γ v2 (TyList A) p2 v2' ->
    v_ann Γ (ListCons v1 v2) (TyList A) p (SkListCons v1' v2')
| AnnFun Γ c A C c' pc p:
    c_ann (CtxU Γ A) c C pc c' ->
    v_ann Γ (Fun c) (TyFun A C) p (SkFun c')
| AnnHandler Γ c c' h h' A Σ E D pc ph p:
    c_ann (CtxU Γ A) c D pc c' -> h_ann Γ h Σ D ph h' ->
    v_ann Γ (Handler c h) (TyHandler (CTy A Σ E) D) p (SkHandler c' h')
| AnnVSubtype Γ v v' A A' p p':
    v_ann Γ v A p' v' ->
    vsubtype A A' ->
    v_ann Γ v A' p v'

with c_ann : forall Γ c C, has_ctype Γ c C -> sk_comp -> Prop :=
| AnnRet Γ v v' A pv p :
    v_ann Γ v A pv v' ->
    c_ann Γ (Ret v) (CTy A SigØ EqsØ) p (SkRet v')
| AnnAbsurd Γ v v' C pv p :
    v_ann Γ v TyØ pv v' ->
    c_ann Γ (Absurd v) C p (SkAbsurd v')
| AnnΠMatch Γ v v' A B c c' C pv pc p:
    v_ann Γ v (TyΠ A B) pv v' -> c_ann (CtxU (CtxU Γ A) B) c C pc c'->
    c_ann Γ (ΠMatch v c) C p (SkΠMatch v' c')
| AnnΣMatch Γ v v' A B c1 c1' c2 c2' C p pv pc1 pc2:
    v_ann Γ v (TyΣ A B) pv v' ->
    c_ann (CtxU Γ A) c1 C pc1 c1' -> c_ann (CtxU Γ B) c2 C pc2 c2' ->
    c_ann Γ (ΣMatch v c1 c2) C p (SkΣMatch v' c1' c2')
| AnnListMatch Γ v v' A c1 c1' c2 c2' C p pv pc1 pc2:
    v_ann Γ v (TyList A) pv v' ->
    c_ann Γ c1 C pc1 c1' -> c_ann (CtxU (CtxU Γ A) (TyList A)) c2 C pc2 c2' ->
    c_ann Γ (ListMatch v c1 c2) C p (SkListMatch v' c1' c2')
| AnnDoBind Γ c1 c1' c2 c2' A B Σ E p pc1 pc2:
    c_ann Γ c1 (CTy A Σ E) pc1 c1' -> c_ann (CtxU Γ A) c2 (CTy B Σ E) pc2 c2' ->
    c_ann Γ (DoBind c1 c2) (CTy B Σ E) p (SkDoBind c1' c2')
| AnnApp Γ v1 v1' v2 v2' A C pv1 pv2 p:
    v_ann Γ v1 (TyFun A C) pv1 v1' -> v_ann Γ v2 A pv2 v2' ->
    c_ann Γ (App v1 v2) C p (SkApp v1' v2')
| AnnHandle Γ v v' c c' C D pv pc p:
    v_ann Γ v (TyHandler C D) pv v' -> c_ann Γ c C pc c' ->
    c_ann Γ (Handle v c) D p (SkHandle v' c')
| AnnLetRec Γ c1 c1' c2 c2' A C D pc1 pc2 p :
    c_ann (CtxU (CtxU Γ A) (TyFun A C)) c1 C pc1 c1' ->
    c_ann (CtxU Γ (TyFun A C)) c2 D pc2 c2' -> 
    c_ann Γ (LetRec c1 c2) D p (SkLetRec c1' c2')
| AnnOp Γ op v v' c c' A Σ E Aop Bop pv pc p :
    get_op_type Σ op = Some (Aop, Bop) ->
    v_ann Γ v Aop pv v' -> c_ann (CtxU Γ Bop) c (CTy A Σ E) pc c' ->
    c_ann Γ (Op op v c) (CTy A Σ E) p 
      (SkOp op (skeletize_vtype Aop) (skeletize_vtype Bop) v' c')
| AnnCSubtype Γ c c' C C' p p':
    c_ann Γ c C p' c' ->
    csubtype C C' ->
    c_ann Γ c C' p c'

with h_ann : forall Γ h Σ D, has_htype Γ h Σ D -> sk_hcases -> Prop := 
| AnnCasesØ Γ Σ D p:
    h_ann Γ CasesØ Σ D p SkCasesØ
| AnnCasesU Γ Σ D h h' c c' A B op ph pc p:
    h_ann Γ h Σ D ph h' ->
    c_ann (CtxU (CtxU Γ A) (TyFun B D)) c D pc c' ->
    h_ann Γ (CasesU h op A B c) (SigU Σ op A B) D p 
      (SkCasesU h' op (skeletize_vtype A) (skeletize_vtype B) c')
.
