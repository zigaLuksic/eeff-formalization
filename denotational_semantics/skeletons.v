Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".
Require Export declarational.

(* ==================== Syntax ==================== *)

Inductive sk_vtype : Type :=
| SkTyUnit : sk_vtype
| SkTyInt : sk_vtype
| SkTyEmpty : sk_vtype
| SkTySum : sk_vtype -> sk_vtype -> sk_vtype
| SkTyProd : sk_vtype -> sk_vtype -> sk_vtype
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
| SkLeft : sk_vtype -> sk_vtype -> sk_val -> sk_val
| SkRight : sk_vtype -> sk_vtype -> sk_val -> sk_val
| SkPair : sk_val -> sk_val -> sk_val
| SkNil : sk_vtype -> sk_val
| SkCons : sk_val -> sk_val -> sk_val
| SkFun : sk_vtype -> sk_comp -> sk_val
| SkHandler : sk_vtype -> sk_comp -> sk_hcases -> sk_val

with sk_comp : Type :=
| SkRet : sk_val -> sk_comp
| SkAbsurd : sk_ctype -> sk_val -> sk_comp
| SkProdMatch : sk_val -> sk_comp -> sk_comp
| SkSumMatch : sk_val -> sk_comp -> sk_comp -> sk_comp
| SkListMatch : sk_val -> sk_comp -> sk_comp -> sk_comp
| SkApp : sk_val -> sk_val -> sk_comp
| SkOp : op_id -> sk_vtype -> sk_vtype -> sk_val -> sk_comp -> sk_comp
| SkLetRec : sk_vtype -> sk_ctype -> sk_comp -> sk_comp -> sk_comp
| SkDo : sk_comp -> sk_comp -> sk_comp
| SkHandle : sk_val -> sk_comp -> sk_comp

with sk_hcases : Type :=
| SkCasesØ : sk_ctype -> sk_hcases
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
    has_sk_vtype Γ (SkPair v1 v2) (SkTyProd A B)
| SkTypeLeft Γ v A B :
    has_sk_vtype Γ v A ->
    has_sk_vtype Γ (SkLeft A B v) (SkTySum A B)
| SkTypeRight Γ v A B :
    has_sk_vtype Γ v B ->
    has_sk_vtype Γ (SkRight A B v) (SkTySum A B)
| SkTypeNil Γ A :
    has_sk_vtype Γ (SkNil A) (SkTyList A)
| SkTypeCons Γ v vs A :
    has_sk_vtype Γ v A ->
    has_sk_vtype Γ vs (SkTyList A) ->
    has_sk_vtype Γ (SkCons v vs) (SkTyList A)
| SkTypeFun Γ c A C :
    has_sk_ctype (SkCtxU Γ A) c C ->
    has_sk_vtype Γ (SkFun A c) (SkTyFun A C)
| SkTypeHandler Γ cr h A D :
    has_sk_ctype (SkCtxU Γ A) cr D ->
    has_sk_htype Γ h D -> 
    has_sk_vtype Γ (SkHandler A cr h) (SkTyHandler (SkCTy A) D)

with has_sk_ctype : sk_ctx -> sk_comp -> sk_ctype -> Prop :=
| SkTypeRet Γ v A : 
    has_sk_vtype Γ v A ->
    has_sk_ctype Γ (SkRet v) (SkCTy A)
| SkTypeAbsurd Γ v C :
    has_sk_vtype Γ v SkTyEmpty -> 
    has_sk_ctype Γ (SkAbsurd C v) C
| SkTypeProdMatch Γ v A B c C :
    has_sk_vtype Γ v (SkTyProd A B) ->
    has_sk_ctype (SkCtxU (SkCtxU Γ A) B) c C ->
    has_sk_ctype Γ (SkProdMatch v c) C
| SkTypeSumMatch Γ v A B c1 c2 C :
    has_sk_vtype Γ v (SkTySum A B) ->
    has_sk_ctype (SkCtxU Γ A) c1 C ->
    has_sk_ctype (SkCtxU Γ B) c2 C ->
    has_sk_ctype Γ (SkSumMatch v c1 c2) C
| SkTypeListMatch Γ v A c1 c2 C :
    has_sk_vtype Γ v (SkTyList A) ->
    has_sk_ctype Γ c1 C ->
    has_sk_ctype (SkCtxU (SkCtxU Γ A) (SkTyList A)) c2 C ->
    has_sk_ctype Γ (SkListMatch v c1 c2) C
| SkTypeDo Γ c1 c2 A B :
    has_sk_ctype Γ c1 (SkCTy A) ->
    has_sk_ctype (SkCtxU Γ A) c2 (SkCTy B) ->
    has_sk_ctype Γ (SkDo c1 c2) (SkCTy B)
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
    has_sk_ctype Γ (SkLetRec A C c1 c2) D
| SkTypeOp Γ op v c Aop Bop A :
    has_sk_vtype Γ v Aop ->
    has_sk_ctype (SkCtxU Γ Bop) c (SkCTy A) ->
    has_sk_ctype Γ (SkOp op Aop Bop v c) (SkCTy A)

with has_sk_htype : sk_ctx -> sk_hcases -> sk_ctype -> Prop :=
| SkTypeCasesØ Γ D : has_sk_htype Γ (SkCasesØ D) D
| SkTypeCasesU Γ h op cop Aop Bop D :
    has_sk_htype Γ h D ->
    has_sk_ctype (SkCtxU (SkCtxU Γ Aop) (SkTyFun Bop D)) cop D ->
    has_sk_htype Γ (SkCasesU h op Aop Bop cop) D
.


(* ==================== Skeletonization ==================== *)

Fixpoint skeletize_vtype A :=
  match A with
  | TyUnit => SkTyUnit
  | TyInt => SkTyInt
  | TyEmpty => SkTyEmpty
  | TySum A B => SkTySum (skeletize_vtype A) (skeletize_vtype B)
  | TyProd A B => SkTyProd (skeletize_vtype A) (skeletize_vtype B)
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

Fixpoint skeletize_val v :=
match v with
| Var x => SkVar x
| Unit => SkUnit 
| Int n => SkInt n
| Left A B v => 
    SkLeft (skeletize_vtype A) (skeletize_vtype B) (skeletize_val v)
| Right A B v => 
    SkRight (skeletize_vtype A) (skeletize_vtype B) (skeletize_val v)
| Pair v1 v2 => SkPair (skeletize_val v1) (skeletize_val v2)
| Nil A => SkNil  (skeletize_vtype A)
| Cons v1 v2 => SkCons (skeletize_val v1) (skeletize_val v2)
| Fun A c => SkFun (skeletize_vtype A) (skeletize_comp c)
| Handler A c h => 
    SkHandler (skeletize_vtype A) (skeletize_comp c) (skeletize_hcases h)
end

with skeletize_comp c :=
match c with
| Ret v => SkRet (skeletize_val v)
| Absurd C v => SkAbsurd  (skeletize_ctype C) (skeletize_val v)
| ProdMatch v c => SkProdMatch (skeletize_val v) (skeletize_comp c)
| SumMatch v c1 c2 => 
    SkSumMatch (skeletize_val v) (skeletize_comp c1) (skeletize_comp c2)
| ListMatch v c1 c2 =>
    SkListMatch (skeletize_val v) (skeletize_comp c1) (skeletize_comp c2)
| App v1 v2 => SkApp (skeletize_val v1) (skeletize_val v2)
| Op op A B v c => 
    SkOp op (skeletize_vtype A) (skeletize_vtype B)
    (skeletize_val v) (skeletize_comp c)
| LetRec A C c1 c2 => 
    SkLetRec (skeletize_vtype A) (skeletize_ctype C) 
      (skeletize_comp c1) (skeletize_comp c2)
| Do c1 c2 => SkDo (skeletize_comp c1) (skeletize_comp c2)
| Handle v c => SkHandle (skeletize_val v) (skeletize_comp c)
end

with skeletize_hcases h :=
match h with
| CasesØ D => SkCasesØ (skeletize_ctype D)
| CasesU h op A B c => 
    SkCasesU (skeletize_hcases h) op (skeletize_vtype A) (skeletize_vtype B)
      (skeletize_comp c)
end
.

