(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Export syntax.

(* ==================== Syntax Definitions ==================== *)

Inductive Bval : Type :=
| BVar : nat -> Bval
| BUnit : Bval
| BInt : Z.t -> Bval
| BLeft : Bval -> Bval
| BRight : Bval -> Bval
| BPair : Bval -> Bval -> Bval
| BNil : Bval
| BCons : Bval -> Bval -> Bval
| BFun : Bcomp -> Bval
| BHandler : Bcomp -> Bhcases -> Bval
| BAnnV : Bval -> Bvtype -> Bval

with Bcomp : Type :=
| BRet : Bval -> Bcomp
| BAbsurd : Bval -> Bcomp
| BProdMatch : Bval -> Bcomp -> Bcomp (* x~1 y~0 *)
| BSumMatch : Bval -> Bcomp -> Bcomp -> Bcomp
| BListMatch : Bval -> Bcomp -> Bcomp -> Bcomp
| BApp : Bval -> Bval -> Bcomp
| BOp : op_id -> Bval -> Bcomp -> Bcomp (* x~1 k~0 *)
| BLetRec : Bvtype -> Bcomp -> Bcomp -> Bcomp (* f~0 x~1 *)
| BDo : Bcomp -> Bcomp -> Bcomp
| BHandle : Bval -> Bcomp -> Bcomp
| BAnnC : Bcomp -> Bctype -> Bcomp

with Bhcases : Type :=
| BCasesØ : Bhcases
| BCasesU : Bhcases -> op_id -> Bcomp -> Bhcases

with Bvtype : Type :=
| BTyUnit : Bvtype
| BTyInt : Bvtype
| BTyEmpty : Bvtype
| BTySum : Bvtype -> Bvtype -> Bvtype
| BTyProd : Bvtype -> Bvtype -> Bvtype
| BTyList : Bvtype -> Bvtype 
| BTyFun : Bvtype -> Bctype -> Bvtype
| BTyHandler : Bctype -> Bctype -> Bvtype

with Bctype : Type :=
| BCTy : Bvtype -> Bsig -> Beqs -> Bctype

with Bsig : Type :=
| BSigØ : Bsig
| BSigU : Bsig -> op_id -> Bvtype -> Bvtype -> Bsig

with Bctx : Type :=
| BCtxØ : Bctx
| BCtxU : Bctx -> Bvtype -> Bctx

with Btctx : Type :=
| BTCtxØ : Btctx
| BTCtxU : Btctx -> Bvtype -> Btctx

with Btmpl : Type :=
| BTApp : nat -> Bval -> Btmpl
| BTAbsurd : Bval -> Btmpl
| BTProdMatch : Bval -> Btmpl -> Btmpl
| BTSumMatch : Bval -> Btmpl -> Btmpl -> Btmpl
| BTListMatch : Bval -> Btmpl -> Btmpl -> Btmpl
| BTDo : Bcomp -> Btmpl -> Btmpl
| BTOp : op_id -> Bval -> Btmpl -> Btmpl

with Beqs : Type := 
| BEqsØ : Beqs
| BEqsU : Beqs -> Bctx -> Btctx -> Btmpl -> Btmpl -> Beqs
.

(* ==================== Getters and Ctx Modification ==================== *)

Fixpoint bidir_get_vtype Γ i :=
  match Γ, i with
  | BCtxØ , _=> None
  | BCtxU Γ' A, 0 => Some A
  | BCtxU Γ' A, S i' =>  bidir_get_vtype Γ' i'
  end.

Fixpoint bidir_get_ttype Z i :=
  match Z, i with
  | BTCtxØ , _=> None
  | BTCtxU Z' A, 0 => Some A
  | BTCtxU Z' A, S i' =>  bidir_get_ttype Z' i'
  end.

Fixpoint bidir_get_op_type Σ op :=
  match Σ with
  | BSigØ => None
  | BSigU Σ' op' A B =>
      if op == op' then Some (A, B)
      else bidir_get_op_type Σ' op
  end.

Fixpoint bidir_get_case h op :=
  match h with
  | BCasesØ => None
  | BCasesU h_others op' c_op =>
      if op == op' then Some c_op
      else bidir_get_case h_others op
  end.

Fixpoint bidir_has_eq E Γ Z T1 T2 :=
  match E with
  | BEqsØ => False
  | BEqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ bidir_has_eq E' Γ Z T1 T2
  end.

Fixpoint bidir_ctx_insert (Γ:Bctx) A (i:nat) :=
  match Γ, i with
  | Γ', 0 => BCtxU Γ' A
  | BCtxØ, _ => BCtxØ
  | BCtxU Γ' A', S i' => BCtxU (bidir_ctx_insert Γ' A i') A'
  end.

(* ==================== Subtyping ==================== *)

Inductive Bvsubtype : Bvtype -> Bvtype -> Prop :=
| BSubtypeUnit : Bvsubtype BTyUnit BTyUnit
| BSubtypeInt : Bvsubtype BTyInt BTyInt
| BSubtypeTyEmpty : Bvsubtype BTyEmpty BTyEmpty
| BSubtypeTySum A A' B B' : 
    Bvsubtype A A' -> Bvsubtype B B' -> 
    Bvsubtype (BTySum A B) (BTySum A' B')
| BSubtypeTyProd A A' B B' : 
    Bvsubtype A A' -> Bvsubtype B B' -> 
    Bvsubtype (BTyProd A B) (BTyProd A' B')
| BSubtypeTyFun A A' C C' : 
    Bvsubtype A' A -> Bcsubtype C C' -> 
    Bvsubtype (BTyFun A C) (BTyFun A' C')
| BSubtypeTyHandler C C' D D': 
    Bcsubtype C' C -> Bcsubtype D D' -> 
    Bvsubtype (BTyHandler C D) (BTyHandler C' D')

with Bcsubtype : Bctype -> Bctype -> Prop  :=
| BSubtypeCTy A A' Σ Σ' E E': 
    Bvsubtype A A' -> Bsig_subtype Σ Σ' -> Beqs_subtype E E' ->
    Bcsubtype (BCTy A Σ E) (BCTy A' Σ' E')

with Bsig_subtype : Bsig -> Bsig -> Prop :=
| BSubtypeSigØ Σ: Bsig_subtype BSigØ Σ
| BSubtypeSigU Σ Σ' op A B A' B' : 
    Bsig_subtype Σ Σ' -> bidir_get_op_type Σ' op = Some (A', B') -> 
    Bvsubtype A A' -> Bvsubtype B' B ->
    Bsig_subtype (BSigU Σ op A B) Σ'

with Beqs_subtype : Beqs -> Beqs -> Prop :=
| BSubtypeEqsØ E: Beqs_subtype BEqsØ E
| BSubtypeEqsU E E' Γ Z T1 T2 : 
    Beqs_subtype E E' -> bidir_has_eq E' Γ Z T1 T2 ->
    Beqs_subtype (BEqsU E Γ Z T1 T2) E'
.

Inductive Bctx_subtype : Bctx -> Bctx -> Prop :=
| BSubtypeCtxØ : Bctx_subtype BCtxØ BCtxØ
| BSubtypeCtxU Γ Γ' A A' : 
    Bctx_subtype Γ Γ' -> Bvsubtype A A' ->
    Bctx_subtype (BCtxU Γ A) (BCtxU Γ' A')
.

(* ==================== Wellformed Judgements ==================== *)

Inductive wf_bidir_vtype : Bvtype -> Prop :=
| BWfUnit : wf_bidir_vtype BTyUnit 
| BWfInt : wf_bidir_vtype BTyInt
| BWfEmpty : wf_bidir_vtype BTyEmpty
| BWfTySum A B: wf_bidir_vtype A -> wf_bidir_vtype B -> wf_bidir_vtype (BTySum A B)
| BWfTyProd A B : wf_bidir_vtype A -> wf_bidir_vtype B -> wf_bidir_vtype (BTyProd A B)
| BWfTyList A : wf_bidir_vtype A ->  wf_bidir_vtype (BTyList A)
| BWfTyFun A C : wf_bidir_vtype A -> wf_bidir_ctype C -> wf_bidir_vtype (BTyFun A C)
| BWfTyHandler C D : wf_bidir_ctype C -> wf_bidir_ctype D -> wf_bidir_vtype (BTyHandler C D)

with wf_bidir_ctype : Bctype -> Prop :=
| BWfCTy A Σ E : 
  wf_bidir_vtype A -> wf_bidir_sig Σ -> wf_bidir_eqs E Σ -> 
  wf_bidir_ctype (BCTy A Σ E)
    
with wf_bidir_sig : Bsig -> Prop :=
| BWfSigØ : wf_bidir_sig BSigØ
| BWfSigU Σ op Aop Bop: 
    wf_bidir_sig Σ -> bidir_get_op_type Σ op = None ->
    wf_bidir_vtype Aop -> wf_bidir_vtype Bop -> 
    wf_bidir_sig (BSigU Σ op Aop Bop)

with wf_bidir_ctx : Bctx -> Prop :=
| BWfCtxØ : wf_bidir_ctx BCtxØ
| BWfCtxU Γ A : wf_bidir_ctx Γ -> wf_bidir_vtype A -> wf_bidir_ctx (BCtxU Γ A)

with wf_bidir_tctx : Btctx -> Prop :=
| BWfTCtxØ : wf_bidir_tctx BTCtxØ
| BWfTCtxU Z A : wf_bidir_tctx Z -> wf_bidir_vtype A -> wf_bidir_tctx (BTCtxU Z A)

with wf_bidir_tmpl : Bctx -> Btctx -> Btmpl -> Bsig -> Prop :=
| BWfTApp Γ Z n v A Σ : 
    bidir_get_ttype Z n = Some A -> vcheck Γ v A -> 
    wf_bidir_tmpl Γ Z (BTApp n v) Σ
| BWfTAbsurd Γ Z v Σ :
    vcheck Γ v BTyEmpty -> 
    wf_bidir_tmpl Γ Z (BTAbsurd v) Σ 
| BWfTProdMatch Γ Z v A B T Σ :
    vsynth Γ v (BTyProd A B) -> 
    wf_bidir_tmpl (BCtxU (BCtxU Γ A) B) Z T Σ -> 
    wf_bidir_tmpl Γ Z (BTProdMatch v T) Σ
| BWfTSumMatch Γ Z v A T1 B T2 Σ :
    vsynth Γ v (BTySum A B) -> 
    wf_bidir_tmpl (BCtxU Γ A) Z T1 Σ -> 
    wf_bidir_tmpl (BCtxU Γ B) Z T2 Σ -> 
    wf_bidir_tmpl Γ Z (BTSumMatch v T1 T2) Σ
| BWfTListMatch Γ Z v T1 T2 A Σ :
    vsynth Γ v (BTyList A) -> 
    wf_bidir_tmpl Γ Z T1 Σ -> 
    wf_bidir_tmpl (BCtxU (BCtxU Γ A) (BTyList A)) Z T2 Σ ->  
    wf_bidir_tmpl Γ Z (BTListMatch v T1 T2) Σ
| BWfTLetBind Γ Z c A T Σ :
    csynth Γ c (BCTy A BSigØ BEqsØ) ->
    wf_bidir_tmpl (BCtxU Γ A) Z T Σ ->
    wf_bidir_tmpl Γ Z (BTDo c T) Σ
| BWfTOp Γ Z op A_op B_op v T Σ :
    bidir_get_op_type Σ op = Some (A_op, B_op) -> 
    vcheck Γ v A_op ->
    wf_bidir_tmpl (BCtxU Γ B_op) Z T Σ -> 
    wf_bidir_tmpl Γ Z (BTOp op v T) Σ

with wf_bidir_eqs : Beqs -> Bsig -> Prop :=
| BWfEqsØ Σ : wf_bidir_eqs BEqsØ Σ
| BWfEqsU E Γ Z T1 T2 Σ: 
    wf_bidir_eqs E Σ -> wf_bidir_ctx Γ -> wf_bidir_tctx Z -> wf_bidir_sig Σ ->
    wf_bidir_tmpl Γ Z T1 Σ -> wf_bidir_tmpl Γ Z T2 Σ -> 
    wf_bidir_eqs (BEqsU E Γ Z T1 T2) Σ

(* ==================== Type Judgements ==================== *)

with vsynth : Bctx -> Bval -> Bvtype -> Prop :=
| SynthV Γ v A : wf_bidir_ctx Γ ->  wf_bidir_vtype A -> vsynth' Γ v A -> vsynth Γ v A

with vsynth' : Bctx -> Bval -> Bvtype -> Prop :=
| SynthUnit Γ : vsynth' Γ BUnit BTyUnit 
| SynthInt Γ n : vsynth' Γ (BInt n) BTyInt
| SynthVar Γ n A :
    bidir_get_vtype Γ n = Some A ->
    vsynth' Γ (BVar n) A
| SynthPair Γ v1 v2 A B :
    vsynth Γ v1 A ->
    vsynth Γ v2 B ->
    vsynth' Γ (BPair v1 v2) (BTyProd A B)
| SynthCons Γ v vs A :
    vsynth Γ v A ->
    vcheck Γ vs (BTyList A) ->
    vsynth' Γ (BCons v vs) (BTyList A)
| SynthAnnV Γ v A :
    vcheck Γ v A ->
    vsynth' Γ (BAnnV v A) A

with csynth : Bctx -> Bcomp -> Bctype -> Prop :=
| SynthC Γ c C : wf_bidir_ctx Γ ->  wf_bidir_ctype C -> csynth' Γ c C -> csynth Γ c C

with csynth' : Bctx -> Bcomp -> Bctype -> Prop :=
| SynthRet Γ v A : 
    vsynth Γ v A ->
    csynth' Γ (BRet v) (BCTy A BSigØ BEqsØ)
| SynthProdMatch Γ v A B c C :
    vsynth Γ v (BTyProd A B) ->
    csynth (BCtxU (BCtxU Γ A) B) c C ->
    csynth' Γ (BProdMatch v c) C
| SynthApp Γ v1 v2 A C :
    vsynth Γ v1 (BTyFun A C) ->
    vcheck Γ v2 A ->
    csynth' Γ (BApp v1 v2) C
| SynthHandle Γ v c C D :
    vsynth Γ v (BTyHandler C D) ->
    ccheck Γ c C ->
    csynth' Γ (BHandle v c) D
| SynthLetRec Γ A C c1 c2 D:
    ccheck (BCtxU (BCtxU Γ A) (BTyFun A C)) c1 C ->
    csynth (BCtxU Γ (BTyFun A C)) c2 D ->
    csynth' Γ (BLetRec (BTyFun A C) c1 c2) D
| SynthAnnC Γ c C :
    ccheck Γ c C ->
    csynth' Γ (BAnnC c C) C

with vcheck : Bctx -> Bval -> Bvtype -> Prop :=
| CheckV Γ v A : wf_bidir_ctx Γ ->  wf_bidir_vtype A -> vcheck' Γ v A -> vcheck Γ v A

with vcheck' : Bctx -> Bval -> Bvtype -> Prop :=
| CheckVBySynth Γ v A A':
    vsynth Γ v A' -> Bvsubtype A' A -> vcheck' Γ v A
| CheckLeft Γ v A B :
    vcheck Γ v A ->
    vcheck' Γ (BLeft v) (BTySum A B)
| CheckRight Γ v A B :
    vcheck Γ v B ->
    vcheck' Γ (BRight v) (BTySum A B)
| CheckNil Γ A :
    vcheck' Γ BNil (BTyList A)
| CheckFun Γ c A C :
    ccheck (BCtxU Γ A) c C ->
    vcheck' Γ (BFun c) (BTyFun A C)
| CheckHandler Γ cr h A Σ E D :
    ccheck (BCtxU Γ A) cr D ->
    hcheck Γ h Σ D ->
    vcheck' Γ (BHandler cr h) (BTyHandler (BCTy A Σ E) D)

with ccheck : Bctx -> Bcomp -> Bctype -> Prop :=
| CheckC Γ c C : wf_bidir_ctx Γ ->  wf_bidir_ctype C -> ccheck' Γ c C -> ccheck Γ c C

with ccheck' : Bctx -> Bcomp -> Bctype -> Prop :=
| CheckCBySynth Γ c C C' : 
    csynth Γ c C' -> Bcsubtype C' C -> ccheck' Γ c C
| CheckSumMatch Γ v A B cl cr C :
    vsynth Γ v (BTySum A B) ->
    ccheck (BCtxU Γ A) cl C ->
    ccheck (BCtxU Γ B) cr C ->
    ccheck' Γ (BSumMatch v cl cr) C
| CheckListMatch Γ v A c1 c2 C :
    vsynth Γ v (BTyList A) ->
    ccheck Γ c1 C ->
    ccheck (BCtxU (BCtxU Γ A) (BTyList A)) c2 C ->
    ccheck' Γ (BListMatch v c1 c2) C
| CheckDo Γ c1 c2 A B Σ E :
    csynth Γ c1 (BCTy A Σ E) ->
    ccheck (BCtxU Γ A) c2 (BCTy B Σ E) ->
    ccheck' Γ (BDo c1 c2) (BCTy B Σ E)
| CheckOp Γ op_id v c A_op B_op A Σ E :
    bidir_get_op_type Σ op_id = Some (A_op, B_op) ->
    vcheck Γ v A_op ->
    ccheck (BCtxU Γ B_op) c (BCTy A Σ E) ->
    ccheck' Γ (BOp op_id v c) (BCTy A Σ E)

with hcheck :Bctx -> Bhcases -> Bsig -> Bctype -> Prop :=
| CheckH Γ h Σ D :
    wf_bidir_ctx Γ -> wf_bidir_sig Σ -> wf_bidir_ctype D -> hcheck' Γ h Σ D -> hcheck Γ h Σ D

with hcheck' : Bctx -> Bhcases -> Bsig -> Bctype -> Prop :=
| CheckCasesØ Γ D : hcheck' Γ BCasesØ BSigØ D
| CheckCasesU Γ h op_id c_op A_op B_op Σ D :
    bidir_get_case h op_id = None ->
    hcheck Γ h Σ D ->
    ccheck (BCtxU (BCtxU Γ A_op) (BTyFun B_op D)) c_op D ->
    hcheck' 
      Γ (BCasesU h op_id c_op)
      (BSigU Σ op_id A_op B_op) D
.