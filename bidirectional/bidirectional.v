(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Export syntax.

(* ==================== Syntax Definitions ==================== *)

Inductive βval : Type :=
| βVar : nat -> βval
| βUnit : βval
| βInt : Z.t -> βval
| βInl : βval -> βval
| βInr : βval -> βval
| βPair : βval -> βval -> βval
| βListNil : βval
| βListCons : βval -> βval -> βval
| βFun : βcomp -> βval
| βHandler : βcomp -> βhcases -> βval
| βAnnV : βval -> βvtype -> βval

with βcomp : Type :=
| βRet : βval -> βcomp
| βAbsurd : βval -> βcomp
| βΠMatch : βval -> βcomp -> βcomp (* x~1 y~0 *)
| βΣMatch : βval -> βcomp -> βcomp -> βcomp
| βListMatch : βval -> βcomp -> βcomp -> βcomp
| βApp : βval -> βval -> βcomp
| βOp : op_id -> βval -> βcomp -> βcomp (* x~1 k~0 *)
| βLetRec : βvtype -> βcomp -> βcomp -> βcomp (* f~0 x~1 *)
| βDoBind : βcomp -> βcomp -> βcomp
| βHandle : βval -> βcomp -> βcomp
| βAnnC : βcomp -> βctype -> βcomp

with βhcases : Type :=
| βCasesØ : βhcases
| βCasesU : βhcases -> op_id -> βcomp -> βhcases

with βvtype : Type :=
| βTyUnit : βvtype
| βTyInt : βvtype
| βTyØ : βvtype
| βTyΣ : βvtype -> βvtype -> βvtype
| βTyΠ : βvtype -> βvtype -> βvtype
| βTyList : βvtype -> βvtype 
| βTyFun : βvtype -> βctype -> βvtype
| βTyHandler : βctype -> βctype -> βvtype

with βctype : Type :=
| βCTy : βvtype -> βsig -> βeqs -> βctype

with βsig : Type :=
| βSigØ : βsig
| βSigU : βsig -> op_id -> βvtype -> βvtype -> βsig

with βctx : Type :=
| βCtxØ : βctx
| βCtxU : βctx -> βvtype -> βctx

with βtctx : Type :=
| βTCtxØ : βtctx
| βTCtxU : βtctx -> βvtype -> βtctx

with βtmpl : Type :=
| βTApp : nat -> βval -> βtmpl
| βTAbsurd : βval -> βtmpl
| βTΠMatch : βval -> βtmpl -> βtmpl
| βTΣMatch : βval -> βtmpl -> βtmpl -> βtmpl
| βTListMatch : βval -> βtmpl -> βtmpl -> βtmpl
| βTLetBind : βcomp -> βtmpl -> βtmpl
| βTOp : op_id -> βval -> βtmpl -> βtmpl

with βeqs : Type := 
| βEqsØ : βeqs
| βEqsU : βeqs -> βctx -> βtctx -> βtmpl -> βtmpl -> βeqs
.

(* ==================== Getters and Ctx Modification ==================== *)

Fixpoint get_βvtype Γ i :=
  match Γ, i with
  | βCtxØ , _=> None
  | βCtxU Γ' A, 0 => Some A
  | βCtxU Γ' A, S i' =>  get_βvtype Γ' i'
  end.

Fixpoint get_βttype Z i :=
  match Z, i with
  | βTCtxØ , _=> None
  | βTCtxU Z' A, 0 => Some A
  | βTCtxU Z' A, S i' =>  get_βttype Z' i'
  end.


Fixpoint get_op_βtype Σ op :=
  match Σ with
  | βSigØ => None
  | βSigU Σ' op' A B =>
      if op == op' then Some (A, B)
      else get_op_βtype Σ' op
  end.


Fixpoint get_βcase h op :=
  match h with
  | βCasesØ => None
  | βCasesU h_others op' c_op =>
      if op == op' then Some c_op
      else get_βcase h_others op
  end.


Fixpoint has_βeq E Γ Z T1 T2 :=
  match E with
  | βEqsØ => False
  | βEqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ has_βeq E' Γ Z T1 T2
  end.


Fixpoint βctx_insert (Γ:βctx) A (i:nat) :=
  match Γ, i with
  | Γ', 0 => βCtxU Γ' A
  | βCtxØ, _ => βCtxØ
  | βCtxU Γ' A', S i' => βCtxU (βctx_insert Γ' A i') A'
  end.

(* ==================== Subtyping ==================== *)

Inductive βvsubtype : βvtype -> βvtype -> Prop :=
| βSubtypeUnit : βvsubtype βTyUnit βTyUnit
| βSubtypeInt : βvsubtype βTyInt βTyInt
| βSubtypeTyØ : βvsubtype βTyØ βTyØ
| βSubtypeTyΣ A A' B B' : 
    βvsubtype A A' -> βvsubtype B B' -> 
    βvsubtype (βTyΣ A B) (βTyΣ A' B')
| βSubtypeTyΠ A A' B B' : 
    βvsubtype A A' -> βvsubtype B B' -> 
    βvsubtype (βTyΠ A B) (βTyΠ A' B')
| βSubtypeTyFun A A' C C' : 
    βvsubtype A' A -> βcsubtype C C' -> 
    βvsubtype (βTyFun A C) (βTyFun A' C')
| βSubtypeTyHandler C C' D D': 
    βcsubtype C' C -> βcsubtype D D' -> 
    βvsubtype (βTyHandler C D) (βTyHandler C' D')

with βcsubtype : βctype -> βctype -> Prop  :=
| βSubtypeCTy A A' Σ Σ' E E': 
    βvsubtype A A' -> βsig_subtype Σ Σ' -> βeqs_subtype E E' ->
    βcsubtype (βCTy A Σ E) (βCTy A' Σ' E')

with βsig_subtype : βsig -> βsig -> Prop :=
| βSubtypeSigØ Σ: βsig_subtype βSigØ Σ
| βSubtypeSigU Σ Σ' op A B A' B' : 
    βsig_subtype Σ Σ' -> get_op_βtype Σ' op = Some (A', B') -> 
    βvsubtype A A' -> βvsubtype B' B ->
    βsig_subtype (βSigU Σ op A B) Σ'

with βeqs_subtype : βeqs -> βeqs -> Prop :=
| βSubtypeEqsØ E: βeqs_subtype βEqsØ E
| βSubtypeEqsU E E' Γ Z T1 T2 : 
    βeqs_subtype E E' -> has_βeq E' Γ Z T1 T2 ->
    βeqs_subtype (βEqsU E Γ Z T1 T2) E'
.

Inductive βctx_subtype : βctx -> βctx -> Prop :=
| βSubtypeCtxØ : βctx_subtype βCtxØ βCtxØ
| βSubtypeCtxU Γ Γ' A A' : 
    βctx_subtype Γ Γ' -> βvsubtype A A' ->
    βctx_subtype (βCtxU Γ A) (βCtxU Γ' A')
.

(* ==================== Wellformed Judgements ==================== *)

Inductive wf_βvtype : βvtype -> Prop :=
| βWfUnit : wf_βvtype βTyUnit 
| βWfInt : wf_βvtype βTyInt
| βWfEmpty : wf_βvtype βTyØ
| βWfTyΣ A B: wf_βvtype A -> wf_βvtype B -> wf_βvtype (βTyΣ A B)
| βWfTyΠ A B : wf_βvtype A -> wf_βvtype B -> wf_βvtype (βTyΠ A B)
| βWfTyList A : wf_βvtype A ->  wf_βvtype (βTyList A)
| βWfTyFun A C : wf_βvtype A -> wf_βctype C -> wf_βvtype (βTyFun A C)
| βWfTyHandler C D : wf_βctype C -> wf_βctype D -> wf_βvtype (βTyHandler C D)

with wf_βctype : βctype -> Prop :=
| βWfCTy A Σ E : 
  wf_βvtype A -> wf_βsig Σ -> wf_βeqs E Σ -> 
  wf_βctype (βCTy A Σ E)
    
with wf_βsig : βsig -> Prop :=
| βWfSigØ : wf_βsig βSigØ
| βWfSigU Σ op Aop Bop: 
    wf_βsig Σ -> get_op_βtype Σ op = None ->
    wf_βvtype Aop -> wf_βvtype Bop -> 
    wf_βsig (βSigU Σ op Aop Bop)

with wf_βctx : βctx -> Prop :=
| βWfCtxØ : wf_βctx βCtxØ
| βWfCtxU Γ A : wf_βctx Γ -> wf_βvtype A -> wf_βctx (βCtxU Γ A)

with wf_βtctx : βtctx -> Prop :=
| βWfTCtxØ : wf_βtctx βTCtxØ
| βWfTCtxU Γ A : wf_βtctx Γ -> wf_βvtype A -> wf_βtctx (βTCtxU Γ A)

with wf_βtmpl : βctx -> βtctx -> βtmpl -> βsig -> Prop :=
| βWfTApp Γ Z n v A Σ : 
    get_βttype Z n = Some A -> vcheck Γ v A -> 
    wf_βtmpl Γ Z (βTApp n v) Σ
| βWfTAbsurd Γ Z v Σ :
    vcheck Γ v βTyØ -> 
    wf_βtmpl Γ Z (βTAbsurd v) Σ 
| βWfTΠMatch Γ Z v A B T Σ :
    vsynth Γ v (βTyΠ A B) -> 
    wf_βtmpl (βCtxU (βCtxU Γ A) B) Z T Σ -> 
    wf_βtmpl Γ Z (βTΠMatch v T) Σ
| βWfTΣMatch Γ Z v A T1 B T2 Σ :
    vsynth Γ v (βTyΣ A B) -> 
    wf_βtmpl (βCtxU Γ A) Z T1 Σ -> 
    wf_βtmpl (βCtxU Γ B) Z T2 Σ -> 
    wf_βtmpl Γ Z (βTΣMatch v T1 T2) Σ
| βWfTListMatch Γ Z v T1 T2 A Σ :
    vsynth Γ v (βTyList A) -> 
    wf_βtmpl Γ Z T1 Σ -> 
    wf_βtmpl (βCtxU (βCtxU Γ A) (βTyList A)) Z T2 Σ ->  
    wf_βtmpl Γ Z (βTListMatch v T1 T2) Σ
| βWfTLetBind Γ Z c A T Σ :
    csynth Γ c (βCTy A βSigØ βEqsØ) ->
    wf_βtmpl (βCtxU Γ A) Z T Σ ->
    wf_βtmpl Γ Z (βTLetBind c T) Σ
| βWfTOp Γ Z op A_op B_op v T Σ :
    get_op_βtype Σ op = Some (A_op, B_op) -> 
    vcheck Γ v A_op ->
    wf_βtmpl (βCtxU Γ B_op) Z T Σ -> 
    wf_βtmpl Γ Z (βTOp op v T) Σ

with wf_βeqs : βeqs -> βsig -> Prop :=
| βWfEqsØ Σ : wf_βeqs βEqsØ Σ
| βWfEqsU E Γ Z T1 T2 Σ: 
    wf_βeqs E Σ -> wf_βctx Γ -> wf_βtctx Z -> wf_βsig Σ ->
    wf_βtmpl Γ Z T1 Σ -> wf_βtmpl Γ Z T2 Σ -> 
    wf_βeqs (βEqsU E Γ Z T1 T2) Σ

(* ==================== Type Judgements ==================== *)

with vsynth : βctx -> βval -> βvtype -> Prop :=
| SynthV Γ v A : wf_βctx Γ ->  wf_βvtype A -> vsynth' Γ v A -> vsynth Γ v A

with vsynth' : βctx -> βval -> βvtype -> Prop :=
| SynthUnit Γ : vsynth' Γ βUnit βTyUnit 
| SynthInt Γ n : vsynth' Γ (βInt n) βTyInt
| SynthVar Γ n A :
    get_βvtype Γ n = Some A ->
    vsynth' Γ (βVar n) A
| SynthPair Γ v1 v2 A B :
    vsynth Γ v1 A ->
    vsynth Γ v2 B ->
    vsynth' Γ (βPair v1 v2) (βTyΠ A B)
| SynthListCons Γ v vs A :
    vsynth Γ v A ->
    vcheck Γ vs (βTyList A) ->
    vsynth' Γ (βListCons v vs) (βTyList A)
| SynthAnnV Γ v A :
    vcheck Γ v A ->
    vsynth' Γ (βAnnV v A) A

with csynth : βctx -> βcomp -> βctype -> Prop :=
| SynthC Γ c C : wf_βctx Γ ->  wf_βctype C -> csynth' Γ c C -> csynth Γ c C

with csynth' : βctx -> βcomp -> βctype -> Prop :=
| SynthRet Γ v A : 
    vsynth Γ v A ->
    csynth' Γ (βRet v) (βCTy A βSigØ βEqsØ)
| SynthΠMatch Γ v A B c C :
    vsynth Γ v (βTyΠ A B) ->
    csynth (βCtxU (βCtxU Γ A) B) c C ->
    csynth' Γ (βΠMatch v c) C
| SynthApp Γ v1 v2 A C :
    vsynth Γ v1 (βTyFun A C) ->
    vcheck Γ v2 A ->
    csynth' Γ (βApp v1 v2) C
| SynthHandle Γ v c C D :
    vsynth Γ v (βTyHandler C D) ->
    ccheck Γ c C ->
    csynth' Γ (βHandle v c) D
| SynthLetRec Γ A C c1 c2 D:
    ccheck (βCtxU (βCtxU Γ A) (βTyFun A C)) c1 C ->
    csynth (βCtxU Γ (βTyFun A C)) c2 D ->
    csynth' Γ (βLetRec (βTyFun A C) c1 c2) D
| SynthAnnC Γ c C :
    ccheck Γ c C ->
    csynth' Γ (βAnnC c C) C

with vcheck : βctx -> βval -> βvtype -> Prop :=
| CheckV Γ v A : wf_βctx Γ ->  wf_βvtype A -> vcheck' Γ v A -> vcheck Γ v A

with vcheck' : βctx -> βval -> βvtype -> Prop :=
| CheckVBySynth Γ v A A':
    vsynth Γ v A' -> βvsubtype A' A -> vcheck' Γ v A
| CheckInl Γ v A B :
    vcheck Γ v A ->
    vcheck' Γ (βInl v) (βTyΣ A B)
| CheckInr Γ v A B :
    vcheck Γ v B ->
    vcheck' Γ (βInr v) (βTyΣ A B)
| CheckListNil Γ A :
    vcheck' Γ βListNil (βTyList A)
| CheckFun Γ c A C :
    ccheck (βCtxU Γ A) c C ->
    vcheck' Γ (βFun c) (βTyFun A C)
| CheckHandler Γ cr h A Σ E D :
    ccheck (βCtxU Γ A) cr D ->
    hcheck Γ h Σ D ->
    vcheck' Γ (βHandler cr h) (βTyHandler (βCTy A Σ E) D)

with ccheck : βctx -> βcomp -> βctype -> Prop :=
| CheckC Γ c C : wf_βctx Γ ->  wf_βctype C -> ccheck' Γ c C -> ccheck Γ c C

with ccheck' : βctx -> βcomp -> βctype -> Prop :=
| CheckCBySynth Γ c C C' : 
    csynth Γ c C' -> βcsubtype C' C -> ccheck' Γ c C
| CheckΣMatch Γ v A B cl cr C :
    vsynth Γ v (βTyΣ A B) ->
    ccheck (βCtxU Γ A) cl C ->
    ccheck (βCtxU Γ B) cr C ->
    ccheck' Γ (βΣMatch v cl cr) C
| CheckListMatch Γ v A c1 c2 C :
    vsynth Γ v (βTyList A) ->
    ccheck Γ c1 C ->
    ccheck (βCtxU (βCtxU Γ A) (βTyList A)) c2 C ->
    ccheck' Γ (βListMatch v c1 c2) C
| CheckDoBind Γ c1 c2 A B Σ E :
    csynth Γ c1 (βCTy A Σ E) ->
    ccheck (βCtxU Γ A) c2 (βCTy B Σ E) ->
    ccheck' Γ (βDoBind c1 c2) (βCTy B Σ E)
| CheckOp Γ op_id v c A_op B_op A Σ E :
    get_op_βtype Σ op_id = Some (A_op, B_op) ->
    vcheck Γ v A_op ->
    ccheck (βCtxU Γ B_op) c (βCTy A Σ E) ->
    ccheck' Γ (βOp op_id v c) (βCTy A Σ E)

with hcheck :βctx -> βhcases -> βsig -> βctype -> Prop :=
| CheckH Γ h Σ D :
    wf_βctx Γ -> wf_βsig Σ -> wf_βctype D -> hcheck' Γ h Σ D -> hcheck Γ h Σ D

with hcheck' : βctx -> βhcases -> βsig -> βctype -> Prop :=
| CheckCasesØ Γ D : hcheck' Γ βCasesØ βSigØ D
| CheckCasesU Γ h op_id c_op A_op B_op Σ D :
    get_βcase h op_id = None ->
    hcheck Γ h Σ D ->
    ccheck (βCtxU (βCtxU Γ (βTyFun B_op D)) A_op) c_op D ->
    hcheck' 
      Γ (βCasesU h op_id c_op)
      (βSigU Σ op_id A_op B_op) D
.