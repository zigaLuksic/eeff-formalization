Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export syntax.


(* Syntax Definitions *)
Inductive τval : Type :=
| τVar : var_id -> τval
| τUnit : τval
| τInt : Z.t -> τval
| τInl : τval -> τval
| τInr : τval -> τval
| τPair : τval -> τval -> τval
| τFun : var_name -> τcomp -> τval
| τHandler : var_name -> τcomp -> τhcases -> τval
| τAnnV : τval -> τvtype -> τval

with τcomp : Type :=
| τRet : τval -> τcomp
| τAbsurd : τval -> τcomp
| τΠMatch : τval -> var_name -> var_name -> τcomp -> τcomp (* x~1 y~0 *)
| τΣMatch : τval -> var_name -> τcomp -> var_name -> τcomp -> τcomp
| τApp : τval -> τval -> τcomp
| τOp : op_id -> τval -> var_name -> τcomp -> τcomp (* x~1 k~0 *)
| τLetRec : var_name -> var_name -> τvtype -> τcomp -> τcomp -> τcomp (* f~0 x~1 *)
| τDoBind : var_name -> τcomp -> τcomp -> τcomp
| τHandle : τval -> τcomp -> τcomp
| τAnnC : τcomp -> τctype -> τcomp

with τhcases : Type :=
| τCasesØ : τhcases
| τCasesU : τhcases -> op_id -> var_name -> var_name -> τcomp -> τhcases

with τvtype : Type :=
| τTyUnit : τvtype
| τTyInt : τvtype
| τTyØ : τvtype
| τTyΣ : τvtype -> τvtype -> τvtype
| τTyΠ : τvtype -> τvtype -> τvtype
| τTyFun : τvtype -> τctype -> τvtype
| τTyHandler : τctype -> τctype -> τvtype

with τctype : Type :=
| τCTy : τvtype -> τsig -> τeqs -> τctype

with τsig : Type :=
| τSigØ : τsig
| τSigU : τsig -> op_id -> τvtype -> τvtype -> τsig

with τctx : Type :=
| τCtxØ : τctx
| τCtxU : τctx -> τvtype -> τctx

with τtctx : Type :=
| τTCtxØ : τtctx
| τTCtxU : τtctx -> τvtype -> τtctx

with τtmpl : Type :=
| τTApp : var_id -> τval -> τtmpl
| τTAbsurd : τval -> τtmpl
| τTΠMatch : τval -> var_name -> var_name -> τtmpl -> τtmpl
| τTΣMatch : τval -> var_name -> τtmpl -> var_name -> τtmpl -> τtmpl
| τTOp : op_id -> τval -> var_name -> τtmpl -> τtmpl

with τeqs : Type := 
| τEqsØ : τeqs
| τEqsU : τeqs -> τctx -> τtctx -> τtmpl -> τtmpl -> τeqs
.


(* Auxiliary Function Definitions *)

Fixpoint get_τvtype Γ i :=
  match Γ, i with
  | τCtxØ , _=> None
  | τCtxU Γ' A, 0 => Some A
  | τCtxU Γ' A, S i' =>  get_τvtype Γ' i'
  end.

Fixpoint get_τttype Z i :=
  match Z, i with
  | τTCtxØ , _=> None
  | τTCtxU Z' A, 0 => Some A
  | τTCtxU Z' A, S i' =>  get_τttype Z' i'
  end.


Fixpoint get_op_τtype Σ op :=
  match Σ with
  | τSigØ => None
  | τSigU Σ' op' A B =>
      if op == op' then Some (A, B)
      else get_op_τtype Σ' op
  end.


Fixpoint find_op_τcase h op : option (var_name * var_name * τcomp) :=
  match h with
  | τCasesØ => None
  | τCasesU h_others op' x_op k_op c_op =>
      if op == op' then Some (x_op, k_op, c_op)
      else find_op_τcase h_others op
  end.


Fixpoint τhas_eq E Γ Z T1 T2 :=
  match E with
  | τEqsØ => False
  | τEqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ τhas_eq E' Γ Z T1 T2
  end.



Inductive τvsubtype : τvtype -> τvtype -> Prop :=
| τSubtypeUnit : τvsubtype τTyUnit τTyUnit
| τSubtypeInt : τvsubtype τTyInt τTyInt
| τSubtypeTyØ : τvsubtype τTyØ τTyØ
| τSubtypeTyΣ A A' B B' : 
    τvsubtype A A' -> τvsubtype B B' -> 
    τvsubtype (τTyΣ A B) (τTyΣ A' B')
| τSubtypeTyΠ A A' B B' : 
    τvsubtype A A' -> τvsubtype B B' -> 
    τvsubtype (τTyΠ A B) (τTyΠ A' B')
| τSubtypeTyFun A A' C C' : 
    τvsubtype A' A -> τcsubtype C C' -> 
    τvsubtype (τTyFun A C) (τTyFun A' C')
| τSubtypeTyHandler C C' D D': 
    τcsubtype C' C -> τcsubtype D D' -> 
    τvsubtype (τTyHandler C D) (τTyHandler C' D')

with τcsubtype : τctype -> τctype -> Prop  :=
| τSubtypeCTy A A' Σ Σ' E E': 
    τvsubtype A A' -> τsig_subtype Σ Σ' -> τeqs_subtype E E' ->
    τcsubtype (τCTy A Σ E) (τCTy A' Σ' E')

with τsig_subtype : τsig -> τsig -> Prop :=
| τSubtypeSigØ Σ: τsig_subtype τSigØ Σ
| τSubtypeSigU Σ Σ' op A B A' B' : 
    τsig_subtype Σ Σ' -> get_op_τtype Σ' op = Some (A', B') -> 
    τvsubtype A A' -> τvsubtype B' B ->
    τsig_subtype (τSigU Σ op A B) Σ'

with τeqs_subtype : τeqs -> τeqs -> Prop :=
| τSubtypeEqsØ E: τeqs_subtype τEqsØ E
| τSubtypeEqsU E E' Γ Z T1 T2 : 
    τeqs_subtype E E' -> τhas_eq E' Γ Z T1 T2 ->
    τeqs_subtype (τEqsU E Γ Z T1 T2) E'
.

Inductive τctx_subtype : τctx -> τctx -> Prop :=
| τSubtypeCtxØ : τctx_subtype τCtxØ τCtxØ
| τSubtypeCtxU Γ Γ' A A' : 
    τctx_subtype Γ Γ' -> τvsubtype A A' ->
    τctx_subtype (τCtxU Γ A) (τCtxU Γ' A')
.


Inductive wf_τvtype : τvtype -> Prop :=
| τWfUnit : wf_τvtype τTyUnit 
| τWfInt : wf_τvtype τTyInt
| τWfEmpty : wf_τvtype τTyØ
| τWfTyΣ A B: wf_τvtype A -> wf_τvtype B -> wf_τvtype (τTyΣ A B)
| τWfTyΠ A B : wf_τvtype A -> wf_τvtype B -> wf_τvtype (τTyΠ A B)
| τWfTyFun A C : wf_τvtype A -> wf_τctype C -> wf_τvtype (τTyFun A C)
| τWfTyHandler C D : wf_τctype C -> wf_τctype D -> wf_τvtype (τTyHandler C D)

with wf_τctype : τctype -> Prop :=
| τWfCTy A Σ E : wf_τvtype A -> wf_τsig Σ -> wf_τeqs E Σ -> 
  wf_τctype (τCTy A Σ E)
    
with wf_τsig : τsig -> Prop :=
| τWfSigØ : wf_τsig τSigØ
| τWfSigU Σ op Aop Bop: 
    wf_τsig Σ -> get_op_τtype Σ op = None ->
    wf_τvtype Aop -> wf_τvtype Bop -> wf_τsig (τSigU Σ op Aop Bop)

with wf_τctx : τctx -> Prop :=
| τWfCtxØ : wf_τctx τCtxØ
| τWfCtxU Γ A : wf_τctx Γ -> wf_τvtype A -> wf_τctx (τCtxU Γ A)

with wf_τtctx : τtctx -> Prop :=
| τWfTCtxØ : wf_τtctx τTCtxØ
| τWfTCtxU Γ A : wf_τtctx Γ -> wf_τvtype A -> wf_τtctx (τTCtxU Γ A)

with wf_τtmpl : τctx -> τtctx -> τtmpl -> τsig -> Prop :=
| τWfTApp Γ Z name num v A Σ : 
    vcheck Γ v A -> get_τttype Z num = Some A ->
    wf_τtmpl Γ Z (τTApp (name, num) v) Σ
| τWfTAbsurd Γ Z v Σ :
    vcheck Γ v τTyØ -> wf_τtmpl Γ Z (τTAbsurd v) Σ 
| τWfTΠMatch Γ Z v A B x y T Σ :
    vcheck Γ v (τTyΠ A B) -> wf_τtmpl (τCtxU (τCtxU Γ A) B) Z T Σ -> 
    wf_τtmpl Γ Z (τTΠMatch v x y T) Σ
| τWfTΣMatch Γ Z v x A Tl y B Tr Σ :
    vcheck Γ v (τTyΣ A B) -> wf_τtmpl (τCtxU Γ A) Z Tl Σ -> 
    wf_τtmpl (τCtxU Γ B) Z Tr Σ -> wf_τtmpl Γ Z (τTΣMatch v x Tl y Tr) Σ
| τWfTOp Γ Z op A_op B_op v y T Σ :
    get_op_τtype Σ op = Some (A_op, B_op) -> vcheck Γ v A_op ->
    wf_τtmpl (τCtxU Γ B_op) Z T Σ -> wf_τtmpl Γ Z (τTOp op v y T) Σ

with wf_τeqs : τeqs -> τsig -> Prop :=
| τWfEqsØ Σ : wf_τeqs τEqsØ Σ
| τWfEqsU E Γ Z T1 T2 Σ: 
    wf_τeqs E Σ -> wf_τctx Γ -> wf_τtctx Z -> wf_τsig Σ ->
    wf_τtmpl Γ Z T1 Σ -> wf_τtmpl Γ Z T2 Σ -> 
    wf_τeqs (τEqsU E Γ Z T1 T2) Σ

with vsynth : τctx -> τval -> τvtype -> Prop :=
| SynthV Γ v A : wf_τctx Γ ->  wf_τvtype A -> vsynth' Γ v A -> vsynth Γ v A

with vsynth' : τctx -> τval -> τvtype -> Prop :=
| SynthUnit Γ : vsynth' Γ τUnit τTyUnit 
| SynthInt Γ n : vsynth' Γ (τInt n) τTyInt
| SynthVar Γ name num A :
    get_τvtype Γ num = Some A ->
    vsynth' Γ (τVar (name, num)) A
| SynthPair Γ v1 v2 A B :
    vsynth Γ v1 A ->
    vsynth Γ v2 B ->
    vsynth' Γ (τPair v1 v2) (τTyΠ A B)
| SynthVAnnot Γ v A :
    vcheck Γ v A ->
    vsynth' Γ (τAnnV v A) A

with csynth : τctx -> τcomp -> τctype -> Prop :=
| SynthC Γ c C : wf_τctx Γ ->  wf_τctype C -> csynth' Γ c C -> csynth Γ c C

with csynth' : τctx -> τcomp -> τctype -> Prop :=
| SynthRet Γ v A : 
    vsynth Γ v A ->
    csynth' Γ (τRet v) (τCTy A τSigØ τEqsØ)
| SynthΠMatch Γ v A B x y c C :
    vsynth Γ v (τTyΠ A B) ->
    csynth (τCtxU (τCtxU Γ A) B) c C ->
    csynth' Γ (τΠMatch v x y c) C
| SynthApp Γ v1 v2 A C :
    vsynth Γ v1 (τTyFun A C) ->
    vcheck Γ v2 A ->
    csynth' Γ (τApp v1 v2) C
| SynthHandle Γ v c C D :
    vsynth Γ v (τTyHandler C D) ->
    ccheck Γ c C ->
    csynth' Γ (τHandle v c) D
| SynthLetRec Γ f x A C c1 c2 D:
    ccheck (τCtxU (τCtxU Γ A) (τTyFun A C)) c1 C ->
    csynth (τCtxU Γ (τTyFun A C)) c2 D ->
    csynth' Γ (τLetRec f x (τTyFun A C) c1 c2) D
| SynthCAnnot Γ c C :
    ccheck Γ c C ->
    csynth' Γ (τAnnC c C) C

with vcheck : τctx -> τval -> τvtype -> Prop :=
| CheckV Γ v A : wf_τctx Γ ->  wf_τvtype A -> vcheck' Γ v A -> vcheck Γ v A

with vcheck' : τctx -> τval -> τvtype -> Prop :=
| CheckVBySynth Γ v A A':
    vsynth Γ v A' -> τvsubtype A' A -> vcheck' Γ v A
| CheckInl Γ v A B :
    vcheck Γ v A ->
    vcheck' Γ (τInl v) (τTyΣ A B)
| CheckInr Γ v A B :
    vcheck Γ v B ->
    vcheck' Γ (τInr v) (τTyΣ A B)
| CheckFun Γ x c A C :
    ccheck (τCtxU Γ A) c C ->
    vcheck' Γ (τFun x c) (τTyFun A C)
| CheckHandler Γ x c_ret h A Σ E D :
    ccheck (τCtxU Γ A) c_ret D ->
    hcheck Γ h Σ D ->
    vcheck' Γ (τHandler x c_ret h) (τTyHandler (τCTy A Σ E) D)

with ccheck : τctx -> τcomp -> τctype -> Prop :=
| CheckC Γ c C : wf_τctx Γ ->  wf_τctype C -> ccheck' Γ c C -> ccheck Γ c C

with ccheck' : τctx -> τcomp -> τctype -> Prop :=
| CheckCBySynth Γ c C C' : 
    csynth Γ c C' -> τcsubtype C' C -> ccheck' Γ c C
| CheckΣMatch Γ v A B xl cl xr cr C :
    vsynth Γ v (τTyΣ A B) ->
    ccheck (τCtxU Γ A) cl C ->
    ccheck (τCtxU Γ B) cr C ->
    ccheck' Γ (τΣMatch v xl cl xr cr) C
| CheckDoBind Γ x c1 c2 A B Σ E :
    csynth Γ c1 (τCTy A Σ E) ->
    ccheck (τCtxU Γ A) c2 (τCTy B Σ E) ->
    ccheck' Γ (τDoBind x c1 c2) (τCTy B Σ E)
| CheckOp Γ op_id v y c A_op B_op A Σ E :
    get_op_τtype Σ op_id = Some (A_op, B_op) ->
    vcheck Γ v A_op ->
    ccheck (τCtxU Γ B_op) c (τCTy A Σ E) ->
    ccheck' Γ (τOp op_id v y c) (τCTy A Σ E)

with hcheck :τctx -> τhcases -> τsig -> τctype -> Prop :=
| CheckH Γ h Σ D :
    wf_τctx Γ -> wf_τsig Σ -> wf_τctype D -> hcheck' Γ h Σ D -> hcheck Γ h Σ D

with hcheck' : τctx -> τhcases -> τsig -> τctype -> Prop :=
| CheckCasesØ Γ D : hcheck' Γ τCasesØ τSigØ D
| CheckCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_op_τcase h op_id = None ->
    hcheck Γ h Σ D ->
    ccheck (τCtxU (τCtxU Γ (τTyFun B_op D)) A_op) c_op D ->
    hcheck' 
      Γ (τCasesU h op_id x k c_op)
      (τSigU Σ op_id A_op B_op) D
.