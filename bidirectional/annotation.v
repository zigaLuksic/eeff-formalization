(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\bidirectional". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\bidirectional".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Require Import syntax syntax_lemmas bidirectional declarational subtyping_lemmas.


(* ATTEMPT AT PROVIDING AN ANNOTATION SCHEME. STUCK DUE TO PROOF RELEVANCE GIVING ME PROBLEMS. *)

(* ==================== Annotation ==================== *)


Inductive v_ann : forall Γ v A, has_vtype Γ v A -> βval -> Prop :=
| AnnVar Γ x n A p:
    get_vtype Γ n = Some A ->
    v_ann Γ (Var (x, n)) A p (βVar (x, n))
| AnnUnit Γ p: 
    v_ann Γ Unit TyUnit p βUnit
| AnnInt Γ n p: 
    v_ann Γ (Int n) TyInt p (βInt n)
| AnnPair Γ v1 v2 A B v1' v2' p1 p2 p:
    v_ann Γ v1 A p1 v1' -> v_ann Γ v2 B p2 v2' ->
    v_ann Γ (Pair v1 v2) (TyΠ A B) p (βPair v1' v2')
| AnnInl Γ v A B A' B' v' pl p wfa wfb:
    v_ann Γ v A pl v' -> vtype_ann A wfa A' -> vtype_ann B wfb B' ->
    v_ann Γ (Inl v) (TyΣ A B) p (βAnnV (βInl v') (βTyΣ A' B'))
| AnnInr Γ v A B A' B' v' pr p wfa wfb:
    v_ann Γ v B pr v' -> vtype_ann A wfa A' -> vtype_ann B wfb B' ->
    v_ann Γ (Inr v) (TyΣ A B) p (βAnnV (βInr v') (βTyΣ A' B'))
| AnnFun Γ x c A C A' C' c' pc p wfa wfc:
    c_ann (CtxU Γ A) c C pc c' -> vtype_ann A wfa A' -> ctype_ann C wfc C' ->
    v_ann Γ (Fun x c) (TyFun A C) p (βAnnV (βFun x c') (βTyFun A' C'))
| AnnHandler Γ x c c' h h' A A' Σ Σ' E E' D D' ' pc ph p wfa wfs wfe wfd:
    c_ann (CtxU Γ A) c D pc c' -> h_ann Γ h Σ D ph h' ->
    vtype_ann A wfa A' -> sig_ann Σ wfs Σ' -> eqs_ann E Σ wfe E' -> 
    ctype_ann D wfd D' ->
    v_ann Γ (Handler x c h) (TyHandler (CTy A Σ E) D) p
      (βAnnV (βHandler x c' h') (βTyHandler (βCTy A' Σ' E') D')) 
| AnnVSubtype Γ v v' A1 A2 A2' p wfg wft sty wfa2:
    v_ann Γ v A1 p v' -> wf_vtype A1 -> vtype_ann A2 wfa2 A2' ->
    v_ann Γ v A2 
      (TypeV Γ v A2 wfg wft (TypeVSubtype Γ v A1 A2 p sty)) (βAnnV v' A2')

with c_ann : forall Γ c C, has_ctype Γ c C -> βcomp -> Prop :=
| AnnRet Γ v v' A A' pv p wfa :
    v_ann Γ v A pv v' -> vtype_ann A wfa A' ->
    c_ann Γ (Ret v) (CTy A SigØ EqsØ) p (βRet v')
| AnnAbsurd Γ v v' C C' pv p wfc :
    v_ann Γ v TyØ pv v' -> ctype_ann C wfc C' ->
    c_ann Γ (Absurd v) C p (βAnnC (βAbsurd v') C')
| AnnΠMatch Γ v v' A B x y c c' C pv pc p:
    v_ann Γ v (TyΠ A B) pv v' -> c_ann (CtxU (CtxU Γ A) B) c C pc c'->
    c_ann Γ (ΠMatch v x y c) C p (βΠMatch v' x y c')
| AnnΣMatch Γ v v' A B x c1 c1' y c2 c2' C C' p pv wfc pc1 pc2:
    v_ann Γ v (TyΣ A B) pv v' -> ctype_ann C wfc C' ->
    c_ann (CtxU Γ A) c1 C pc1 c1' -> c_ann (CtxU Γ B) c2 C pc2 c2' ->
    c_ann Γ (ΣMatch v x c1 y c2) C p (βAnnC (βΣMatch v' x c1' y c2') C')
| AnnDoBind Γ x c1 c1' c2 c2' A B Σ E p pc1 pc2:
    c_ann Γ c1 (CTy A Σ E) pc1 c1' -> c_ann (CtxU Γ A) c2 (CTy B Σ E) pc2 c2' ->
    c_ann Γ (DoBind x c1 c2) (CTy B Σ E) p (βDoBind x c1' c2')
| AnnApp Γ v1 v1' v2 v2' A C pv1 pv2 p:
    v_ann Γ v1 (TyFun A C) pv1 v1' -> v_ann Γ v2 A pv2 v2' ->
    c_ann Γ (App v1 v2) C p (βApp v1' v2')
| AnnHandle Γ v v' c c' C D pv pc p:
    v_ann Γ v (TyHandler C D) pv v' -> c_ann Γ c C pc c' ->
    c_ann Γ (Handle v c) D p (βHandle v' c')
| AnnLetRec Γ f x c1 c1' c2 c2' A A' C C' D pc1 pc2 p wfa wfc:
    c_ann (CtxU (CtxU Γ A) (TyFun A C)) c1 C pc1 c1' ->
    c_ann (CtxU Γ (TyFun A C)) c2 D pc2 c2' -> 
    vtype_ann A wfa A' -> ctype_ann C wfc C' ->
    c_ann Γ (LetRec f x c1 c2) D p (βLetRec f x (βTyFun A' C') c1' c2')
| AnnOp Γ op v v' y c c' A A' Σ Σ' E E' Aop Bop pv pc p wfa wfs wfe :
    get_op_type Σ op = Some (Aop, Bop) ->
    vtype_ann A wfa A' -> sig_ann Σ wfs Σ' -> eqs_ann E Σ wfe E' ->
    v_ann Γ v Aop pv v' -> c_ann (CtxU Γ Bop) c (CTy A Σ E) pc c' ->
    c_ann Γ (Op op v y c) (CTy A Σ E) p (βAnnC (βOp op v' y c') (βCTy A' Σ' E'))
| AnnCSubtype Γ c c' C1 C2 C2' p wfg wft sty wfc2 :
    c_ann Γ c C1 p c' -> wf_ctype C1 -> ctype_ann C2 wfc2 C2' ->
    c_ann Γ c C2 
      (TypeC Γ c C2 wfg wft (TypeCSubtype Γ c C1 C2 p sty)) (βAnnC c' C2')

with h_ann : forall Γ h Σ D, has_htype Γ h Σ D -> βhcases -> Prop := 
| AnnCasesØ Γ Σ D p:
    h_ann Γ CasesØ Σ D p βCasesØ
| AnnCasesU Γ Σ D h h' c c' A B op x k ph pc p:
    h_ann Γ h Σ D ph h' ->
    c_ann (CtxU (CtxU Γ (TyFun B D)) A) c D pc c' ->
    h_ann Γ (CasesU h op x k c) (SigU Σ op A B) D p (βCasesU h' op x k c')

with vtype_ann : forall A, wf_vtype A -> βvtype -> Prop :=
| AnnTyUnit : 
    vtype_ann TyUnit WfUnit βTyUnit
| AnnTyInt : 
    vtype_ann TyInt WfInt βTyInt
| AnnTyØ : 
    vtype_ann TyØ WfEmpty βTyØ
| AnnTyΠ A B A' B' wfa wfb: 
    vtype_ann A wfa A' -> vtype_ann B wfb B' ->
    vtype_ann (TyΠ A B) (WfTyΠ A B wfa wfb) (βTyΠ A' B')
| AnnTyΣ A B A' B' wfa wfb: 
    vtype_ann A wfa A' -> vtype_ann B wfb B' -> 
    vtype_ann (TyΣ A B) (WfTyΣ A B wfa wfb) (βTyΣ A' B')
| AnnTyFun A C A' C' wfa wfc:
    vtype_ann A wfa A' -> ctype_ann C wfc C' -> 
    vtype_ann (TyFun A C) (WfTyFun A C wfa wfc) (βTyFun A' C')
| AnnTyHandler C D C' D' wfc wfd: 
    ctype_ann C wfc C' -> ctype_ann D wfd D' -> 
    vtype_ann (TyHandler C D) (WfTyHandler C D wfc wfd) (βTyHandler C' D')

with ctype_ann : forall C, wf_ctype C -> βctype -> Prop :=
| AnnCTy A A' Σ Σ' E E' wfa wfs wfe wfc:
    vtype_ann A wfa A' -> sig_ann Σ wfs Σ' -> eqs_ann E Σ wfe E' ->
    ctype_ann (CTy A Σ E) wfc (βCTy A' Σ' E')

with sig_ann : forall Σ, wf_sig Σ -> βsig -> Prop :=
| AnnSigØ:
    sig_ann SigØ WfSigØ βSigØ
| AnnSigU Σ Σ' A A' B B' op wfs wfa wfb wf:
    vtype_ann A wfa A' -> vtype_ann B wfb B' -> sig_ann Σ wfs Σ' ->
    sig_ann (SigU Σ op A B) wf (βSigU Σ' op A' B')

with eqs_ann : forall E Σ, wf_eqs E Σ -> βeqs -> Prop :=
| AnnEqsØ Σ:
    eqs_ann EqsØ Σ (WfEqsØ Σ) βEqsØ
| AnnEqsU Σ T1 T1' T2 T2' E E' Z Z' Γ Γ' wft1 wft2 wfe wfg wfz wf:
    tmpl_ann Γ Z T1 Σ wft1 T1' -> tmpl_ann Γ Z T2 Σ wft2 T2' ->
    eqs_ann E Σ wfe E' -> ctx_ann Γ wfg Γ' -> tctx_ann Z wfz Z' ->
    eqs_ann (EqsU E Γ Z T1 T2) Σ wf (βEqsU E' Γ' Z' T1' T2')

with tmpl_ann : forall Γ Z T Σ, wf_tmpl Γ Z T Σ -> βtmpl -> Prop:=
| AnnTApp Γ Z Σ z i v v' A pv wf:
    get_ttype Z i = Some A ->
    v_ann Γ v A pv v' ->
    tmpl_ann Γ Z (TApp (z, i) v) Σ wf (βTApp (z, i) v')
| AnnTAbsurd Γ Z Σ v v' pv wf:
    v_ann Γ v TyØ pv v' ->
    tmpl_ann Γ Z (TAbsurd v) Σ wf (βTAbsurd v')
| AnnTΠMatch Γ Z Σ v v' A B x y T T' pv wft wf:
    v_ann Γ v (TyΠ A B) pv v' ->
    tmpl_ann (CtxU (CtxU Γ A) B) Z T Σ wft T' ->
    tmpl_ann Γ Z (TΠMatch v x y T) Σ wf (βTΠMatch v' x y T')
| AnnTΣMatch Γ Z Σ v v' A B x y Tl Tr Tl' Tr' pv wftl wftr wf:
    v_ann Γ v (TyΣ A B) pv v' ->
    tmpl_ann (CtxU Γ A) Z Tl Σ wftl Tl' ->
    tmpl_ann (CtxU Γ B) Z Tr Σ wftr Tr' ->
    tmpl_ann Γ Z (TΣMatch v x Tl y Tr) Σ wf (βTΣMatch v' x Tl' y Tr')
| AnnTOp Γ Z Σ op v v' A B y T T' pv wft wf:
    get_op_type Σ op = Some (A, B) -> v_ann Γ v A pv v' ->
    tmpl_ann (CtxU Γ B) Z T Σ wft T' ->
    tmpl_ann Γ Z (TOp op v y T) Σ wf (βTOp op v' y T')

with ctx_ann : forall Γ, wf_ctx Γ -> βctx -> Prop := 
| AnnCtxØ : ctx_ann CtxØ WfCtxØ βCtxØ
| AnnCtxU Γ Γ' A A' wfa wfg wfga: 
    vtype_ann A wfa A' -> ctx_ann Γ wfg Γ' ->
    ctx_ann (CtxU Γ A) wfga (βCtxU Γ' A') 

with tctx_ann : forall Z, wf_tctx Z -> βtctx -> Prop := 
| AnnTCtxØ : tctx_ann TCtxØ WfTCtxØ βTCtxØ
| AnnTCtxU Z Z' A A' wfa wfz wfza: 
    vtype_ann A wfa A' -> tctx_ann Z wfz Z' ->
    tctx_ann (TCtxU Z A) wfza (βTCtxU Z' A') 
.


(* ==================== Annotation Existance, Uniqueness ==================== *)

Fixpoint v_ann_unique Γ v A p v1 v2:
  v_ann Γ v A p v1 -> v_ann Γ v A p v2 -> v1 = v2
with c_ann_unique Γ c C p c1 c2:
  c_ann Γ c C p c1 -> c_ann Γ c C p c2 -> c1 = c2
with h_ann_unique Γ h Σ D p h1 h2:
  h_ann Γ h Σ D p h1 -> h_ann Γ h Σ D p h2 -> h1 = h2
with vtype_ann_unique A wfa A1 A2:
  vtype_ann A wfa A1 -> vtype_ann A wfa A2 -> A1 = A2
with ctype_ann_unique C wfc C1 C2:
  ctype_ann C wfc C1 -> ctype_ann C wfc C2 -> C1 = C2
with sig_ann_unique Σ wfs Σ1 Σ2:
  sig_ann Σ wfs Σ1 -> sig_ann Σ wfs Σ2 -> Σ1 = Σ2
with eqs_ann_unique E Σ wfe E1 E2:
  eqs_ann E Σ wfe E1 -> eqs_ann E Σ wfe E2 -> E1 = E2
with tmpl_ann_unique Γ Z T Σ wf T1 T2:
  tmpl_ann Γ Z T Σ wf T1 -> tmpl_ann Γ Z T Σ wf T2 -> T1 = T2
with ctx_ann_unique Γ wf Γ1 Γ2:
  ctx_ann Γ wf Γ1 -> ctx_ann Γ wf Γ2 -> Γ1 = Γ2
with tctx_ann_unique Z wf Z1 Z2:
  tctx_ann Z wf Z1 -> tctx_ann Z wf Z2 -> Z1 = Z2.
Proof.
all: admit.
Admitted.


Fixpoint v_ann_exists Γ v A (p : has_vtype Γ v A):
  exists v', v_ann Γ v A p v' 
with c_ann_exists Γ c C (p : has_ctype Γ c C):
  exists c', c_ann Γ c C p c' 
with h_ann_exists Γ h Σ D (p : has_htype Γ h Σ D):
  exists h', h_ann Γ h Σ D p h' 
with vtype_ann_exists A (wf : wf_vtype A):
  exists A', vtype_ann A wf A'
with ctype_ann_exists C (wf : wf_ctype C):
  exists C', ctype_ann C wf C'
with sig_ann_exists Σ (wf : wf_sig Σ):
  exists Σ', sig_ann Σ wf Σ'
with eqs_ann_exists E Σ (wf : wf_eqs E Σ):
  exists E', eqs_ann E Σ wf E'
with tmpl_ann_exists Γ Z T Σ (wf : wf_tmpl Γ Z T Σ):
  exists T', tmpl_ann Γ Z T Σ wf T' 
with ctx_ann_exists Γ (wf : wf_ctx Γ):
  exists Γ', ctx_ann Γ wf Γ'
with tctx_ann_exists Z (wf : wf_tctx Z):
  exists Z', tctx_ann Z wf Z'.
Proof.
all: rename v_ann_exists into VL; rename c_ann_exists into CL.
all: rename h_ann_exists into HL; rename vtype_ann_exists into VTL.
all: rename ctype_ann_exists into CTL; rename sig_ann_exists into SL.
all: rename eqs_ann_exists into EL; rename tmpl_ann_exists into TL.
all: rename ctx_ann_exists into GL; rename tctx_ann_exists into ZL.
{
clear SL EL TL GL ZL.
destruct p.  destruct h.
+ clear VL CL HL. exists βUnit. apply AnnUnit.
+ clear VL CL HL. exists (βInt n). apply AnnInt.
+ clear VL CL HL. exists (βVar (x, n)). apply AnnVar. assumption.
+ specialize (VL _ _ _ h) as IH1.
  specialize (VL _ _ _ h0) as IH2.
  clear VL CL HL VTL CTL.
  destruct IH1 as [v1']. destruct IH2 as [v2'].
  exists (βPair v1' v2'). eapply AnnPair; eauto.
+ specialize (VL _ _ _ h) as IH.
  specialize (VTL _ w0) as IHT.
  clear VL CL HL VTL CTL.
  destruct IH as [v']. destruct IHT as [AB']. inv H0.
  exists (βAnnV (βInl v') (βTyΣ A' B')). eapply AnnInl; eauto.
+ specialize (VL _ _ _ h) as IH.
  specialize (VTL _ w0) as IHT.
  clear VL CL HL VTL CTL.
  destruct IH as [v']. destruct IHT as [AB']. inv H0.
  exists (βAnnV (βInr v') (βTyΣ A' B')). eapply AnnInr; eauto.
+ specialize (CL _ _ _ h) as IH.
  specialize (VTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IH as [c']. destruct IHt as [AC']. inv H0.
  exists (βAnnV (βFun x c') (βTyFun A' C')). eapply AnnFun; eauto.
+ specialize (CL _ _ _ h0) as IHc.
  specialize (HL _ _ _ _ h1) as IHh.
  specialize (VTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IHc as [c']. destruct IHh as [h']. destruct IHt as [CD']. 
  inv H1. inv H4.
  exists (βAnnV (βHandler x c' h') (βTyHandler (βCTy A' Σ' E') D')). 
  eapply AnnHandler; eauto.
+ specialize (VL _ _ _ h) as IH.
  specialize (VTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IH as [v']. destruct IHt as [AA'].
  exists (βAnnV v' AA'). eapply AnnVSubtype; eauto. clear H. inv h. assumption. 
}{
clear SL EL TL GL ZL.
destruct p. destruct h.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHt as [C']. inv H0.
  exists (βRet v'). eapply AnnRet; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHt as [C'].
  exists (βAnnC (βAbsurd v') C'). eapply AnnAbsurd; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CL _ _ _ h0) as IHc.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHc as [c'].
  exists (βΠMatch v' x y c'). eapply AnnΠMatch; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CL _ _ _ h0) as IHc1.
  specialize (CL _ _ _ h1) as IHc2.
  specialize (CTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHc1 as [c1']. 
  destruct IHc2 as [c2']. destruct IHt as [C'].
  exists (βAnnC (βΣMatch v' xl c1' xr c2') C'). eapply AnnΣMatch; eauto. 
+ specialize (CL _ _ _ h) as IHc1.
  specialize (CL _ _ _ h0) as IHc2.
  clear VL CL HL VTL CTL.
  destruct IHc1 as [c1']. destruct IHc2 as [c2'].
  exists (βDoBind x c1' c2'). eapply AnnDoBind; eauto.
+ specialize (VL _ _ _ h) as IHv1.
  specialize (VL _ _ _ h0) as IHv2.
  clear VL CL HL VTL CTL.
  destruct IHv1 as [v1']. destruct IHv2 as [v2'].
  exists (βApp v1' v2'). eapply AnnApp; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CL _ _ _ h0) as IHc.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHc as [c'].
  exists (βHandle v' c'). eapply AnnHandle; eauto.
+ assert (exists wa A', vtype_ann A wa A') as IHA.
  { inv h. inv H. inv H4. exists H6. apply VTL. }
  assert (exists wc C', ctype_ann C wc C') as IHC.
  { inv h. exists H0. apply CTL. }
  specialize (CL _ _ _ h) as IHc1.
  specialize (CL _ _ _ h0) as IHc2.
  clear VL CL HL VTL CTL.
  destruct IHc1 as [c1']. destruct IHc2 as [c2'].
  destruct IHA as [wfa [A']]. destruct IHC as [wfc [C']].
  exists (βLetRec f x (βTyFun A' C') c1' c2'). eapply AnnLetRec; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (CL _ _ _ h0) as IHc.
  specialize (CTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IHv as [v']. destruct IHc as [c']. destruct IHt as [C']. inv H1.
  exists (βAnnC (βOp op_id v' y c') (βCTy A' Σ' E')). eapply AnnOp; eauto.
+ specialize (CL _ _ _ h) as IH.
  specialize (CTL _ w0) as IHt.
  clear VL CL HL VTL CTL.
  destruct IH as [c']. destruct IHt as [CC'].
  exists (βAnnC c' CC'). eapply AnnCSubtype; eauto. clear H. inv h. assumption.
}{
clear SL EL TL GL ZL.
destruct p. destruct h0.
+ clear VL CL HL VTL CTL.
  exists βCasesØ. apply AnnCasesØ.
+ specialize (HL _ _ _ _ h0) as IHh.
  specialize (CL _ _ _ h1) as IHc.
  clear VL CL HL VTL CTL.
  destruct IHh as [h']. destruct IHc as [c'].
  exists (βCasesU h' op_id x k c'). eapply AnnCasesU; eauto.
}{
clear VL CL HL SL EL TL GL ZL.
destruct wf.
+ clear VTL CTL.
  exists βTyUnit. apply AnnTyUnit.
+ clear VTL CTL.
  exists βTyInt. apply AnnTyInt.
+ clear VTL CTL.
  exists βTyØ. apply AnnTyØ.
+ specialize (VTL _ wf1) as IH1.
  specialize (VTL _ wf2) as IH2.
  clear VTL CTL.
  destruct IH1 as [A']. destruct IH2 as [B'].
  exists (βTyΣ A' B'). apply AnnTyΣ; auto.
+ specialize (VTL _ wf1) as IH1.
  specialize (VTL _ wf2) as IH2.
  clear VTL CTL.
  destruct IH1 as [A']. destruct IH2 as [B'].
  exists (βTyΠ A' B'). apply AnnTyΠ; auto.
+ specialize (VTL _ wf) as IH1.
  specialize (CTL _ w) as IH2.
  clear VTL CTL.
  destruct IH1 as [A']. destruct IH2 as [C'].
  exists (βTyFun A' C'). apply AnnTyFun; auto.
+ specialize (CTL _ w) as IH1.
  specialize (CTL _ w0) as IH2.
  clear VTL CTL.
  destruct IH1 as [C']. destruct IH2 as [D'].
  exists (βTyHandler C' D'). apply AnnTyHandler; auto.
}{
clear VL CL HL TL GL ZL.
destruct wf.
specialize (VTL _ w) as IHa.
specialize (SL _ w0) as IHs.
specialize (EL _ _ w1) as IHe.
clear VTL CTL SL EL.
destruct IHa as [A']. destruct IHs as [Σ']. destruct IHe as [E'].
exists (βCTy A' Σ' E'). eapply AnnCTy; eauto.
}{
clear VL CL HL TL GL ZL.
destruct wf.
+ clear VTL CTL SL EL.
  exists βSigØ. apply AnnSigØ.
+ specialize (VTL _ w) as IHa.
  specialize (VTL _ w0) as IHb.
  specialize (SL _ wf) as IHs.
  clear VTL CTL SL EL.
  destruct IHs as [Σ']. destruct IHa as [A']. destruct IHb as [B'].
  exists (βSigU Σ' op A' B'). eapply AnnSigU; eauto.
}{
clear VL CL HL.
destruct wf.
+ clear VTL CTL SL EL TL GL ZL.
  exists βEqsØ. apply AnnEqsØ.
+ specialize (TL _ _ _ _ w2) as IH1.
  specialize (TL _ _ _ _ w3) as IH2.
  specialize (GL _ w) as IHg.
  specialize (ZL _ w0) as IHz.
  specialize (EL _ _ wf) as IHe.
  clear VTL CTL SL EL TL GL ZL.
  destruct IH1 as [T1']. destruct IH2 as [T2']. destruct IHg as [Γ'].
  destruct IHe as [E']. destruct IHz as [Z'].
  exists (βEqsU E' Γ' Z' T1' T2'). eapply AnnEqsU; eauto.
}{
clear VTL CTL SL EL GL ZL CL HL.
destruct wf.
+ specialize (VL _ _ _ h) as IHv.
  clear VL TL.
  destruct IHv as [v'].
  exists (βTApp (name, num) v'). eapply AnnTApp; eauto.
+ specialize (VL _ _ _ h) as IHv.
  clear VL TL.
  destruct IHv as [v'].
  exists (βTAbsurd v'). eapply AnnTAbsurd; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (TL _ _ _ _ wf) as IHt.
  clear VL TL.
  destruct IHv as [v']. destruct IHt as [T'].
  exists (βTΠMatch v' x y T'). eapply AnnTΠMatch; eauto.
+ specialize (VL _ _ _ h) as IHv.
  specialize (TL _ _ _ _ wf1) as IHTl.
  specialize (TL _ _ _ _ wf2) as IHTr.
  clear VL TL.
  destruct IHv as [v']. destruct IHTl as [Tl']. destruct IHTr as [Tr'].
  exists (βTΣMatch v' x Tl' y Tr'). eapply AnnTΣMatch; eauto. 
+ specialize (VL _ _ _ h) as IHv.
  specialize (TL _ _ _ _ wf) as IHT.
  clear VL TL.
  destruct IHv as [v']. destruct IHT as [T'].
  exists (βTOp op v' y T'). eapply AnnTOp; eauto.
}{
clear VL CL HL CTL SL EL TL ZL.
destruct wf.
+ clear VTL GL. exists βCtxØ. apply AnnCtxØ.
+ specialize (GL _ wf) as IHg.
  specialize (VTL _ w) as IHa.
  clear VTL GL.
  destruct IHg as [Γ']. destruct IHa as [A'].
  exists (βCtxU Γ' A'). eapply AnnCtxU; eauto.
}{
clear VL CL HL CTL SL EL TL GL.
destruct wf.
+ clear VTL ZL. exists βTCtxØ. apply AnnTCtxØ.
+ specialize (ZL _ wf) as IHz.
  specialize (VTL _ w) as IHa.
  clear VTL ZL.
  destruct IHz as [Z']. destruct IHa as [A'].
  exists (βTCtxU Z' A'). eapply AnnTCtxU; eauto.
}
Qed.

(* ==================== Annotation Getters ==================== *)

Lemma ann_get_op_type Σ Σ' A A' B B' op wfs wfa wfb:
  sig_ann Σ wfs Σ' -> get_op_type Σ op = Some (A, B) ->
  vtype_ann A wfa A' -> vtype_ann B wfb B' ->
  get_op_βtype Σ' op = Some (A', B').
Proof.
intros. destruct H.
+ simpl in H0. discriminate.
+ simpl in *. destruct (op==op0) eqn: eq.
  - inv H0. f_equal. f_equal. eapply vtype_ann_unique; eauto.

(* ==================== Annotation Subtypes ==================== *)

Fixpoint ann_vsubtype A wfa A' B wfb B' :
  vtype_ann A wfa A' -> vtype_ann B wfb B' ->
  vsubtype A B -> βvsubtype A' B'
with ann_csubtype C wfc C' D wfd D':
  ctype_ann C wfc C' -> ctype_ann D wfd D' ->
  csubtype C D -> βcsubtype C' D'
with ann_sigsubtype Σ wfs Σ' Ω wfo Ω':
  sig_ann Σ wfs Σ' -> sig_ann Ω wfo Ω' ->
  sig_subtype Σ Ω -> βsig_subtype Σ' Ω'
with ann_eqssubtype E Σ wfe E' F Ω wff F':
  eqs_ann E Σ wfe E' -> eqs_ann F Ω wff F' ->
  eqs_subtype E F -> βeqs_subtype E' F'.
Proof.
all: intros e1 e2 orig.
{
destruct e1; destruct e2; try inv orig.
+ apply βSubtypeUnit.
+ apply βSubtypeInt.
+ apply βSubtypeTyØ.
+ apply βSubtypeTyΠ; eauto.
+ apply βSubtypeTyΣ; eauto.
+ apply βSubtypeTyFun; eauto.
+ apply βSubtypeTyHandler; eauto.
}{
destruct e1; destruct e2; try inv orig.
apply βSubtypeCTy; eauto.
}{
destruct e1.
+ apply βSubtypeSigØ.
+ eapply βSubtypeSigU.
  - inv orig. eauto.
  - inv orig. 
}
Admitted.


Lemma ann_vsubtype_refl A A' :
  wf_vtype A -> vtype_ann A A' -> βvsubtype A' A'.
Proof.
intros wf sty. eapply ann_vsubtype; eauto. apply vsubtype_refl. assumption.
Qed.


(* ==================== Main ==================== *)

(* This should be fixed to work on annotation not typing!!! *)

Fixpoint has_vtype_vsynths Γ Γ' v v' A A' (orig: has_vtype Γ v A) {struct orig}:
  v_ann Γ v A orig v' -> ctx_ann Γ Γ' ->  vtype_ann A A' ->
  vsynth Γ' v' A'

with has_vtype_vchecks Γ Γ' v v' A A' (orig: has_vtype Γ v A) {struct orig}:
  v_ann Γ v A orig v' -> ctx_ann Γ Γ' ->  vtype_ann A A' ->
  vcheck Γ' v' A'

with has_ctype_csynths Γ Γ' c c' C C' (orig: has_ctype Γ c C) {struct orig}: 
c_ann Γ c C orig c' -> ctx_ann Γ Γ' -> ctype_ann C C' ->
  csynth Γ' c' C'

with has_ctype_cchecks Γ Γ' c c' C C' (orig: has_ctype Γ c C) {struct orig}: 
  c_ann Γ c C orig c' -> ctx_ann Γ Γ' -> ctype_ann C C' ->
  ccheck Γ' c' C'

with has_htype_hchecks Γ Γ' h h' Σ Σ' D D' (orig: has_htype Γ h Σ D) {struct orig}: 
  h_ann Γ h Σ D orig h' -> ctx_ann Γ Γ' -> sig_ann Σ Σ' -> ctype_ann D D' ->
  hcheck Γ' h' Σ' D'

.
Proof.
{
intros vtyann. destruct vtyann; intros cann vann.
all: assert (wf_βctx Γ') by admit.
all: assert (forall A A', wf_vtype A -> vtype_ann A A' -> wf_βvtype A') as vann_wf by admit.
all: assert (forall C C', wf_ctype C -> ctype_ann C C' -> wf_βctype C') as cann_wf by admit.
all: assert (forall Σ Σ', wf_sig Σ -> sig_ann Σ Σ' -> wf_βsig Σ') as sigann_wf by admit.
all: assert (forall Σ Σ' E E', wf_sig Σ -> wf_eqs E Σ -> sig_ann Σ Σ' -> eqs_ann E E' -> wf_βeqs E' Σ') as eqsann_wf by admit.
+ apply SynthV; eauto. inv p. eauto. apply SynthVar. admit.
+ inv vann. apply SynthV; eauto. apply βWfUnit. apply SynthUnit.
+ inv vann. apply SynthV; eauto. apply βWfInt. apply SynthInt.
+ inv vann. apply SynthV; eauto. apply βWfTyΠ; inv p; inv H1; eauto.
  apply SynthPair; eauto.
+ inv vann. inv p. inv H3. apply SynthV; eauto. apply βWfTyΣ; eauto.
  specialize (vtype_ann_unique _ _ _ H H4) as AA.
  specialize (vtype_ann_unique _ _ _ H0 H6) as BB.
  subst. apply SynthAnnV. apply CheckV; eauto. apply βWfTyΣ; eauto.
  apply CheckInl. eauto.
+ inv vann. inv p. inv H3. apply SynthV; eauto. apply βWfTyΣ; eauto.
  specialize (vtype_ann_unique _ _ _ H H4) as AA.
  specialize (vtype_ann_unique _ _ _ H0 H6) as BB.
  subst. apply SynthAnnV. apply CheckV; eauto. apply βWfTyΣ; eauto.
  apply CheckInr. eauto.
+ inv vann. inv p. inv H4. apply SynthV; eauto. apply βWfTyFun; eauto.
  specialize (vtype_ann_unique _ _ _ H0 H5) as AA.
  specialize (ctype_ann_unique _ _ _ H1 H7) as CC.
  subst. apply SynthAnnV. apply CheckV; eauto. apply βWfTyFun; eauto.
  apply CheckFun. eapply has_ctype_cchecks; eauto. apply AnnCtxU; auto.
+ inv vann. inv p. inv H4. apply SynthV; eauto. apply βWfTyHandler; eauto.
  inv H7. eauto. inv H7. eauto. destruct C'. destruct D'0. inv H8. inv H10.
  specialize (vtype_ann_unique _ _ _ H11 H16) as a.
  specialize (sig_ann_unique _ _ _ H12 H22) as aa.
  specialize (eqs_ann_unique _ _ _ H13 H23) as aaa.
  subst. clear H16 H22 H23.
  specialize (vtype_ann_unique _ _ _ H1 H17) as a.
  specialize (sig_ann_unique _ _ _ H2 H20) as aa.
  specialize (eqs_ann_unique _ _ _ H3 H21) as aaa.
  subst. clear H17 H20 H21.
  apply SynthAnnV. apply CheckV; eauto. inv H7. inv H10. inv H14.
   apply βWfTyHandler; apply βWfCTy; eauto.
  apply CheckHandler. eapply has_ctype_cchecks; eauto. 
  - apply AnnCtxU; auto.
  - apply AnnCTy; auto.
  - eapply has_htype_hchecks; eauto. apply AnnCTy; auto.
+ apply SynthV; eauto. specialize (vtype_ann_unique _ _ _ vann H0) as AA2.
  subst. apply SynthAnnV. apply CheckV; eauto. 
  apply vtype_ann_exists in H. destruct H as [A1']. eapply CheckVBySynth.
  2: eapply ann_vsubtype. 2: exact H. all: eauto.
}{
intros vtyann. destruct vtyann; intros cann vann.
all: assert (wf_βctx Γ') by admit.
all: assert (forall A A', wf_vtype A -> vtype_ann A A' -> wf_βvtype A') as vann_wf by admit.
all: assert (forall C C', wf_ctype C -> ctype_ann C C' -> wf_βctype C') as cann_wf by admit.
+ apply CheckV; eauto. inv p. eauto. eapply CheckVBySynth.
  2: eapply ann_vsubtype_refl; inv p; eauto. 
  apply SynthV. auto. inv p. eauto. apply SynthVar. admit.
+ inv vann. apply CheckV; eauto. apply βWfUnit. eapply CheckVBySynth.
  2: eapply ann_vsubtype_refl. 3: apply AnnTyUnit. apply SynthV; eauto.
  apply βWfUnit. apply SynthUnit. apply WfUnit.
+ inv vann. apply CheckV; eauto. apply βWfInt. eapply CheckVBySynth.
  2: eapply ann_vsubtype_refl. 3: apply AnnTyInt. apply SynthV; eauto.
  apply βWfInt. apply SynthInt. apply WfInt.
+ inv vann. apply CheckV; eauto. apply βWfTyΠ; inv p; inv H1; eauto.
  eapply CheckVBySynth. 2: eapply ann_vsubtype_refl. 3: apply AnnTyΠ; eauto.
  apply SynthV; eauto. apply βWfTyΠ; inv p; inv H1; eauto.
  apply SynthPair; eauto. inv p. assumption.
+ inv vann. 
  specialize (vtype_ann_unique _ _ _ H H4) as AA.
  specialize (vtype_ann_unique _ _ _ H0 H6) as BB.
  admit.
+ admit.
+ admit.
+ admit.
+ admit.
}{



}


