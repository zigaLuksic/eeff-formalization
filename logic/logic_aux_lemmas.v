Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export subtyping_lemmas.


Lemma heq_cases_ceq Σ D Γ Ψ h1 h2 op A B c1 c2 :
  form Γ Ψ (Heq Σ D h1 h2) -> get_op_type Σ op = Some (A, B) ->
  get_case h1 op = Some c1 ->
  get_case h2 op = Some c2 ->
  form (CtxU (CtxU Γ (TyFun B D)) A) (hyp_shift Ψ 2 0) (Ceq D c1 c2).
Proof.
intros eqs gets finds1 finds2.
induction Σ. simpl in gets. discriminate.
simpl in *. destruct (op==o).
+ inv gets. inv eqs. inv H1.
  rewrite H8 in finds1. rewrite H12 in finds2.
  inv finds1. inv finds2. auto.
+ inv eqs. inv H1. eauto.
Qed.

(* ==================== Logic Subtyping ==================== *)

Lemma heq_subtype Σ Σ' D Γ Ψ h1 h2 (orig : form Γ Ψ (Heq Σ D h1 h2)) :
  wf_sig Σ' -> sig_subtype Σ' Σ -> form Γ Ψ (Heq Σ' D h1 h2).
Proof.
intros wf sty. induction Σ' as [ | Σ' IH o A' B'].
+ inv orig. inv H. eapply WfForm; auto.
  eapply WfHeq. 4: exact H10. 4: exact H11. auto.
  apply SubtypeSigØ. apply SubtypeSigØ. apply HeqSigØ.
+ inv orig. inv H. eapply WfForm; auto.
  eapply WfHeq. auto. 3: exact H10. 3: exact H11.
  { eapply sig_subtype_trans; eauto. }
  { eapply sig_subtype_trans; eauto. }
  inv sty. inv wf.
  eapply sig_subtype_get_Some in H8 as g1; eauto.
  eapply sig_subtype_get_Some in H9 as g2; eauto.
  destruct g1 as [A1[B1[get1[_ _]]]].
  destruct g2 as [A2[B2[get2[_ _]]]].
  eapply h_has_case in H10 as case1; eauto.
  eapply h_has_case in H11 as case2; eauto.
  destruct case1 as [c1 find1].
  destruct case2 as [c2 find2].
  clear A1 B1 get1 A2 B2 get2.
  eapply HeqSigU; eauto.
  assert 
    (form (CtxU (CtxU Γ (TyFun B'0 D)) A'0) (hyp_shift Ψ 2 0) (Ceq D c1 c2)).
  - eapply heq_cases_ceq. 2: eauto. all: eauto.
    eapply WfForm; eauto. eapply WfHeq. 2: exact H8. all: eauto.
  - eapply ctx_subtype_form; eauto.
    * inv H10. apply WfCtxU. apply WfCtxU. 2: apply WfTyFun. all: auto.
    * apply SubtypeCtxU. apply SubtypeCtxU. 2: apply SubtypeTyFun. all: auto.
      all: inv H10; (apply ctx_subtype_refl || apply csubtype_refl); auto.
Qed.

(* This formulation is needed so that the termination
   checker doesnt run forever. *)
Fixpoint veq_subtype Γ Ψ judg (orig: form Γ Ψ judg) A A' v1 v2 {struct orig} :
  judg = Veq A v1 v2 ->
  wf_vtype A' -> vsubtype A A' -> 
  form Γ Ψ (Veq A' v1 v2)
with ceq_subtype Γ Ψ judg (orig: form Γ Ψ judg) C C' c1 c2 {struct orig} :
  judg = Ceq C c1 c2 ->
  wf_ctype C' -> csubtype C C' -> 
  form Γ Ψ (Ceq C' c1 c2).
Proof.
{ 
intros same wfa' stya.
assert (wf_ctx Γ) as wfctx.
{ clear veq_subtype ceq_subtype. inv orig. inv H. inv H5. auto. } 
assert (has_vtype Γ v1 A') as ty1.
{ clear veq_subtype ceq_subtype. inv orig. inv H.
  apply TypeV; auto. eapply TypeVSubtype; eauto. }
assert (has_vtype Γ v2 A') as ty2.
{ clear veq_subtype ceq_subtype. inv orig. inv H.
  apply TypeV; auto. eapply TypeVSubtype; eauto. }
apply WfForm; auto. apply WfVeq; auto.
{ clear veq_subtype ceq_subtype. inv orig. auto. }
destruct orig. destruct H1; inv same.
+ specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  apply VeqSym. eauto.
+ specialize (veq_subtype _ _ _ H1) as IH1.
  specialize (veq_subtype _ _ _ H2) as IH2.
  clear veq_subtype ceq_subtype.
  eapply VeqTrans; eauto.
+ clear veq_subtype ceq_subtype.
  eapply VeqVar; eauto. eapply vsubtype_trans; eauto.
+ clear veq_subtype ceq_subtype. 
  inv stya. apply VeqUnit; eauto.
+ clear veq_subtype ceq_subtype. 
  inv stya. apply VeqInt; eauto.
+ inv stya.
  specialize (veq_subtype _ _ _ H1) as IH1.
  specialize (veq_subtype _ _ _ H2) as IH2.
  clear veq_subtype ceq_subtype.
  inv wfa'. eapply VeqPair; eauto.
+ inv stya. 
  specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  inv wfa'. eapply VeqInl; eauto.
+ inv stya.
  specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  inv wfa'. eapply VeqInr; eauto.
+ clear veq_subtype ceq_subtype. 
  inv stya. eapply VeqListNil.
+ inv stya. 
  specialize (veq_subtype _ _ _ H1) as IH1.
  specialize (veq_subtype _ _ _ H2) as IH2.
  clear veq_subtype ceq_subtype.
  inv wfa'. eapply VeqListCons; eauto.
  eapply IH2. eauto.
  apply WfTyList. auto. 
  apply SubtypeTyList. auto.
+ inv stya.
  specialize (ceq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  inv wfa'. apply VeqFun.
  eapply ctx_subtype_form. eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. auto.
+ inv stya.
  specialize (ceq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  inv wfa'. inv H6. inv H7. eapply VeqHandler.
  eapply ctx_subtype_form. eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. auto.
  - eapply heq_subtype; eauto.
  - eapply csubtype_trans; eauto.
+ clear veq_subtype ceq_subtype. inv stya. apply ηUnit.
+ clear veq_subtype ceq_subtype. inv stya. apply ηFun.
}{
intros same wfc' styc.
assert (wf_ctx Γ) as wfctx.
{ clear veq_subtype ceq_subtype. inv orig. inv H. inv H5. auto. } 
assert (has_ctype Γ c1 C') as ty1.
{ clear veq_subtype ceq_subtype. inv orig. inv H.
  apply TypeC; auto. eapply TypeCSubtype; eauto. }
assert (has_ctype Γ c2 C') as ty2.
{ clear veq_subtype ceq_subtype. inv orig. inv H.
  apply TypeC; auto. eapply TypeCSubtype; eauto. }
apply WfForm; auto. apply WfCeq; auto.
{ clear veq_subtype ceq_subtype. inv orig. auto. }
destruct orig. destruct H1; inv same.
+ specialize (ceq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  apply CeqSym. eauto.
+ specialize (ceq_subtype _ _ _ H1) as IH1.
  specialize (ceq_subtype _ _ _ H2) as IH2.
  clear veq_subtype ceq_subtype.
  eapply CeqTrans; eauto.
+ inv styc.
  specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  inv wfc'. eapply CeqRet; eauto.
+ clear veq_subtype ceq_subtype.
  eapply CeqAbsurd; eauto.
+ specialize (ceq_subtype _ _ _ H2) as IH.
  clear veq_subtype ceq_subtype.
  eapply CeqΠMatch; eauto.
+ specialize (ceq_subtype _ _ _ H2) as IH1.
  specialize (ceq_subtype _ _ _ H3) as IH2.
  clear veq_subtype ceq_subtype.
  eapply CeqΣMatch; eauto.
+ specialize (ceq_subtype _ _ _ H2) as IH1.
  specialize (ceq_subtype _ _ _ H3) as IH2.
  clear veq_subtype ceq_subtype.
  eapply CeqListMatch; eauto.
+ inv styc. rename A' into B'.
  specialize (ceq_subtype _ _ _ H1) as IH1.
  specialize (ceq_subtype _ _ _ H2) as IH2.
  clear veq_subtype ceq_subtype.
  assert (wf_vtype A).
  { inv H1. inv H3. inv H11. inv H3. auto. }
  eapply CeqDoBind.
  - eapply IH1. eauto. apply WfCTy; eauto; inv wfc'; auto.
    apply SubtypeCTy; auto. apply vsubtype_refl. auto.
  - eapply IH2; eauto. apply SubtypeCTy; auto.
+ specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  assert (wf_vtype A).
  { inv H2. inv H3. inv H8. auto. }
  eapply CeqApp; eauto. eapply IH. eauto.
  - apply WfTyFun; assumption.
  - apply SubtypeTyFun. apply vsubtype_refl. all: auto.
+ rename C' into D'.
  specialize (veq_subtype _ _ _ H1) as IH.
  clear veq_subtype ceq_subtype.
  assert (wf_ctype C0).
  { inv H1. inv H3. inv H8. inv H3. auto. }
  eapply CeqHandle; eauto. eapply IH. eauto.
  - apply WfTyHandler; assumption.
  - apply SubtypeTyHandler. apply csubtype_refl. all: auto.
+ rename C' into D'.
  specialize (ceq_subtype _ _ _ H2) as IH.
  clear veq_subtype ceq_subtype.
  eapply CeqLetRec; eauto.
+ specialize (veq_subtype _ _ _ H2) as IH1.
  specialize (ceq_subtype _ _ _ H3) as IH2.
  clear veq_subtype ceq_subtype.
  inv styc.
  eapply sig_subtype_get_Some in H9 as getop; eauto.
  destruct getop as [A_op'[B_op'[gets[asty bsty]]]].
  eapply CeqOp; eauto; inv wfc'.
  - eapply IH1. eauto.
    eapply get_op_type_wf in gets. destruct gets. all: auto.
  - eapply ctx_subtype_form; eauto.
    * eapply IH2. eauto. apply WfCTy; eauto. apply SubtypeCTy; auto.
    * apply WfCtxU. auto. 
      eapply get_op_type_wf in gets. destruct gets. all: auto.
    * eapply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
+ clear veq_subtype ceq_subtype.
  inv styc. eapply OOTB; eauto. eapply eqs_subtype_contains; eauto.
  eapply wf_inst_tctx_subtype; eauto.
  apply SubtypeCTy; auto.
+ clear veq_subtype ceq_subtype.
  eapply βΠMatch.
+ clear veq_subtype ceq_subtype.
  eapply βΣMatch_Inl.
+ clear veq_subtype ceq_subtype.
  eapply βΣMatch_Inr.
+ clear veq_subtype ceq_subtype.
  eapply βListMatch_Nil.
+ clear veq_subtype ceq_subtype.
  eapply βListMatch_Cons.
+ clear veq_subtype ceq_subtype.
  eapply βApp.
+ clear veq_subtype ceq_subtype.
  eapply βLetRec.
+ clear veq_subtype ceq_subtype.
  eapply βDoBind_Ret.
+ clear veq_subtype ceq_subtype.
  eapply βDoBind_Op.
+ clear veq_subtype ceq_subtype.
  eapply βHandle_Ret.
+ clear veq_subtype ceq_subtype.
  eapply βHandle_Op. eauto.
+ clear veq_subtype ceq_subtype.
  eapply ηPair. omega.
  apply TypeC. inv H2. eauto. auto. eapply TypeCSubtype; eauto.
+ clear veq_subtype ceq_subtype.
  eapply ηSum. omega.
  apply TypeC. inv H2. eauto. auto. eapply TypeCSubtype; eauto.
+ clear veq_subtype ceq_subtype.
  eapply ηList. omega.
  apply TypeC. inv H2. eauto. auto. eapply TypeCSubtype; eauto.
+ clear veq_subtype ceq_subtype.
  eapply ηDoBind.
}
Qed.

(* ==================== Structural Rules for Cases ==================== *)

Lemma heq_case_extend_trivial Σ D Γ Ψ h1 h2 op A1 A2 B1 B2 c1 c2:
  form Γ Ψ (Heq Σ D h1 h2) ->
  get_case h1 op = None -> get_case h2 op = None ->
  has_ctype (CtxU (CtxU Γ (TyFun B1 D)) A1) c1 D ->
  has_ctype (CtxU (CtxU Γ (TyFun B2 D)) A2) c2 D ->
  form Γ Ψ (Heq Σ D (CasesU h1 op c1) (CasesU h2 op c2)).
Proof.
intros orig f1 f2 tys1 tys2.
assert (wf_vtype A1) as wfa1 by (inv tys1; inv H; auto).
assert (wf_vtype A2) as wfa2 by (inv tys2; inv H; auto).
assert (wf_vtype B1) as wfb1 by (inv tys1; inv H; inv H4; inv H6; auto).
assert (wf_vtype B2) as wfb2 by (inv tys2; inv H; inv H4; inv H6; auto).
assert (wf_ctype D) as wfd by (inv tys1; auto).
assert (wf_ctx Γ) as wfctx by (inv orig; inv H; inv H10; auto).
inv orig. inv H.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H10; eauto. destruct H10 as [c f].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H11; eauto. destruct H11 as [c f].
  rewrite f in f2. discriminate. }
assert (sig_subtype Σ (SigU Σ1 op A1 B1)) as ss1.
{ apply sig_subtype_extend. auto. apply WfSigU; auto. inv H10. assumption. }
assert (sig_subtype Σ (SigU Σ2 op A2 B2)) as ss2.
{ apply sig_subtype_extend. auto. apply WfSigU; auto. inv H11. assumption. }
induction Σ as [ | Σ IH o A B].
+ eapply WfForm; auto. eapply WfHeq. auto. exact ss1. exact ss2.
  - apply TypeH. 2:apply WfSigU. 2:inv H10. 7:apply TypeCasesU. all: auto.
  - apply TypeH. 2:apply WfSigU. 2:inv H11. 7:apply TypeCasesU. all: auto.
  - apply HeqSigØ.
+ eapply WfForm; auto. eapply WfHeq. auto. exact ss1. exact ss2.
  - apply TypeH. 2:apply WfSigU. 2:inv H10. 7:apply TypeCasesU. all: auto.
  - apply TypeH. 2:apply WfSigU. 2:inv H11. 7:apply TypeCasesU. all: auto.
  - inv H1. eapply HeqSigU.
    * simpl. destruct (o==op). rewrite e, f1 in H12. discriminate. eauto.
    * simpl. destruct (o==op). rewrite e, f2 in H16. discriminate. eauto.
    * assumption.
    * inv H18. inv H6. inv H8. inv H9.
      apply IH; auto. 
      all: apply sig_subtype_extend; auto.
      all: apply WfSigU; auto. inv H10. auto. inv H11. auto.
Qed.


Lemma heq_case_extend_structural Σ D Γ Ψ h1 h2 op A B c1 c2:
  form Γ Ψ (Heq Σ D h1 h2) ->
  get_case h1 op = None -> get_case h2 op = None ->
  form (CtxU (CtxU Γ (TyFun B D)) A) (hyp_shift Ψ 2 0) (Ceq D c1 c2) ->
  form Γ Ψ (Heq (SigU Σ op A B) D (CasesU h1 op c1) (CasesU h2 op c2)).
Proof.
intros orig f1 f2 ceq12.
assert (has_ctype (CtxU (CtxU Γ (TyFun B D)) A) c1 D) as tys1.
{ inv ceq12. inv H. auto. }
assert (has_ctype (CtxU (CtxU Γ (TyFun B D)) A) c2 D) as tys2.
{ inv ceq12. inv H. auto. }
assert (wf_vtype A) as wfa by (inv tys1; inv H; auto).
assert (wf_vtype B) as wfb by (inv tys1; inv H; inv H4; inv H6; auto).
assert (wf_ctype D) as wfd by (inv tys1; auto).
assert (wf_ctx Γ) as wfctx by (inv orig; inv H; inv H10; auto).
inv orig. inv H.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H10; eauto. destruct H10 as [c f].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H11; eauto. destruct H11 as [c f].
  rewrite f in f2. discriminate. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ1 op A B)) as ss1.
{ eapply SubtypeSigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
  inv H10. auto. simpl. destruct (op==op). reflexivity. destruct n. auto.
  all: apply vsubtype_refl; auto. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ2 op A B)) as ss2.
{ eapply SubtypeSigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
  inv H11. auto. simpl. destruct (op==op). reflexivity. destruct n. auto.
  all: apply vsubtype_refl; auto. }
assert (get_op_type Σ op = None) as sgetnone.
{ destruct (get_op_type Σ op) eqn: gs; auto. destruct p.
  eapply sig_subtype_get_Some in H8; eauto. destruct H8 as [a[b[g]]]. 
  rewrite g in getn1. discriminate. }
eapply WfForm; auto. eapply WfHeq. apply WfSigU; auto. exact ss1. exact ss2.
- apply TypeH. 2:apply WfSigU. 2:inv H10. 7:apply TypeCasesU. all: auto.
- apply TypeH. 2:apply WfSigU. 2:inv H11. 7:apply TypeCasesU. all: auto.
- eapply HeqSigU.
  * simpl. destruct (op==op). reflexivity. destruct n. auto.
  * simpl. destruct (op==op). reflexivity. destruct n. auto.
  * assumption.
  * eapply heq_case_extend_trivial; eauto. 
    eapply WfForm. eapply WfHeq. 2:exact H8. all: eauto.
Qed.

(* ================== Reflexivity, Symmetry, Transitivity ================== *)

Lemma veq_refl Γ v A : 
  has_vtype Γ v A -> form Γ HypØ (Veq A v v)
with ceq_refl Γ c C : 
  has_ctype Γ c C -> form Γ HypØ (Ceq C c c)
with heq_refl Γ h Σ D : 
  has_htype Γ h Σ D -> form Γ HypØ (Heq Σ D h h).
Proof.
all: intros orig.
{
apply WfForm. apply WfVeq; auto. apply WfHypØ. inv orig. auto.
destruct orig. destruct H1.
+ apply VeqUnit.
+ apply VeqInt. 
+ eapply VeqVar. eauto. apply vsubtype_refl. assumption.
+ apply VeqPair; eauto.
+ apply VeqInl; eauto.
+ apply VeqInr; eauto.
+ apply VeqListNil; eauto.
+ apply VeqListCons; eauto.
+ apply VeqFun; eauto. 
+ eapply VeqHandler; eauto. apply csubtype_refl. inv H2. assumption.
+ apply veq_refl in H1. eapply veq_subtype in H1; eauto. inv H1. assumption.
}{
apply WfForm. apply WfCeq; auto. apply WfHypØ. inv orig. auto.
destruct orig. destruct H1.
+ apply CeqRet. auto.
+ apply CeqAbsurd. auto.
+ eapply CeqΠMatch; eauto.
+ eapply CeqΣMatch; eauto.
+ eapply CeqListMatch; eauto.
+ eapply CeqDoBind; eauto. 
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec; eauto.
+ eapply CeqOp; eauto.
+ apply ceq_refl in H1. eapply ceq_subtype in H1; eauto. inv H1. assumption.
}{
apply WfForm. eapply WfHeq; auto.
inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
assumption. assumption. apply WfHypØ. inv orig. assumption.
destruct orig. destruct H2.
+ eapply HeqSigØ.
+ assert (get_case (CasesU h op cop) op = Some cop).
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply HeqSigU; eauto.
  eapply heq_case_extend_trivial; eauto; inv H0; assumption.
}
Qed.


Lemma veq_sym A Γ Ψ v1 v2 : 
  form Γ Ψ (Veq A v1 v2) -> form Γ Ψ (Veq A v2 v1)
with ceq_sym C Γ Ψ c1 c2 : 
  form Γ Ψ (Ceq C c1 c2) -> form Γ Ψ (Ceq C c2 c1).
Proof.
{
intro orig. apply WfForm. apply WfVeq. all: try (inv orig; inv H; assumption).
apply VeqSym. auto.
}{
intro orig. apply WfForm. apply WfCeq. all: try (inv orig; inv H; assumption).
apply CeqSym. auto.
}
Qed.

Lemma heq_sym Σ D Γ Ψ h1 h2 : 
  form Γ Ψ (Heq Σ D h1 h2) -> form Γ Ψ (Heq Σ D h2 h1).
Proof.
induction Σ; intros orig.
all: apply WfForm; try (inv orig; assumption).
+ inv orig. inv H. eapply WfHeq. auto.
  exact H9. exact H8. all: eauto.
+ apply HeqSigØ.
+ inv orig. inv H. eapply WfHeq. auto.
  exact H9. exact H8. all: eauto. 
+ inv orig. inv H1. eapply HeqSigU; eauto.
  apply ceq_sym. auto.
Qed.

    
Lemma veq_trans A Γ Ψ v1 v2 v3:
  form Γ Ψ (Veq A v1 v2) -> form Γ Ψ (Veq A v2 v3) -> form Γ Ψ (Veq A v1 v3)

with  ceq_trans C Γ Ψ c1 c2 c3:
  form Γ Ψ (Ceq C c1 c2) -> form Γ Ψ (Ceq C c2 c3) -> form Γ Ψ (Ceq C c1 c3).

Proof.
{
intros veq1 veq2. apply WfForm. apply WfVeq. 
+ inv veq1. inv H. auto.
+ inv veq2. inv H. auto.
+ inv veq1. auto.
+ eapply VeqTrans; eauto.
}{
intros ceq1 ceq2. apply WfForm. apply WfCeq. 
+ inv ceq1. inv H. auto.
+ inv ceq2. inv H. auto.
+ inv ceq1. auto.
+ eapply CeqTrans; eauto.
}
Qed.


Lemma heq_trans Σ D Γ Ψ h1 h2 h3:
  form Γ Ψ (Heq Σ D h1 h2) -> form Γ Ψ (Heq Σ D h2 h3) -> 
  form Γ Ψ (Heq Σ D h1 h3).
{
intros heq1 heq2. induction Σ.
+ inv heq1. inv heq2. inv H. inv H2. eapply WfForm. eapply WfHeq.
  2: exact H11. 2: exact H16. all: eauto. apply HeqSigØ.
+ inv heq1. inv heq2. inv H. inv H2. eapply WfForm. eapply WfHeq.
  2: exact H11. 2: exact H16. all: eauto. 
  inv H1. inv H4. eapply HeqSigU; eauto.
  rewrite H10 in H23. inv H23.
  eapply ceq_trans; eauto.
}
Qed.