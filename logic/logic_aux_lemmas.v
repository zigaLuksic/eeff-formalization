Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".

Require Export subtyping_lemmas.


Lemma heq_cases_ceq Σ D Γ h1 h2 op A B c1 c2 :
  heq Σ D Γ h1 h2 -> get_op_type Σ op = Some (A, B) ->
  get_case h1 op = Some c1 ->
  get_case h2 op = Some c2 ->
  ceq D (CtxU (CtxU Γ A) (TyFun B D)) c1 c2.
Proof.
intros eqs gets finds1 finds2.
induction Σ. simpl in gets. discriminate.
simpl in *. destruct (op==o).
+ inv gets. inv eqs. inv H4.
  rewrite H9 in finds1. rewrite H14 in finds2.
  inv finds1. inv finds2. auto.
+ inv eqs. inv H4. eauto.
Qed.

(* ==================== Logic Subtyping ==================== *)

Lemma heq_subtype Σ Σ' D Γ h1 h2 (orig : heq Σ D Γ h1 h2) :
  wf_sig Σ' -> sig_subtype Σ' Σ -> heq Σ' D Γ h1 h2.
Proof.
intros wf sty. induction Σ' as [ | Σ' IH o A' B'].
+ inv orig. eapply Heq. auto. 3: exact H2. 3: exact H3.
  apply STySigØ. apply STySigØ. apply HeqSigØ.
+ inv orig. eapply Heq. auto. 3: exact H2. 3: exact H3.
  { eapply sig_subtype_trans; eauto. }
  { eapply sig_subtype_trans; eauto. }
  inv sty. inv wf.
  eapply sig_subtype_get_Some in H0 as g1; eauto.
  eapply sig_subtype_get_Some in H1 as g2; eauto.
  destruct g1 as [A1[B1[get1[_ _]]]].
  destruct g2 as [A2[B2[get2[_ _]]]].
  eapply h_has_case in H2 as case1; eauto.
  eapply h_has_case in H3 as case2; eauto.
  destruct case1 as [c1 find1].
  destruct case2 as [c2 find2].
  clear A1 B1 get1 A2 B2 get2.
  eapply HeqSigU; eauto.
  assert (ceq D (CtxU (CtxU Γ A'0) (TyFun B'0 D)) c1 c2).
  - eapply heq_cases_ceq. 2: eauto.
    eapply Heq. 2: exact H0. all: eauto.
  - eapply ctx_subtype_ceq; eauto.
    * inv H2. apply WfCtxU. apply WfCtxU. 3: apply WfTyFun. all: auto.
    * apply STyCtxU. apply STyCtxU. 3: apply STyFun. all: auto.
      all: inv H2; (apply ctx_subtype_refl || apply csubtype_refl); auto.
Qed.


Fixpoint veq_subtype A A' Γ v1 v2 (orig : veq A Γ v1 v2) {struct orig} :
  wf_vtype A' -> vsubtype A A' -> veq A' Γ v1 v2
with ceq_subtype C C' Γ c1 c2 (orig : ceq C Γ c1 c2) {struct orig} :
  wf_ctype C' -> csubtype C C' -> ceq C' Γ c1 c2.
Proof.
{ 
intros. inv orig.
assert (has_vtype Γ v1 A') as ty1.
{ apply TypeV; auto. inv H1. auto. eapply TypeVSubsume; eauto. }
assert (has_vtype Γ v2 A') as ty2.
{ apply TypeV; auto. inv H1. auto. eapply TypeVSubsume; eauto. }
destruct H3; apply Veq; auto.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply VeqVar; eauto. eapply vsubtype_trans; eauto.
+ inv H0. apply VeqUnit; eauto.
+ inv H0. apply VeqInt; eauto.
+ inv H0. inv H. eapply VeqPair; eapply veq_subtype; eauto.
+ inv H0. eapply VeqLeft. eapply veq_subtype; eauto. inv H. auto.
  all: eapply vsubtype_trans; eauto.
+ inv H0. eapply VeqRight. eapply veq_subtype; eauto. inv H. auto.
  all: eapply vsubtype_trans; eauto.
+ inv H0. eapply VeqNil.
  all: eapply vsubtype_trans; eauto.
+ inv H0. eapply VeqCons; eapply veq_subtype; eauto. inv H. auto.
  apply STyList. auto.
+ inv H0. apply VeqFun. inv H. eapply ceq_subtype in H3; eauto.
  eapply ctx_subtype_ceq. eauto.
  - apply WfCtxU; auto. inv H1. auto.
  - apply STyCtxU; auto. apply ctx_subtype_refl. inv H1. auto.
+ inv H0. clear ceq_subtype veq_subtype.
  inv H10. eapply VeqHandler; eauto.
  eapply ctx_subtype_ceq. eauto. all: inv H; inv H9.
  - apply WfCtxU; auto. inv H1. assumption.
  - apply STyCtxU; auto. apply ctx_subtype_refl. inv H1. auto.
  - eapply respects_eqs_subtype; eauto. eapply wf_eqs_sig_subtype; eauto.
    eapply sig_subtype_trans; eauto. inv H4. auto.
  - eapply sig_subtype_trans; eauto.
  - eapply csubtype_trans; eauto.
+ inv H0. apply ηUnit.
+ inv H0. apply ηFun.
}{
intros. inv orig.
assert (wf_ctx Γ) as wfctx by (inv H1; assumption).
assert (has_ctype Γ c1 C') as ty1.
{ apply TypeC; auto. eapply TypeCSubsume; eauto. }
assert (has_ctype Γ c2 C') as ty2.
{ apply TypeC; auto. eapply TypeCSubsume; eauto. }
apply Ceq; auto. destruct H3.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ inv H0. inv H. eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto. all: eapply csubtype_trans; eauto.
+ eapply CeqProdMatch; eauto.
+ eapply CeqSumMatch; eauto.
+ eapply CeqListMatch; eauto.
+ inv H0. rename A' into B'. 
  assert (wf_vtype A) by (inv H3; inv H0; inv H7; auto). 
  eapply CeqDo.
  - eapply ceq_subtype. eauto. 
    apply WfCTy; eauto; inv H; auto.
    apply STyCTy; auto. apply vsubtype_refl. auto.
  - eapply ceq_subtype; eauto. apply STyCTy; auto.
+ eapply CeqApp; eauto. eapply veq_subtype; eauto; inv H3; inv H5; inv H8.
  - apply WfTyFun; assumption.
  - apply STyFun. apply vsubtype_refl. all: auto.
+ eapply CeqHandle; eauto. eapply veq_subtype; eauto; inv H3; inv H5; inv H8.
  - apply WfTyHandler; assumption.
  - apply STyHandler. apply csubtype_refl. all: auto.
+ eapply CeqLetRec; eauto.
+ inv H0. eapply sig_subtype_get_Some in H3; eauto.
  destruct H3 as [A_op'[B_op'[gets[asty bsty]]]].
  eapply CeqOp; eauto.
  all: try (eapply vsubtype_trans; eauto).
  - eapply veq_subtype; eauto.
    eapply get_op_type_wf in gets. destruct gets. auto. inv H. auto.
  - eapply ctx_subtype_ceq; eauto.
    * eapply ceq_subtype; eauto. apply STyCTy; auto.
    * apply WfCtxU. auto. 
      eapply get_op_type_wf in gets. destruct gets. auto. inv H. auto.
    * eapply STyCtxU. apply ctx_subtype_refl. all: auto.
+ eapply OOTB; eauto. eapply csubtype_trans; eauto.
+ eapply βMatchPair.
+ eapply βMatchLeft.
+ eapply βMatchRight.
+ eapply βMatchNil.
+ eapply βMatchCons.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoRet.
+ eapply βDoOp.
+ eapply βHandleRet.
+ eapply βHandleOp. eauto.
+ eapply ηEmpty; aomega.
+ eapply ηPair. omega.
  apply TypeC. inv H4. eauto. auto. eapply TypeCSubsume; eauto.
+ eapply ηSum. omega.
  apply TypeC. inv H4. eauto. auto. eapply TypeCSubsume; eauto.
+ eapply ηList. omega.
  apply TypeC. inv H4. eauto. auto. eapply TypeCSubsume; eauto.
+ eapply ηDo.
}
Qed.

(* ==================== Structural Rules for Cases ==================== *)

Lemma heq_case_extend_trivial Σ D Γ h1 h2 op A1 A2 B1 B2 c1 c2:
  heq Σ D Γ h1 h2 ->
  get_case h1 op = None -> get_case h2 op = None ->
  has_ctype (CtxU (CtxU Γ A1) (TyFun B1 D)) c1 D ->
  has_ctype (CtxU (CtxU Γ A2) (TyFun B2 D)) c2 D ->
  heq Σ D Γ (CasesU h1 op A1 B1 c1) (CasesU h2 op A2 B2 c2).
Proof.
intros orig f1 f2 tys1 tys2.
assert (wf_vtype A1) as wfa1. { inv tys1. inv H. inv H4. auto. }
assert (wf_vtype A2) as wfa2. { inv tys2. inv H. inv H4. auto. }
assert (wf_vtype B1) as wfb1. { inv tys1. inv H. inv H5. auto. }
assert (wf_vtype B2) as wfb2. { inv tys2. inv H. inv H5. auto. }
assert (wf_ctype D) as wfd. { inv tys1. auto. }
assert (wf_ctx Γ) as wfctx. { inv orig. inv H2. auto. }
destruct orig.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H2; eauto. destruct H2 as [c f].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H3; eauto. destruct H3 as [c f].
  rewrite f in f2. discriminate. }
assert (sig_subtype Σ (SigU Σ1 op A1 B1)) as ss1.
{ apply sig_subtype_extend. auto. apply WfSigU; auto. inv H2. assumption. }
assert (sig_subtype Σ (SigU Σ2 op A2 B2)) as ss2.
{ apply sig_subtype_extend. auto. apply WfSigU; auto. inv H3. assumption. }
induction Σ as [ | Σ IH o A B].
+ eapply Heq. auto. exact ss1. exact ss2.
  - apply TypeH. 2:apply WfSigU. 2:inv H2. 7:apply TypeCasesU. all: auto.
  - apply TypeH. 2:apply WfSigU. 2:inv H3. 7:apply TypeCasesU. all: auto.
  - apply HeqSigØ.
+ eapply Heq. auto. exact ss1. exact ss2.
  - apply TypeH. 2:apply WfSigU. 2:inv H2. 7:apply TypeCasesU. all: auto.
  - apply TypeH. 2:apply WfSigU. 2:inv H3. 7:apply TypeCasesU. all: auto.
  - inv H4. eapply HeqSigU.
    * simpl. destruct (o==op). rewrite e, f1 in H9. discriminate. eauto.
    * simpl. destruct (o==op). rewrite e, f2 in H14. discriminate. eauto.
    * assumption.
    * inv H. inv H0. inv H1. inv H16.
      apply IH; auto; apply sig_subtype_extend; auto.
      all: inv H2; inv H3; apply WfSigU; auto.
Qed.


Lemma heq_case_extend_structural Σ D Γ h1 h2 op A B c1 c2:
  heq Σ D Γ h1 h2 ->
  get_case h1 op = None -> get_case h2 op = None ->
  ceq D (CtxU (CtxU Γ A) (TyFun B D)) c1 c2 ->
  heq (SigU Σ op A B) D Γ (CasesU h1 op A B c1) (CasesU h2 op A B c2).
Proof.
intros orig f1 f2 ceq12.
assert (has_ctype (CtxU (CtxU Γ A) (TyFun B D)) c1 D) as tys1 
by (inv ceq12; auto).
assert (has_ctype (CtxU (CtxU Γ A) (TyFun B D)) c2 D) as tys2 
by (inv ceq12; auto).
assert (wf_vtype A) as wfa. { inv tys1. inv H. inv H4. auto. }
assert (wf_vtype B) as wfb. { inv tys1. inv H. inv H5. auto. }
assert (wf_ctype D) as wfd. { inv tys1. auto. }
assert (wf_ctx Γ) as wfctx. { inv orig. inv H2. auto. }
destruct orig.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H2; eauto. destruct H2 as [c f].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H3; eauto. destruct H3 as [c f].
  rewrite f in f2. discriminate. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ1 op A B)) as ss1.
{ eapply STySigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
  inv H2. auto. simpl. destruct (op==op). reflexivity. destruct n. auto.
  all: apply vsubtype_refl; auto. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ2 op A B)) as ss2.
{ eapply STySigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
  inv H3. auto. simpl. destruct (op==op). reflexivity. destruct n. auto.
  all: apply vsubtype_refl; auto. }
assert (get_op_type Σ op = None) as sgetnone.
{ destruct (get_op_type Σ op) eqn: gs; auto. destruct p.
  eapply sig_subtype_get_Some in H0; eauto. destruct H0 as [a[b[g]]]. 
  rewrite g in getn1. discriminate. }
eapply Heq. apply WfSigU; auto. exact ss1. exact ss2.
- apply TypeH. 2:apply WfSigU. 2:inv H2. 7:apply TypeCasesU. all: auto.
- apply TypeH. 2:apply WfSigU. 2:inv H3. 7:apply TypeCasesU. all: auto.
- eapply HeqSigU.
  * simpl. destruct (op==op). reflexivity. destruct n. auto.
  * simpl. destruct (op==op). reflexivity. destruct n. auto.
  * assumption.
  * eapply heq_case_extend_trivial; eauto. eapply Heq. 2:exact H0. all: eauto.
Qed.


(* ================== Reflexivity, Symmetry, Transitivity ================== *)

Lemma veq_refl Γ v A   : has_vtype Γ v A -> veq A Γ v v
with  ceq_refl Γ c C   : has_ctype Γ c C -> ceq C Γ c c
with  heq_refl Γ h Σ D : has_htype Γ h Σ D -> heq Σ D Γ h h.
Proof.
all: intros orig.
{
apply Veq; auto. all: destruct orig; auto. destruct H1.
+ apply VeqUnit.
+ apply VeqInt. 
+ eapply VeqVar. eauto. apply vsubtype_refl. assumption.
+ apply VeqPair; eauto.
+ apply VeqLeft; eauto.
  all: inv H0; apply vsubtype_refl; auto.
+ apply VeqRight; eauto.
  all: inv H0; apply vsubtype_refl; auto.
+ apply VeqNil; eauto.
  all: inv H0; apply vsubtype_refl; auto.
+ apply VeqCons; eauto.
+ apply VeqFun; eauto.
  all: inv H0; apply vsubtype_refl; auto.
+ eapply VeqHandler; eauto.
  all: inv H0; inv H6; apply sig_subtype_refl || apply csubtype_refl; auto.
+ apply veq_refl in H1. eapply veq_subtype in H1; eauto. inv H1. assumption.
}{
apply Ceq; auto. all: destruct orig; auto. destruct H1.
+ apply CeqRet. auto.
+ apply CeqAbsurd. all: apply csubtype_refl; auto.
+ eapply CeqProdMatch; eauto.
+ eapply CeqSumMatch; eauto.
+ eapply CeqListMatch; eauto.
+ eapply CeqDo; eauto. 
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec; eauto.
+ apply get_op_type_wf in H1 as wf. destruct wf.
  eapply CeqOp; eauto. 
  - apply veq_refl in H4. eapply veq_subtype; eauto.
  - apply ceq_refl in H5. eapply ctx_subtype_ceq; eauto.
    all: apply WfCtxU || apply STyCtxU; auto. apply ctx_subtype_refl. auto.
  - inv H0. auto.
+ apply ceq_refl in H1. eapply ceq_subtype in H1; eauto. inv H1. assumption.
}{
eapply Heq. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
assumption. assumption.
destruct orig. destruct H2.
+ eapply HeqSigØ.
+ assert (get_case (CasesU h op A B c) op = Some c).
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply HeqSigU; eauto.
  eapply heq_case_extend_trivial; eauto; inv H0; auto.
  all: eapply wf_sig_unique_cases; eauto.
}
Qed.


Lemma veq_sym A Γ v1 v2   : veq A Γ v1 v2 -> veq A Γ v2 v1
with  ceq_sym C Γ c1 c2   : ceq C Γ c1 c2 -> ceq C Γ c2 c1
with  heq_sym Σ D Γ h1 h2 : heq Σ D Γ h1 h2 -> heq Σ D Γ h1 h2.
Proof.
{
intro orig. apply Veq. all: try (inv orig; assumption). apply VeqSym. auto.
}{
intro orig. apply Ceq. all: try (inv orig; assumption). apply CeqSym. auto.
}{
intro orig. destruct orig. induction H4.
+ eapply Heq. 2: exact H0. all: eauto. apply HeqSigØ.
+ eapply Heq. 2: exact H0. all: eauto.
  eapply HeqSigU; eauto.
}
Qed.


Lemma veq_trans A Γ v1 v2 v3:
  veq A Γ v1 v2 -> veq A Γ v2 v3 -> veq A Γ v1 v3

with  ceq_trans C Γ c1 c2 c3:
  ceq C Γ c1 c2 -> ceq C Γ c2 c3 -> ceq C Γ c1 c3

with  heq_trans Σ D Γ h1 h2 h3:
  heq Σ D Γ h1 h2 -> heq Σ D Γ h2 h3 -> heq Σ D Γ h1 h3.

Proof.
{
intros veq1 veq2. apply Veq. inv veq1. auto. inv veq2. auto.
eapply VeqTrans; eauto.
}{
intros ceq1 ceq2. apply Ceq. inv ceq1. auto. inv ceq2. auto.
eapply CeqTrans; eauto.
}{
intros heq1 heq2. induction Σ. 
+ inv heq1. inv heq2. eapply Heq. 2: exact H0. all: eauto. apply HeqSigØ.
+ inv heq1. inv heq2. eapply Heq. 2: exact H0. all: eauto.
  inv H4. inv H10. eapply HeqSigU; eauto.
  rewrite H14 in H20. inv H20. apply Ceq.
  - inv H21. assumption.
  - inv H24. assumption.
  - eapply CeqTrans; eauto.
}
Qed.
