Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export syntax_lemmas substitution_lemmas subtyping_lemmas.

Lemma heq_cases_ceq Σ D Γ h1 h2 op A B x1 x2 k1 k2 c1 c2 :
  heq Σ D Γ h1 h2 -> get_op_type Σ op = Some (A, B) ->
  find_case h1 op = Some (x1, k1, c1) ->
  find_case h2 op = Some (x2, k2, c2) ->
  ceq D (CtxU (CtxU Γ (TyFun B D)) A) c1 c2.
Proof.
intros eqs gets finds1 finds2.
induction Σ. simpl in gets. discriminate.
simpl in *. destruct (op==o).
+ inv gets. inv eqs. inv H4. 
  rewrite H9 in finds1. rewrite H14 in finds2. inv finds1. inv finds2. auto.
+ inv eqs. inv H4. eauto.
Qed.


Lemma heq_subtype Σ Σ' D Γ h1 h2 (orig : heq Σ D Γ h1 h2) :
  wf_sig Σ' -> sig_subtype Σ' Σ -> heq Σ' D Γ h1 h2.
Proof.
intros wf sty. induction Σ' as [ | Σ' IH o A' B'].
+ inv orig. eapply Heq. auto. 3: exact H2. 3: exact H3.
  apply SubtypeSigØ. apply SubtypeSigØ. apply HeqSigØ.
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
  destruct case1 as [x1[k1[c1 find1]]].
  destruct case2 as [x2[k2[c2 find2]]].
  clear A1 B1 get1 A2 B2 get2.
  eapply HeqSigU; eauto.
  assert (ceq D (CtxU (CtxU Γ (TyFun B'0 D)) A'0) c1 c2).
  - eapply heq_cases_ceq. 2: eauto.
    eapply Heq. 2: exact H0. all: eauto.
  - eapply ctx_subtype_ceq; eauto.
    inv H2. apply WfCtxU. apply WfCtxU. 2: apply WfTyFun. all: auto.
    apply SubtypeCtxU. apply SubtypeCtxU. 2: apply SubtypeTyFun. all: auto.
    all: inv H2. apply ctx_subtype_refl. auto. apply csubtype_refl. auto.
Qed.


Fixpoint veq_subtype A A' Γ v1 v2 (orig : veq A Γ v1 v2) {struct orig} :
  wf_vtype A' -> vsubtype A A' -> veq A' Γ v1 v2
with ceq_subtype C C' Γ c1 c2 (orig : ceq C Γ c1 c2) {struct orig} :
  wf_ctype C' -> csubtype C C' -> ceq C' Γ c1 c2.
Proof.
{ 
intros. inv orig.
assert (has_vtype Γ v1 A') as ty1.
{ apply TypeV; auto. inv H1. auto. eapply TypeVSubtype; eauto. }
assert (has_vtype Γ v2 A') as ty2.
{ apply TypeV; auto. inv H1. auto. eapply TypeVSubtype; eauto. }
destruct H3; apply Veq; auto.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply VeqVar; eauto. eapply vsubtype_trans; eauto.
+ inv H0. apply VeqUnit; eauto.
+ inv H0. apply VeqInt; eauto.
+ inv H0. inv H. eapply VeqPair; eapply veq_subtype; eauto.
+ inv H0. eapply VeqInl. eapply veq_subtype; eauto. inv H. auto.
+ inv H0. eapply VeqInr. eapply veq_subtype; eauto. inv H. auto.
+ inv H0. eapply VeqListNil.
+ inv H0. eapply VeqListCons; eapply veq_subtype; eauto. inv H. auto.
  apply SubtypeTyList. auto.
+ inv H0. apply VeqFun. inv H. eapply ceq_subtype in H3; eauto.
  eapply ctx_subtype_ceq. eauto.
  - apply WfCtxU; auto. inv H1. auto.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. inv H1. auto.
+ inv H0. inv H8. eapply VeqHandler. eapply ceq_subtype in H3; eauto.
  eapply ctx_subtype_ceq. eauto. all: inv H; inv H7.
  - apply WfCtxU; auto. inv H1. assumption.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. inv H1. auto.
  - assumption.
  - eapply heq_subtype; eauto.
  - eapply csubtype_trans; eauto.
+ inv H0. apply ηUnit.
+ inv H0. apply ηFun.
}{
intros. inv orig.
assert (wf_ctx Γ) as wfctx by (inv H1; assumption).
assert (has_ctype Γ c1 C') as ty1.
{ apply TypeC; auto. eapply TypeCSubtype; eauto. }
assert (has_ctype Γ c2 C') as ty2.
{ apply TypeC; auto. eapply TypeCSubtype; eauto. }
apply Ceq; auto. destruct H3.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ inv H0. inv H. eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto.
+ eapply CeqΠMatch; eauto.
+ eapply CeqΣMatch; eauto.
+ eapply CeqListMatch; eauto.
+ eapply CeqDoBind; eauto.
+ eapply CeqApp; eauto. eapply veq_subtype; eauto; inv H3; inv H5; inv H8.
  - apply WfTyFun; assumption.
  - apply SubtypeTyFun. apply vsubtype_refl. all: auto.
+ eapply CeqHandle; eauto. eapply veq_subtype; eauto; inv H3; inv H5; inv H8.
  - apply WfTyHandler; assumption.
  - apply SubtypeTyHandler. apply csubtype_refl. all: auto.
+ eapply CeqLetRec; eauto.
+ inv H0. eapply sig_subtype_get_Some in H3; eauto.
  destruct H3 as [A_op'[B_op'[gets[asty bsty]]]].
  eapply CeqOp; eauto.
  - eapply veq_subtype; eauto.
    eapply get_op_type_wf in gets. destruct gets. auto. inv H. auto.
  - eapply ctx_subtype_ceq; eauto.
    * eapply ceq_subtype; eauto. apply SubtypeCTy; auto.
    * apply WfCtxU. auto. 
      eapply get_op_type_wf in gets. destruct gets. auto. inv H. auto.
    * eapply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
+ inv H0. eapply OOTB; eauto. eapply eqs_subtype_contains; eauto.
  eapply wf_inst_tctx_subtype; eauto.
  apply SubtypeCTy; auto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βListMatch_Nil.
+ eapply βListMatch_Cons.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
+ eapply ηPair.
+ eapply ηSum.
+ eapply ηDoBind.
}
Qed.


Lemma heq_case_extend_trivial Σ D Γ h1 h2 op A1 A2 B1 B2 x1 x2 k1 k2 c1 c2:
  heq Σ D Γ h1 h2 -> find_case h1 op = None -> find_case h2 op = None ->
  has_ctype (CtxU (CtxU Γ (TyFun B1 D)) A1) c1 D ->
  has_ctype (CtxU (CtxU Γ (TyFun B2 D)) A2) c2 D ->
  heq Σ D Γ (CasesU h1 op x1 k1 c1) (CasesU h2 op x2 k2 c2).
Proof.
intros orig f1 f2 tys1 tys2.
assert (wf_vtype A1) as wfa1 by (inv tys1; inv H; auto).
assert (wf_vtype A2) as wfa2 by (inv tys2; inv H; auto).
assert (wf_vtype B1) as wfb1 by (inv tys1; inv H; inv H4; inv H6; auto).
assert (wf_vtype B2) as wfb2 by (inv tys2; inv H; inv H4; inv H6; auto).
assert (wf_ctype D) as wfd by (inv tys1; auto).
assert (wf_ctx Γ) as wfctx by (inv orig; inv H2; auto).
destruct orig.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H2; eauto. destruct H2 as [x[k[c f]]].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H3; eauto. destruct H3 as [x[k[c f]]].
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


Lemma heq_case_extend_structural Σ D Γ h1 h2 op A B x1 x2 k1 k2 c1 c2:
  heq Σ D Γ h1 h2 -> find_case h1 op = None -> find_case h2 op = None ->
  has_ctype (CtxU (CtxU Γ (TyFun B D)) A) c1 D ->
  has_ctype (CtxU (CtxU Γ (TyFun B D)) A) c2 D ->
  ceq D (CtxU (CtxU Γ (TyFun B D)) A) c1 c2 ->
  heq (SigU Σ op A B) D Γ (CasesU h1 op x1 k1 c1) (CasesU h2 op x2 k2 c2).
Proof.
intros orig f1 f2 tys1 tys2 ceq12.
assert (wf_vtype A) as wfa by (inv tys1; inv H; auto).
assert (wf_vtype B) as wfb by (inv tys1; inv H; inv H4; inv H6; auto).
assert (wf_ctype D) as wfd by (inv tys1; auto).
assert (wf_ctx Γ) as wfctx by (inv orig; inv H2; auto).
destruct orig.
assert (get_op_type Σ1 op = None) as getn1.
{ destruct (get_op_type Σ1 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H2; eauto. destruct H2 as [x[k[c f]]].
  rewrite f in f1. discriminate. }
assert (get_op_type Σ2 op = None) as getn2.
{ destruct (get_op_type Σ2 op) eqn: g. destruct p. 2: reflexivity.
  eapply h_has_case in H3; eauto. destruct H3 as [x[k[c f]]].
  rewrite f in f2. discriminate. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ1 op A B)) as ss1.
{ eapply SubtypeSigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
  inv H2. auto. simpl. destruct (op==op). reflexivity. destruct n. auto.
  all: apply vsubtype_refl; auto. }
assert (sig_subtype (SigU Σ op A B) (SigU Σ2 op A B)) as ss2.
{ eapply SubtypeSigU. apply sig_subtype_extend. auto. apply WfSigU; auto. 
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


Lemma veq_refl Γ v A : has_vtype Γ v A -> veq A Γ v v
with  ceq_refl Γ c C : has_ctype Γ c C -> ceq C Γ c c
with  heq_refl Γ h Σ D : has_htype Γ h Σ D -> heq Σ D Γ h h.
Proof.
all: intros orig.
{
apply Veq; auto. all: destruct orig; auto. destruct H1.
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
apply Ceq; auto. all: destruct orig; auto. destruct H1.
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
eapply Heq. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
assumption. assumption.
destruct orig. destruct H2.
+ eapply HeqSigØ.
+ assert (find_case (CasesU h op_id x k c_op) op_id = Some (x, k, c_op)).
  { simpl. destruct (op_id==op_id). auto. destruct n. auto. }
  eapply HeqSigU; eauto.
  eapply heq_case_extend_trivial; eauto; inv H0; assumption.
}
Qed.



Lemma veq_sym A Γ v1 v2:
  veq A Γ v1 v2 -> veq A Γ v2 v1
with ceq_sym C Γ c1 c2:
  ceq C Γ c1 c2 -> ceq C Γ c2 c1
with heq_sym Σ D Γ h1 h2:
  heq Σ D Γ h1 h2 -> heq Σ D Γ h1 h2.
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
