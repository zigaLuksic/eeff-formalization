Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export syntax_lemmas substitution_lemmas subtyping_lemmas.

(* ==================== Logic Subtyping ==================== *)

Fixpoint veq_subtype A A' Γ v1 v2 (orig : veq A Γ v1 v2) {struct orig} :
  wf_vtype A' -> vsubtype A A' -> veq A' Γ v1 v2

with ceq_subtype C C' Γ c1 c2 (orig : ceq C Γ c1 c2) {struct orig} :
  wf_ctype C' -> csubtype C C' -> ceq C' Γ c1 c2

with heq_subtype Σ Σ' D D' Γ h1 h2 (orig : heq Σ D Γ h1 h2) {struct orig} :
  wf_sig Σ' -> wf_ctype D' -> sig_subtype Σ' Σ -> csubtype D D' -> 
  heq Σ' D' Γ h1 h2.

Proof.
{ 
intros. inv orig.
assert (has_vtype Γ v1 A') as ty1.
{ apply TypeV; auto. eapply TypeVSubtype; eauto. }
assert (has_vtype Γ v2 A') as ty2.
{ apply TypeV; auto. eapply TypeVSubtype; eauto. }
induction H5; apply Veq; auto.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply VeqVar; eauto. eapply vsubtype_trans; eauto.
+ inv H0. apply VeqUnit; eauto.
+ inv H0. apply VeqInt; eauto.
+ inv H0. inv H. eapply VeqPair; eapply veq_subtype; eauto.
+ inv H0. eapply VeqInl. eapply veq_subtype; eauto. inv H. auto.
+ inv H0. eapply VeqInr. eapply veq_subtype; eauto. inv H. auto.
+ inv H0. apply VeqFun. inv H. eapply ceq_subtype in H5; eauto.
  eapply ctx_subtype_ceq. eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. auto.
+ inv H0. inv H9. apply VeqHandler. eapply ceq_subtype in H5; eauto.
  eapply ctx_subtype_ceq. eauto. all: inv H.
  - apply WfCtxU; auto. inv H8.  assumption.
  - apply SubtypeCtxU; auto. apply ctx_subtype_refl. auto.
  - assumption.
  - eapply heq_subtype. eauto. inv H8. all: assumption.
+ inv H0. apply ηUnit.
+ inv H0. apply ηFun.
}{
intros. inv orig. 
assert (has_ctype Γ c1 C') as ty1.
{ apply TypeC; auto. eapply TypeCSubtype; eauto. }
assert (has_ctype Γ c2 C') as ty2.
{ apply TypeC; auto. eapply TypeCSubtype; eauto. }
apply Ceq; auto. destruct H5.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ inv H0. inv H. eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto.
+ eapply CeqΠMatch; eauto.
+ eapply CeqΣMatch; eauto.
+ eapply CeqDoBind; eauto.
+ eapply CeqApp; eauto. eapply veq_subtype; eauto; inv H5; inv H7.
  - apply WfTyFun; assumption.
  - apply SubtypeTyFun. apply vsubtype_refl. all: auto.
+ eapply CeqHandle; eauto. eapply veq_subtype; eauto; inv H5; inv H7.
  - apply WfTyHandler; assumption.
  - apply SubtypeTyHandler. apply csubtype_refl. all: auto.
+ eapply CeqLetRec; eauto.
+ inv H0. eapply sig_subtype_get_Some in H5; eauto.
  destruct H5 as [A_op'[B_op'[gets[asty bsty]]]].
  eapply CeqOp; eauto.
  - eapply veq_subtype; eauto.
    eapply get_op_type_wf in gets. destruct gets. auto.
    inv H. auto.
  - eapply ctx_subtype_ceq; eauto.
    * eapply ceq_subtype; eauto. apply SubtypeCTy; auto.
    * apply WfCtxU. auto. 
      eapply get_op_type_wf in gets. destruct gets. auto.
      inv H. auto.
    * eapply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
}{
intros. inv orig.
assert (has_htype Γ h1 Σ' D') as ty1.
{ apply TypeH; eauto. eapply TypeHSubtype; eauto. }
assert (has_htype Γ h2 Σ' D') as ty2.
{ apply TypeH; eauto. eapply TypeHSubtype; eauto. }
apply Heq; auto. destruct H8.
+ apply HeqSym. eauto.
+ eapply HeqTrans; eauto.
+ inv H1. eapply HeqSigØ. simpl in H9. discriminate.
+ destruct Σ' as [ | Σ' o A' B']. apply HeqSigØ. destruct (o==op).
  - subst. eapply HeqSigU; eauto. eapply ceq_subtype; eauto.
    eapply ctx_subtype_ceq; eauto.
    * inv H. apply WfCtxU; eauto. apply WfCtxU; eauto. apply WfTyFun; eauto.
    * inv H1. simpl in H18. destruct (op==op). 2: destruct n; reflexivity.
      inv H18. apply SubtypeCtxU; eauto. apply SubtypeCtxU; eauto.
      apply ctx_subtype_refl. auto. apply SubtypeTyFun; eauto.
}
Admitted.


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
+ apply VeqFun; eauto.
+ apply VeqHandler; eauto.
+ apply veq_refl in H1. eapply veq_subtype in H1; eauto. inv H1. assumption.
}{
apply Ceq; auto. all: destruct orig; auto. destruct H1.
+ apply CeqRet. auto.
+ apply CeqAbsurd. auto.
+ eapply CeqΠMatch; eauto.
+ eapply CeqΣMatch; eauto.
+ eapply CeqDoBind; eauto. 
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec; eauto.
+ eapply CeqOp; eauto.
+ apply ceq_refl in H1. eapply ceq_subtype in H1; eauto. inv H1. assumption.
}{
apply Heq; auto. all: try (destruct orig; assumption). destruct Σ.
+ eapply HeqSigØ.
+ eapply h_has_case in orig as finds. 2: instantiate (3:=o).
  2: simpl; destruct (o==o). 2: reflexivity. destruct finds as [x[k[c]]].
  eapply HeqSigU; eauto.
  simpl.  destruct (op_id==op_id). reflexivity. destruct n. reflexivity.
  simpl. destruct (op_id==op_id). reflexivity. destruct n. reflexivity.
  auto. apply heq_refl.
}
admit. admit.
Admitted.





