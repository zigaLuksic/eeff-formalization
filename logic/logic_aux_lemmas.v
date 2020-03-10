(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".

Require Export subtyping_lemmas.


(* ================== Reflexivity, Symmetry, Transitivity ================== *)

(* We 'upgrade' it to arbitrary hypotheses in aux_type_lemmas *)
Lemma veq_refl_raw Γ v A : 
  has_vtype Γ v A -> judg Γ HypØ (Veq A v v)
with ceq_refl_raw Γ c C : 
  has_ctype Γ c C -> judg Γ HypØ (Ceq C c c)
with heq_refl_raw Γ h Σ D : 
  has_htype Γ h Σ D -> judg Γ HypØ (Heq Σ D h h).
Proof.
all: intros orig.
{
apply WfJudg. apply WfVeq; auto. apply WfHypØ. inv orig. auto.
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
+ apply veq_refl_raw in H1. eapply VeqSubtype; eauto.
}{
apply WfJudg. apply WfCeq; auto. apply WfHypØ. inv orig. auto.
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
+ apply ceq_refl_raw in H1. eapply CeqSubtype; eauto.
}{
apply WfJudg. eapply WfHeq; auto.
inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
apply sig_subtype_refl. inv orig. assumption.
assumption. assumption. apply WfHypØ. inv orig. assumption.
destruct orig. destruct H2.
+ eapply HeqSigØ.
+ eapply HeqExtend; eauto.
}
Qed.


Lemma veq_sym A Γ Ψ v1 v2 : 
  judg Γ Ψ (Veq A v1 v2) -> judg Γ Ψ (Veq A v2 v1)
with ceq_sym C Γ Ψ c1 c2 : 
  judg Γ Ψ (Ceq C c1 c2) -> judg Γ Ψ (Ceq C c2 c1)
with heq_sym Σ D Γ Ψ h1 h2 : 
  judg Γ Ψ (Heq Σ D h1 h2) -> judg Γ Ψ (Heq Σ D h2 h1).
Proof.
{
intro orig. apply WfJudg. apply WfVeq. all: try (inv orig; inv H; assumption).
apply VeqSym. auto.
}{
intro orig. apply WfJudg. apply WfCeq. all: try (inv orig; inv H; assumption).
apply CeqSym. auto.
}{
intro orig. apply WfJudg. inv orig. inv H.
eapply WfHeq. 3: exact H8. all: eauto. inv orig. auto.
apply HeqSym. auto.
}
Qed.

    
Lemma veq_trans A Γ Ψ v1 v2 v3:
  judg Γ Ψ (Veq A v1 v2) -> judg Γ Ψ (Veq A v2 v3) -> judg Γ Ψ (Veq A v1 v3)

with  ceq_trans C Γ Ψ c1 c2 c3:
  judg Γ Ψ (Ceq C c1 c2) -> judg Γ Ψ (Ceq C c2 c3) -> judg Γ Ψ (Ceq C c1 c3)

with  heq_trans Σ D Γ Ψ h1 h2 h3:
  judg Γ Ψ (Heq Σ D h1 h2) -> judg Γ Ψ (Heq Σ D h2 h3) -> 
  judg Γ Ψ (Heq Σ D h1 h3).

Proof.
{
intros veq1 veq2. apply WfJudg. apply WfVeq. 
+ inv veq1. inv H. auto.
+ inv veq2. inv H. auto.
+ inv veq1. auto.
+ eapply VeqTrans; eauto.
}{
intros ceq1 ceq2. apply WfJudg. apply WfCeq. 
+ inv ceq1. inv H. auto.
+ inv ceq2. inv H. auto.
+ inv ceq1. auto.
+ eapply CeqTrans; eauto.
}{
intros heq1 heq2. apply WfJudg. 
+ inv heq1. inv H. inv heq2. inv H. eapply WfHeq.
  4: eauto. 4: eauto. all:eauto.
+ inv heq1. auto.
+ eapply HeqTrans; eauto.
}
Qed.
