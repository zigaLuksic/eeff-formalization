(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\skeletons". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\skeletons".
Require Export skeletons subtyping_lemmas.


Lemma skeletons_ignore_vsubtype A A':
  vsubtype A A' -> skeletize_vtype A = skeletize_vtype A'
with skeletons_ignore_csubtype C C':
  csubtype C C' -> skeletize_ctype C = skeletize_ctype C'.
Proof.
all: intros sty; induction sty; simpl; f_equal; auto.
apply skeletons_ignore_csubtype in H. auto.
Qed.


Fixpoint skeleton_val_type Γ v A (types : has_vtype Γ v A) {struct types}:
  has_sk_vtype (skeletize_ctx Γ) (skeletize_val v) (skeletize_vtype A)
with skeleton_comp_type Γ c C (types : has_ctype Γ c C) {struct types}:
  has_sk_ctype (skeletize_ctx Γ) (skeletize_comp c) (skeletize_ctype C)
with skeleton_hcases_type Γ h Σ D (types : has_htype Γ h Σ D) {struct types}:
  has_sk_htype (skeletize_ctx Γ) (skeletize_hcases h) (skeletize_ctype D).
Proof.
all: rename skeleton_val_type into VL.
all: rename skeleton_comp_type into CL.
all: rename skeleton_hcases_type into HL.
{
destruct types. destruct H1; simpl.
+ apply SkTypeUnit.
+ apply SkTypeInt.
+ apply SkTypeVar.
  assert (forall n γ A, get_vtype γ n = Some A ->
    get_sk_vtype (skeletize_ctx γ) n = Some (skeletize_vtype A)).
  { intros k γ B. revert k. induction γ; intros k gets. discriminate. simpl.
    destruct k. 
    + simpl in gets. inv gets. auto.
    + simpl in *. auto. }
  apply H2. auto.
+ apply SkTypePair; eauto.
+ apply SkTypeLeft; eauto.
+ apply SkTypeRight; eauto.
+ apply SkTypeNil.
+ apply SkTypeCons; eauto. apply VL in H2. simpl in *. auto.
+ apply SkTypeFun. eapply CL in H1. simpl in *. auto.
+ apply SkTypeHandler. 
  eapply CL in H1. simpl in *. auto.
  eapply HL in H2. simpl in *. auto.
+ eapply VL in H1. simpl in *.
  apply skeletons_ignore_vsubtype in H2. inv H2. auto.
}{
destruct types. destruct H1; simpl.
+ apply SkTypeRet. eauto.
+ apply SkTypeAbsurd. eapply VL in H1. simpl in *. auto.
+ eapply SkTypeProdMatch.
  eapply VL in H1. simpl in *. eauto.
  eapply CL in H2. simpl in *. auto.
+ eapply SkTypeSumMatch.
  eapply VL in H1. simpl in *. eauto.
  eapply CL in H2. simpl in *. auto.
  eapply CL in H3. simpl in *. auto.
+ eapply SkTypeListMatch.
  eapply VL in H1. simpl in *. eauto.
  eapply CL in H2. simpl in *. auto.
  eapply CL in H3. simpl in *. auto.
+ eapply SkTypeDo.
  eapply CL in H1. simpl in *. eauto.
  eapply CL in H2. simpl in *. auto.
+ eapply SkTypeApp; eauto.
  eapply VL in H1. simpl in *. auto.
+ eapply SkTypeHandle; eauto.
  eapply VL in H1. simpl in *. auto.
+ eapply SkTypeLetRec.
  eapply CL in H1. simpl in *. eauto.
  eapply CL in H2. simpl in *. auto.
+ eapply SkTypeOp. eauto.
  eapply CL in H7. simpl in *. auto.
+ eapply CL in H1. simpl in *.
  apply skeletons_ignore_csubtype in H2. inv H2. auto.
}{
destruct types. destruct H2; simpl.
+ apply SkTypeCasesØ.
+ eapply SkTypeCasesU. eauto.
  eapply CL in H3. simpl in *. auto.
}
Qed.

