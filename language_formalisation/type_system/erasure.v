Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
Require Import syntax syntax_lemmas bidirectional declarational.


Ltac inv H := inversion H; clear H; subst.


Fixpoint vcheck_has_vtype Γ v A {struct v}:
  vcheck Γ v A -> has_vtype Γ (v_remove_annot v) A
with vsynth_has_vtype Γ v A {struct v}:
  vsynth Γ v A -> has_vtype Γ (v_remove_annot v) A
with ccheck_has_ctype Γ c C {struct c}:
  ccheck Γ c C -> has_ctype Γ (c_remove_annot c) C
with csynth_has_ctype Γ c C {struct c}:
  csynth Γ c C -> has_ctype Γ (c_remove_annot c) C
with hcheck_has_htype Γ h Σ D {struct h}:
  hcheck Γ h Σ D -> has_htype Γ (h_remove_annot h) Σ D.
Proof.
{
clear vcheck_has_vtype.
revert Γ A. induction v; intros Γ A orig; inv orig; try inv H; simpl.
+ apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv. assumption.
+ apply TypeInr. apply IHv. assumption.
+ apply TypePair; auto.
+ apply TypeFun. auto.
+ apply TypeHandler; auto.
+ auto.
}{
clear vsynth_has_vtype.
revert Γ A. induction v; intros Γ A orig; inv orig; simpl.
+ apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypePair; auto.
+ auto.
}{
clear ccheck_has_ctype.
revert Γ C. induction c; intros Γ C orig; inv orig; try inv H; simpl.
+ apply TypeRet. auto.
+ eapply TypeΠMatch. apply vsynth_has_vtype; exact H5.
  apply csynth_has_ctype. assumption.
+ eapply TypeΣMatch. apply vsynth_has_vtype; exact H6. auto. auto.
+ eapply TypeApp. apply vsynth_has_vtype. exact H3. auto.
+ eapply TypeOp; try exact H5 || auto.
+ eapply TypeLetRec. apply IHc1. exact H7. auto.
+ eapply TypeDoBind.
  - apply csynth_has_ctype in H4. exact H4.
  - apply IHc2. assumption.
+ eapply TypeHandle. apply vsynth_has_vtype. exact H3. auto.
+ auto. 
}{
clear csynth_has_ctype.
revert Γ C. induction c; intros Γ C orig; inv orig; simpl.
+ apply TypeRet. auto.
+ eapply TypeΠMatch. apply vsynth_has_vtype; exact H4. auto.
+ eapply TypeApp. apply vsynth_has_vtype; exact H2. auto.
+ eapply TypeLetRec. apply ccheck_has_ctype. exact H6. auto.
+ eapply TypeHandle. apply vsynth_has_vtype; exact H2. auto.
+ auto.
}{
clear hcheck_has_htype.
revert Γ Σ D. induction h; intros Γ Σ D orig; inv orig; simpl.
+ apply TypeCasesØ.
+ apply TypeCasesU; auto. rewrite <-find_op_remove_annot.
  rewrite H7. simpl. reflexivity.
}
Qed.


Fixpoint has_vtype_vsynths_with_annot Γ v A {struct v}:
  has_vtype Γ v A -> 
    exists v', vsynth Γ v' A /\ v = v_remove_annot v'
with has_ctype_csynths_with_annot Γ c C {struct c}:
  has_ctype Γ c C ->
    exists c', csynth Γ c' C /\ c = c_remove_annot c'
with has_htype_hchecks_with_annot Γ h Σ D {struct h}:
  has_htype Γ h Σ D ->
    exists h', hcheck Γ h' Σ D /\ h = h_remove_annot h'.
Proof.
all:
rename has_vtype_vsynths_with_annot into vLemma;
rename has_ctype_csynths_with_annot into cLemma;
rename has_htype_hchecks_with_annot into hLemma.
{
clear vLemma.
revert Γ A. induction v; intros Γ A orig.
- destruct v as (name, num).
  exists (Ann_Var (name, num)). constructor.
  + apply SynthVar. inv orig. assumption.
  + reflexivity.
- exists Ann_Unit. constructor.
  + inv orig. apply SynthUnit.
  + reflexivity.
- exists (Ann_Int t). constructor.
  + inv orig. apply SynthInt.
  + reflexivity.
- (* Annotate sumtypes *)
  inv orig. apply IHv in H1. destruct H1 as [v' [vty' same]].
  exists (Ann_Val (Ann_Inl v') (TyΣ A0 B)). constructor.
  + apply SynthVAnnot. apply CheckInl. apply CheckVBySynth. assumption.
  + simpl. f_equal. assumption.
- (* Annotate sumtypes *)
  inv orig. apply IHv in H1. destruct H1 as [v' [vty' same]].
  exists (Ann_Val (Ann_Inr v') (TyΣ A0 B)). constructor.
  + apply SynthVAnnot. apply CheckInr. apply CheckVBySynth. assumption.
  + simpl. f_equal. assumption.
- inv orig.
  apply IHv1 in H2. destruct H2 as [v1' [v1ty' same1]].
  apply IHv2 in H4. destruct H4 as [v2' [v2ty' same2]].
  exists (Ann_Pair v1' v2'). constructor.
  + apply SynthPair; assumption.
  + simpl. f_equal; assumption.
- inv orig. (* Annotate functions. *)
  apply cLemma in H3. destruct H3 as [c' [cty' same]].
  exists (Ann_Val (Ann_Fun v c') (TyFun A0 C)). constructor.
  + apply SynthVAnnot. apply CheckFun. eapply CheckCBySynth. exact cty'.
  + simpl. f_equal. assumption.
- inv orig. (* Annotate functions. *)
  apply cLemma in H4. destruct H4 as [c_r' [cty' samec]].
  apply hLemma in H5. destruct H5 as [h' [hty' sameh]].
  exists (Ann_Val (Ann_Handler v c_r' h') (TyHandler (CTy A0 sig eqs) D)).
  constructor.
  + apply SynthVAnnot. apply CheckHandler;
    try eapply CheckCBySynth; auto.
  + simpl. f_equal; assumption.
}{
clear cLemma.
revert Γ C. induction c; intros Γ C orig.
- inv orig.
  apply vLemma in H1. destruct H1 as [v' [vty' same]].
  exists (Ann_Ret v'). constructor.
  + apply SynthRet. assumption.
  + simpl. f_equal. assumption.
- inv orig.
  apply vLemma in H4. destruct H4 as [v' [vty' same]].
  apply IHc in H5. destruct H5 as [c' [cty' csame]].
  exists (Ann_ΠMatch v' (x,y) c'). constructor.
  + eapply SynthΠMatch. exact vty'. assumption.
  + simpl. f_equal; assumption.
- (* Annotate sum match. *)
  inv orig. rename v0 into x. rename v1 into y.
  apply vLemma in H6. destruct H6 as [v' [vty' vsame]]. 
  apply IHc1 in H7. destruct H7 as [c1' [c1ty' c1same]].
  apply IHc2 in H8. destruct H8 as [c2' [c2ty' c2same]].
  exists (Ann_Comp (Ann_ΣMatch v' x c1' y c2') C). constructor.
  + apply SynthCAnnot. eapply CheckΣMatch. exact vty'. 
    eapply CheckCBySynth. exact c1ty'.
    eapply CheckCBySynth. exact c2ty'.
  + simpl. f_equal; assumption.
- inv orig.
  apply vLemma in H2. destruct H2 as [v1' [v1ty' v1same]]. 
  apply vLemma in H4. destruct H4 as [v2' [v2ty' v2same]].
  exists (Ann_App v1' v2'). constructor.
  + eapply SynthApp. exact v1ty'. apply CheckVBySynth. assumption.
  + simpl. f_equal; assumption.
- inv orig. (* Annotate operations! *)
  apply vLemma in H6. destruct H6 as [v' [vty' vsame]].
  apply IHc in H7. destruct H7 as [c' [cty' csame]].
  exists (Ann_Comp (Ann_Op o v' v0 c') (CTy A Σ eqs)). constructor.
  + eapply SynthCAnnot. eapply CheckOp. exact H5.
    apply CheckVBySynth. assumption. eapply CheckCBySynth. exact cty'.
  + simpl. f_equal; assumption.
- inv orig. rename v into f. rename v0 into x.
  apply IHc1 in H5. destruct H5 as [c1' [c1ty' c1same]].
  apply IHc2 in H6. destruct H6 as [c2' [c2ty' c2same]].
  exists (Ann_LetRec f x (TyFun A C0) c1' c2'). constructor.
  + apply SynthLetRec. eapply CheckCBySynth. exact c1ty'. assumption.
  + simpl. f_equal; assumption.
- inv orig. (* Annotate binds! *)
  apply IHc1 in H4. destruct H4 as [c1' [c1ty' c1same]].
  apply IHc2 in H5. destruct H5 as [c2' [c2ty' c2same]].
  exists (Ann_Comp (Ann_DoBind v c1' c2') (CTy B Σ eqs)). constructor.
  apply SynthCAnnot. eapply CheckDoBind.
  + exact c1ty'.
  + apply CheckCBySynth. assumption.
  + simpl. f_equal; assumption.
- inv orig.
  apply vLemma in H2. destruct H2 as [v' [vty' vsame]].
  apply IHc in H4. destruct H4 as [c' [cty' csame]].
  exists (Ann_Handle v' c'). constructor.
  + eapply SynthHandle. exact vty'. eapply CheckCBySynth. exact cty'.
  + simpl. f_equal; assumption.
}{
clear hLemma.
revert Γ Σ D. induction h; intros Γ Σ D orig.
- inv orig. exists Ann_CasesØ. constructor. apply CheckCasesØ. reflexivity.
- inv orig. rename v into x. rename v0 into k.
  apply IHh in H8. destruct H8 as [h' [hty' hsame]].
  apply cLemma in H9. destruct H9 as [c' [cty' csame]].
  exists (Ann_CasesU h' o x k c'). constructor.
  + apply CheckCasesU.
    * assert (forall h h',
        h = h_remove_annot h' ->
        find_op_case h o = None -> find_op_ann_case h' o = None ).
      intros H. induction H; intros H' eq nocase; destruct H'.
      ++ simpl. reflexivity.
      ++ simpl in eq. discriminate.
      ++ simpl in eq. discriminate.
      ++ simpl in eq. injection eq. intros. subst.
         simpl in *. destruct (o==o1). discriminate.
         apply IHhcases. reflexivity. assumption.
      ++ eapply H. exact hsame. assumption.
    * assumption.
    * eapply CheckCBySynth. exact cty'.
  + simpl. f_equal; assumption.
}
Qed.

