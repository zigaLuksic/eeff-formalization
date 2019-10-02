Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
Require Import syntax bidirectional.

Inductive has_vtype : ctx -> val -> vtype -> Prop :=
| TypeUnit Γ : has_vtype Γ Unit TyUnit 
| TypeInt Γ n : has_vtype Γ (Int n) TyInt
| TypeVar Γ id A :
    get_vtype Γ id = Some A ->
    has_vtype Γ (Var id) A
| TypePair Γ v1 v2 A B :
    has_vtype Γ v1 A ->
    has_vtype Γ v2 B ->
    has_vtype Γ (Pair v1 v2) (TyΠ A B)
| TypeVAnnot Γ v A :
    has_vtype Γ v A ->
    has_vtype Γ (VAnnot v A) A
| TypeInl Γ v A B :
    has_vtype Γ v A ->
    has_vtype Γ (Inl v) (TyΣ A B)
| TypeInr Γ v A B :
    has_vtype Γ v B ->
    has_vtype Γ (Inr v) (TyΣ A B)
| TypeFun Γ x c A C :
    has_ctype (CtxU Γ A) c C ->
    has_vtype Γ (Fun x c) (TyFun A C)
| TypeHandler Γ x c_ret h A sig eqs D :
    has_ctype (CtxU Γ A) c_ret D ->
    has_htype Γ h sig D ->
    has_vtype Γ (Handler x c_ret h) (TyHandler (CTy A sig eqs) D)
with has_ctype : ctx -> comp -> ctype -> Prop :=
| TypeRet Γ v A : 
    has_vtype Γ v A ->
    has_ctype Γ (Ret v) (CTy A SigØ EqsØ)
| TypeΠMatch Γ v A B x y c C :
    has_vtype Γ v (TyΠ A B) ->
    has_ctype (CtxU (CtxU Γ A) B) c C ->
    has_ctype Γ (ΠMatch v (x, y) c) C
| TypeApp Γ v1 v2 A C :
    has_vtype Γ v1 (TyFun A C) ->
    has_vtype Γ v2 A ->
    has_ctype Γ (App v1 v2) C
| TypeHandle Γ v c C D :
    has_vtype Γ v (TyHandler C D) ->
    has_ctype Γ c C ->
    has_ctype Γ (Handle v c) D
| TypeCAnnot Γ c C :
    has_ctype Γ c C ->
    has_ctype Γ (CAnnot c C) C
| TypeLetRec Γ f x A C c1 c2 D:
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C ->
    has_ctype (CtxU Γ (TyFun A C)) c2 D ->
    has_ctype Γ (LetRec f x (TyFun A C) c1 c2) D
| TypeΣMatch Γ v A B xl cl xr cr C :
    has_vtype Γ v (TyΣ A B) ->
    has_ctype (CtxU Γ A) cl C ->
    has_ctype (CtxU Γ B) cr C ->
    has_ctype Γ (ΣMatch v xl cl xr cr) C
| TypeOp Γ op_id v y c A_op B_op A Σ eqs :
    get_op_type Σ op_id = Some (A_op, B_op) ->
    has_vtype Γ v A_op ->
    has_ctype (CtxU Γ B_op) c (CTy A Σ eqs) ->
    has_ctype Γ (Op op_id v y c) (CTy A Σ eqs)
with has_htype : ctx -> hcases -> sig -> ctype -> Prop :=
| TypeCasesØ Γ D : has_htype Γ CasesØ SigØ D
| TypeCasesU Γ h op_id x k c_op A_op B_op Σ D :
    find_op_case h op_id = None ->
    has_htype Γ h Σ D ->
    has_ctype (CtxU (CtxU Γ (TyFun B_op D)) A_op) c_op D ->
    has_htype 
      Γ (CasesU h op_id x k c_op)
      (SigU Σ op_id A_op B_op) D
.

Ltac inv H := inversion H; clear H; subst.


Fixpoint vcheck_has_vtype Γ v A {struct v}:
  vcheck Γ v A -> has_vtype Γ v A
with vsynth_has_vtype Γ v A {struct v}:
  vsynth Γ v A -> has_vtype Γ v A
with ccheck_has_ctype Γ c C {struct c}:
  ccheck Γ c C -> has_ctype Γ c C
with csynth_has_ctype Γ c C {struct c}:
  csynth Γ c C -> has_ctype Γ c C
with hcheck_has_htype Γ h Σ D {struct h}:
  hcheck Γ h Σ D -> has_htype Γ h Σ D.
Proof.
{
clear vcheck_has_vtype.
revert Γ A. induction v; intros Γ A orig; inv orig; try inv H.
+ apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv. assumption.
+ apply TypeInr. apply IHv. assumption.
+ apply TypePair; auto.
+ apply TypeFun. auto.
+ apply TypeHandler; auto.
+ apply TypeVAnnot; auto.
}{
clear vsynth_has_vtype.
revert Γ A. induction v; intros Γ A orig; inv orig.
+ apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypePair; auto.
+ apply TypeVAnnot. auto.
}{
clear ccheck_has_ctype.
revert Γ C. induction c; intros Γ C orig; inv orig; try inv H.
+ apply TypeRet. auto.
+ eapply TypeΠMatch. apply vsynth_has_vtype; exact H5.
  apply csynth_has_ctype. assumption.
+ eapply TypeΣMatch. apply vsynth_has_vtype; exact H6. auto. auto.
+ eapply TypeApp. apply vsynth_has_vtype. exact H3. auto.
+ eapply TypeOp; try exact H5 || auto.
+ apply TypeLetRec; auto.
+ eapply TypeHandle. apply vsynth_has_vtype. exact H3. auto.
+ apply TypeCAnnot. auto. 
}{
clear csynth_has_ctype.
revert Γ C. induction c; intros Γ C orig; inv orig.
+ apply TypeRet. auto.
+ eapply TypeΠMatch. apply vsynth_has_vtype; exact H4. auto.
+ eapply TypeApp. apply vsynth_has_vtype; exact H2. auto.
+ apply TypeLetRec. auto. apply IHc2. assumption.
+ eapply TypeHandle. apply vsynth_has_vtype; exact H2. auto.
+ eapply TypeCAnnot. auto.
}{
clear hcheck_has_htype.
revert Γ Σ D. induction h; intros Γ Σ D orig; inv orig.
+ apply TypeCasesØ.
+ apply TypeCasesU; auto.
}
Qed.


Fixpoint v_remove_annot v :=
match v with
| Var id => Var id
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_remove_annot v')
| Inr v' => Inr (v_remove_annot v')
| Pair v1 v2 => Pair (v_remove_annot v1) (v_remove_annot v2)
| Fun x c => Fun x (c_remove_annot c)
| Handler x c_ret h => Handler x (c_remove_annot c_ret) (h_remove_annot h)
| VAnnot v' A => v_remove_annot v'
end
with c_remove_annot c :=
match c with
| Ret v => Ret (v_remove_annot v)
| ΠMatch v (x, y) c => ΠMatch (v_remove_annot v) (x,y) (c_remove_annot c)
| ΣMatch v xl cl xr cr => 
    ΣMatch (v_remove_annot v) xl (c_remove_annot cl) xr (c_remove_annot cr)
| App v1 v2 => App (v_remove_annot v1) (v_remove_annot v2)
| Op op v_arg y c => Op op (v_remove_annot v_arg) y (c_remove_annot c)
| LetRec f x f_ty c1 c2 =>
    LetRec f x f_ty (c_remove_annot c1) (c_remove_annot c2)
| DoBind x c1 c2 => DoBind x (c_remove_annot c1) (c_remove_annot c2)
| Handle v c' => Handle (v_remove_annot v) (c_remove_annot c')
| CAnnot c' C => (c_remove_annot c')
end
with h_remove_annot h :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c =>
    CasesU (h_remove_annot h) op x k (c_remove_annot c)
end.

Lemma v_type_remove_annot Γ v A:
  has_vtype Γ v A -> has_vtype Γ (v_remove_annot v) A
with c_type_remove_annot Γ c C:
  has_ctype Γ c C -> has_ctype Γ (c_remove_annot c) C
with h_type_remove_annot Γ h Σ D:
  has_htype Γ h Σ D -> has_htype Γ (h_remove_annot h) Σ D.
Proof.
{
revert Γ A. induction v; intros Γ A orig; inv orig; simpl; auto.
+ apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv. assumption.
+ apply TypeInr. apply IHv. assumption.
+ apply TypePair; auto.
+ apply TypeFun. auto.
+ apply TypeHandler; auto.
}{
revert Γ C. induction c; intros Γ C orig; inv orig; simpl; auto.
+ apply TypeRet. auto.
+ eapply TypeΠMatch. apply v_type_remove_annot. exact H4.
  apply c_type_remove_annot. assumption.
+ eapply TypeΣMatch. apply v_type_remove_annot. exact H6. auto. auto.
+ eapply TypeApp. apply v_type_remove_annot. exact H2. auto.
+ eapply TypeOp; try exact H5 || auto.
+ apply TypeLetRec; auto.
+ eapply TypeHandle. apply v_type_remove_annot. exact H2. auto.
}{
revert Γ Σ D. induction h; intros Γ Σ D orig; inv orig; simpl; auto.
+ apply TypeCasesØ.
+ apply TypeCasesU; auto.
  assert (forall h o,
    find_op_case h o = None -> find_op_case (h_remove_annot h) o = None).
  { intros h' op orig. induction h'.
    * simpl. auto.
    * simpl. simpl in *. destruct (op == o0).
      ++ discriminate.
      ++ auto.
  }
  apply H. auto.
}
Qed.


Fixpoint has_vtype_vsynths_with_annot Γ v A {struct v}:
  has_vtype Γ v A -> 
    exists v', vsynth Γ v' A /\ v_remove_annot v = v_remove_annot v'
with has_ctype_csynths_with_annot Γ c C {struct c}:
  has_ctype Γ c C ->
    exists c', csynth Γ c' C /\ c_remove_annot c = c_remove_annot c'
with has_htype_hchecks_with_annot Γ h Σ D {struct h}:
  has_htype Γ h Σ D ->
    exists h', hcheck Γ h' Σ D /\ h_remove_annot h = h_remove_annot h'.
Proof.
all:
rename has_vtype_vsynths_with_annot into vLemma;
rename has_ctype_csynths_with_annot into cLemma;
rename has_htype_hchecks_with_annot into hLemma.
{
clear vLemma.
revert Γ A. induction v; intros Γ A orig.
- exists (Var v). constructor.
  + apply SynthVar. inv orig. assumption.
  + reflexivity.
- exists Unit. constructor.
  + inv orig. apply SynthUnit.
  + reflexivity.
- exists (Int t). constructor.
  + inv orig. apply SynthInt.
  + reflexivity.
- (* Annotate sumtypes *)
  inv orig. apply IHv in H1. destruct H1 as [v' [vty' same]].
  exists (VAnnot (Inl v') (TyΣ A0 B)). constructor.
  + apply SynthVAnnot. apply CheckInl. apply CheckVBySynth. assumption.
  + simpl. f_equal. assumption.
- (* Annotate sumtypes *)
  inv orig. apply IHv in H1. destruct H1 as [v' [vty' same]].
  exists (VAnnot (Inr v') (TyΣ A0 B)). constructor.
  + apply SynthVAnnot. apply CheckInr. apply CheckVBySynth. assumption.
  + simpl. f_equal. assumption.
- inv orig.
  apply IHv1 in H2. destruct H2 as [v1' [v1ty' same1]].
  apply IHv2 in H4. destruct H4 as [v2' [v2ty' same2]].
  exists (Pair v1' v2'). constructor.
  + apply SynthPair; assumption.
  + simpl. f_equal; assumption.
- inv orig. (* Annotate functions. *)
  apply cLemma in H3. destruct H3 as [c' [cty' same]].
  exists (VAnnot (Fun v c') (TyFun A0 C)). constructor.
  + apply SynthVAnnot. apply CheckFun. eapply CheckCBySynth. exact cty'. auto.
  + simpl. f_equal. assumption.
- inv orig. (* Annotate functions. *)
  apply cLemma in H4. destruct H4 as [c_r' [cty' samec]].
  apply hLemma in H5. destruct H5 as [h' [hty' sameh]].
  exists (VAnnot (Handler v c_r' h') (TyHandler (CTy A0 sig eqs) D)).
  constructor.
  + apply SynthVAnnot. apply CheckHandler;
    try eapply CheckCBySynth; auto. auto.
  + simpl. f_equal; assumption.
- inv orig. apply IHv in H3. destruct H3 as [v' [vty' same1]].
  exists (VAnnot v' A). constructor.
  + apply SynthVAnnot. apply CheckVBySynth. assumption.
  + simpl. assumption.
}{
clear cLemma.
revert Γ C. induction c; intros Γ C orig.
- inv orig.
  apply vLemma in H1. destruct H1 as [v' [vty' same]].
  exists (Ret v'). constructor.
  + apply SynthRet. assumption.
  + simpl. f_equal. assumption.
- inv orig.
  apply vLemma in H4. destruct H4 as [v' [vty' same]].
  apply IHc in H5. destruct H5 as [c' [cty' csame]].
  exists (ΠMatch v' (x,y) c'). constructor.
  + eapply SynthΠMatch. exact vty'. assumption.
  + simpl. f_equal; assumption.
- (* Annotate sum match. *)
  inv orig. rename v0 into x. rename v1 into y.
  apply vLemma in H6. destruct H6 as [v' [vty' vsame]]. 
  apply IHc1 in H7. destruct H7 as [c1' [c1ty' c1same]].
  apply IHc2 in H8. destruct H8 as [c2' [c2ty' c2same]].
  exists (CAnnot (ΣMatch v' x c1' y c2') C). constructor.
  + apply SynthCAnnot. eapply CheckΣMatch. exact vty'. 
    eapply CheckCBySynth. exact c1ty'. reflexivity.
    eapply CheckCBySynth. exact c2ty'. reflexivity.
  + simpl. f_equal; assumption.
- inv orig.
  apply vLemma in H2. destruct H2 as [v1' [v1ty' v1same]]. 
  apply vLemma in H4. destruct H4 as [v2' [v2ty' v2same]].
  exists (App v1' v2'). constructor.
  + eapply SynthApp. exact v1ty'. apply CheckVBySynth. assumption.
  + simpl. f_equal; assumption.
- inv orig. (* Annotate operations! *)
  apply vLemma in H6. destruct H6 as [v' [vty' vsame]].
  apply IHc in H7. destruct H7 as [c' [cty' csame]].
  exists (CAnnot (Op o v' v0 c') (CTy A Σ eqs)). constructor.
  + eapply SynthCAnnot. eapply CheckOp. exact H5.
    apply CheckVBySynth. assumption. eapply CheckCBySynth. exact cty'. auto.
  + simpl. f_equal; assumption.
- inv orig. rename v into f. rename v0 into x.
  apply IHc1 in H6. destruct H6 as [c1' [c1ty' c1same]].
  apply IHc2 in H7. destruct H7 as [c2' [c2ty' c2same]].
  exists (LetRec f x (TyFun A C0) c1' c2'). constructor.
  + apply SynthLetRec. eapply CheckCBySynth. exact c1ty'. auto. assumption.
  + simpl. f_equal; assumption.
- inv orig.
- inv orig.
  apply vLemma in H2. destruct H2 as [v' [vty' vsame]].
  apply IHc in H4. destruct H4 as [c' [cty' csame]].
  exists (Handle v' c'). constructor.
  + eapply SynthHandle. exact vty'. eapply CheckCBySynth. exact cty'. auto.
  + simpl. f_equal; assumption.
- inv orig.
  apply IHc in H3. destruct H3 as [c' [cty' csame]].
  exists (CAnnot c' C). constructor.
  + apply SynthCAnnot. eapply CheckCBySynth. exact cty'. auto.
  + simpl. auto.
}{
clear hLemma.
revert Γ Σ D. induction h; intros Γ Σ D orig.
- inv orig. exists CasesØ. constructor. apply CheckCasesØ. reflexivity.
- inv orig. rename v into x. rename v0 into k.
  apply IHh in H8. destruct H8 as [h' [hty' hsame]].
  apply cLemma in H9. destruct H9 as [c' [cty' csame]].
  exists (CasesU h' o x k c'). constructor.
  + apply CheckCasesU.
    * assert (forall h h',
        h_remove_annot h = h_remove_annot h' ->
        find_op_case h o = None -> find_op_case h' o = None ).
      intros H. induction H; intros H' eq nocase; destruct H'.
      ++ assumption.
      ++ simpl in eq. discriminate.
      ++ simpl in eq. discriminate.
      ++ simpl in eq. injection eq. intros. subst.
         simpl in *. destruct (o==o1). discriminate.
         apply IHhcases; assumption.
      ++ eapply H. exact hsame. assumption.
    * assumption.
    * eapply CheckCBySynth. exact cty'. auto.
  + simpl. f_equal; assumption.
}
Qed.

