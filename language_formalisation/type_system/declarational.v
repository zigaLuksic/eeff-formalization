Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Import syntax bidirectional.

Inductive has_vtype : ctx -> val -> vtype -> Type :=
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
with has_ctype : ctx -> comp -> ctype -> Type :=
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
with has_htype : ctx -> hcases -> sig -> ctype -> Type :=
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
| CAnnot c' C => CAnnot (c_remove_annot c') C
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
+ apply TypeCAnnot. auto.
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
(* 
Inductive VChecks : ctx -> val -> vtype -> Prop :=
| VCheck Γ v' A : vcheck Γ v' A -> VChecks Γ v' A.
Inductive CChecks : ctx -> comp -> ctype -> Prop :=
| CCheck Γ c' C : ccheck Γ c' C -> CChecks Γ c' C.
Inductive HChecks : ctx -> hcases -> sig -> ctype -> Prop :=
| HCheck Γ h' Σ D : hcheck Γ h' Σ D -> HChecks Γ h' Σ D.

Fixpoint has_vtype_vchecks_with_annot Γ v A {struct v}:
  has_vtype Γ v A -> exists v',
    (VChecks Γ v' A) /\ v_remove_annot v = v_remove_annot v'
with has_ctype_cchecks_with_annot Γ c C {struct c}:
  has_ctype Γ c C -> exists c',
    (CChecks Γ c' C) /\ c_remove_annot c = c_remove_annot c'
with has_htype_hchecks_with_annot Γ h Σ D {struct h}:
  has_htype Γ h Σ D -> exists h',
    (HChecks Γ h' Σ D) /\ h_remove_annot h = h_remove_annot h'.
Proof.
all:
rename has_vtype_vchecks_with_annot into vLemma;
rename has_ctype_cchecks_with_annot into cLemma;
rename has_htype_hchecks_with_annot into hLemma.
{
clear vLemma.
revert Γ A. induction v; intros Γ A orig; inv orig.
- exists (Var v). constructor.
  + constructor. apply CheckVBySynth. apply SynthVar. assumption.
  + reflexivity.
- exists Unit. constructor.
  + constructor. apply CheckVBySynth. apply SynthUnit.
  + reflexivity.
- exists (Int t). constructor.
  + constructor. apply CheckVBySynth. apply SynthInt.
  + reflexivity.
- apply IHv in H1. destruct H1 as [v' P]. destruct P.
  exists (Inl v'). constructor.
  + constructor. destruct H.
} *)