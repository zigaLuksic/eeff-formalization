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
