Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas wellfounded_lemmas.

Ltac inv H := inversion H; clear H; subst.


Fixpoint v_insert_typesafe v Γ A A_ins i {struct v} :
  has_vtype Γ v A -> wf_vtype A_ins ->
  has_vtype (ctx_insert_var Γ A_ins i) (Sub.v_shift v 1 i) A
with c_insert_typesafe c Γ C A_ins i {struct c} :
  has_ctype Γ c C -> wf_vtype A_ins ->
  has_ctype (ctx_insert_var Γ A_ins i) (Sub.c_shift c 1 i) C
with h_insert_typesafe h Γ Σ D A_ins i {struct h} :
  has_htype Γ h Σ D -> wf_vtype A_ins ->
  has_htype (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D.
Proof.
{
intros orig wfins. apply TypeV.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply ctx_insert_wf. inv orig. assumption. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
inv orig. destruct v.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. destruct (i <=? num) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeUnit.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeInt.
+ specialize (v_insert_typesafe v) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeInl. apply IHv; assumption.
+ specialize (v_insert_typesafe v) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeInr. apply IHv; assumption.
+ specialize (v_insert_typesafe v1) as IHv1.
  specialize (v_insert_typesafe v2) as IHv2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypePair. 
  - apply IHv1; assumption.
  - apply IHv2; assumption.
+ specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeFun. rewrite ctx_insert_extend.
  apply IHc; assumption.
+ specialize (h_insert_typesafe h) as IHh.
  specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeHandler. rewrite ctx_insert_extend. 
  - apply IHc; assumption. 
  - apply IHh; assumption.
}{
intros orig wfins. apply TypeC.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply ctx_insert_wf. inv orig. assumption. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
inv orig. destruct c.
+ specialize (v_insert_typesafe v) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. apply TypeRet. apply IHv; assumption.
+ specialize (v_insert_typesafe v) as IHv.
  specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1; simpl. eapply TypeΠMatch.
  apply IHv. exact H7. assumption.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend.
  assert (i+1+1=i+2) by omega. rewrite H1. apply IHc; assumption.
+ specialize (v_insert_typesafe v) as IHv.
  specialize (c_insert_typesafe c1) as IHc1.
  specialize (c_insert_typesafe c2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeΣMatch.
  - apply IHv. exact H9. assumption.
  - rewrite ctx_insert_extend. apply IHc1; assumption. 
  - rewrite ctx_insert_extend. apply IHc2; assumption. 
+ specialize (v_insert_typesafe v) as IHv.
  specialize (v_insert_typesafe v0) as IHv0.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeApp.
  - apply IHv. exact H5. assumption.
  - apply IHv0; assumption.
+ specialize (v_insert_typesafe v) as IHv.
  specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeOp. exact H8.
  - apply IHv; assumption.
  - rewrite ctx_insert_extend. apply IHc; assumption.
+ specialize (c_insert_typesafe c1) as IHc1.
  specialize (c_insert_typesafe c2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeLetRec.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. apply IHc1. exact H8. assumption.
  - rewrite ctx_insert_extend.  apply IHc2; assumption.
+ specialize (c_insert_typesafe c1) as IHc1.
  specialize (c_insert_typesafe c2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeDoBind.
  - apply IHc1. exact H7. assumption.
  - rewrite ctx_insert_extend. apply IHc2; assumption.
+ specialize (v_insert_typesafe v) as IHv.
  specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H1. simpl. eapply TypeHandle.
  - apply IHv. exact H5. assumption.
  - apply IHc; assumption.
}{
intros orig wfins. apply TypeH.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply ctx_insert_wf. inv orig. assumption. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
inv orig. destruct h.
+ inv H2. simpl. clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply TypeCasesØ.
+ specialize (h_insert_typesafe h) as IHh.
  specialize (c_insert_typesafe c) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv H2. simpl. apply TypeCasesU.
  - assert (forall h,
      find_op_case h o = None ->
      find_op_case (Sub.h_shift h 1 i) o = None).
    * intros h' orig. induction h'; auto.
      simpl in *. destruct (o==o0). discriminate.
      apply IHh'. assumption.
    * apply H2. assumption.
  - apply IHh; assumption.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H2. apply IHc; assumption.
}
Qed.


Fixpoint v_shift_typesafe v (Γ:ctx) A0 A {struct v} :
  has_vtype Γ v A -> wf_vtype A0 ->
  has_vtype (CtxU Γ A0) (Sub.v_shift v 1 0) A

with c_shift_typesafe c (Γ:ctx) A0 C {struct c} :
  has_ctype Γ c C -> wf_vtype A0 ->
  has_ctype (CtxU Γ A0) (Sub.c_shift c 1 0) C

with h_shift_typesafe h (Γ:ctx) A0 Σ D {struct h} :
  has_htype Γ h Σ D -> wf_vtype A0 ->
  has_htype (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D.

Proof.
all: intro orig;
assert (ctx_insert_var Γ A0 0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H.
apply v_insert_typesafe. assumption.
apply c_insert_typesafe. assumption.
apply h_insert_typesafe. assumption.
Qed.


Fixpoint v_negshift_typesafe v (Γ:ctx) A i {struct v} :
  has_vtype Γ v A -> v_no_var_j v i ->
  has_vtype (ctx_remove_var Γ i) (Sub.v_negshift v 1 i) A

with c_negshift_typesafe c (Γ:ctx) C i {struct c} :
  has_ctype Γ c C -> c_no_var_j c i ->
  has_ctype (ctx_remove_var Γ i) (Sub.c_negshift c 1 i) C

with h_negshift_typesafe h (Γ:ctx) Σ D i {struct h} :
  has_htype Γ h Σ D -> h_no_var_j h i ->
  has_htype (ctx_remove_var Γ i) (Sub.h_negshift h 1 i) Σ D.
Proof.
{
intros orig no_var. simpl in no_var. apply TypeV; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct v.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct v as (name, num). simpl. inv H1.
  assert (
    (if i <=? num then (name, num - 1) else (name, num))
      = (name, if i <=? num then num - 1 else num) ) 
    as same by (destruct (i<=?num); reflexivity).
  rewrite same. destruct (i <=? num) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct num. destruct no_var. omega.
      simpl. assert (num-0=num) by omega. rewrite H1. assumption.
    * destruct cmp.
      ++ destruct no_var. reflexivity.
      ++ omega.
  - apply TypeVar. rewrite <-get_ctx_remove_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeUnit.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeInt.
+ specialize (v_negshift_typesafe v) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeInl. apply IHv.
  assumption. assumption.
+ specialize (v_negshift_typesafe v) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeInr. apply IHv.
  assumption. assumption.
+ specialize (v_negshift_typesafe v1) as IHv1.
  specialize (v_negshift_typesafe v2) as IHv2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. apply TypePair. 
  apply IHv1; assumption. apply IHv2; assumption.
+ specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeFun. rewrite ctx_remove_extend.
  apply IHc; assumption.
+ specialize (h_negshift_typesafe h) as IHh.
  specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var.
  apply TypeHandler. rewrite ctx_remove_extend.
  apply IHc; assumption. apply IHh; assumption.
}{
intros orig no_var. simpl in no_var. apply TypeC; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct c.
+ specialize (v_negshift_typesafe v) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. apply TypeRet. apply IHv; assumption.
+ specialize (v_negshift_typesafe v) as IHv.
  specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeΠMatch.
  - apply IHv. exact H7. assumption.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) as SSi by omega. rewrite SSi. apply IHc; assumption.
+ specialize (v_negshift_typesafe v) as IHv.
  specialize (c_negshift_typesafe c1) as IHc1.
  specialize (c_negshift_typesafe c2) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. destruct H0. destruct H2.
  eapply TypeΣMatch.
  - apply IHv. exact H9. assumption.
  - rewrite ctx_remove_extend. apply IHc1; assumption. 
  - rewrite ctx_remove_extend. apply IHc2; assumption. 
+ specialize (v_negshift_typesafe v) as IHv.
  specialize (v_negshift_typesafe v0) as IHv0.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeApp.
  - apply IHv. exact H5. assumption.
  - apply IHv0; assumption.
+ specialize (v_negshift_typesafe v) as IHv.
  specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeOp. exact H8.
  - apply IHv; assumption.
  - rewrite ctx_remove_extend. apply IHc; assumption.
+ specialize (c_negshift_typesafe c1) as IHc1.
  specialize (c_negshift_typesafe c2) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeLetRec.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) as SSi by omega. rewrite SSi.
    apply IHc1. exact H8. assumption.
  - rewrite ctx_remove_extend.  apply IHc2; assumption.
+ specialize (c_negshift_typesafe c1) as IHc1.
  specialize (c_negshift_typesafe c2) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeDoBind.
  - apply IHc1. exact H7. assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ specialize (v_negshift_typesafe v) as IHv.
  specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H1. destruct no_var. eapply TypeHandle.
  - apply IHv. exact H5. assumption.
  - apply IHc; assumption.
}{
intros orig no_var; simpl; apply TypeH; inv orig.
{ apply ctx_remove_wf. assumption. }
assumption. assumption.
destruct h.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. inv H2. apply TypeCasesØ.
+ specialize (h_negshift_typesafe h) as IHh.
  specialize (c_negshift_typesafe c) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl in no_var. destruct no_var. simpl. inv H2. apply TypeCasesU.
  - assert (forall h,
      find_op_case h o = None ->
      find_op_case (Sub.h_negshift h 1 i) o = None) as no_find.
    * intros h' orig. induction h'; auto.
      simpl in *. destruct (o==o0). discriminate.
      apply IHh'; assumption.
    * apply no_find. assumption.
  - apply IHh; assumption. 
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) as SSi by omega. rewrite SSi. apply IHc; assumption.
}
Qed.


Fixpoint v_subs_typesafe v Γ A i v_s A_s {struct v}:
  has_vtype Γ v A -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe c Γ C i v_s A_s {struct c}:
  has_ctype Γ c C -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe h Γ Σ D i v_s A_s {struct h}:
  has_htype Γ h Σ D -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
all: assert (forall i, i+1=S i) as Si by (intro; omega).
all: assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
{
intros orig gets vs_types. apply TypeV; inv orig.
assumption. assumption. destruct v.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. destruct v as (name, num). simpl. inv H1.
  destruct (num =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H6 in gets.
    injection gets. intro. subst. inv vs_types. assumption.
  - apply TypeVar. assumption.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeUnit.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeInt.
+ specialize (v_subs_typesafe v) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeInl. eapply IHv.
  assumption. exact gets. assumption.
+ specialize (v_subs_typesafe v) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeInr. eapply IHv.
  assumption. exact gets. assumption.
+ specialize (v_subs_typesafe v1) as IHv1.
  specialize (v_subs_typesafe v2) as IHv2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypePair.
  eapply IHv1. assumption. exact gets. assumption.
  eapply IHv2. assumption. exact gets. assumption.
+ specialize (c_subs_typesafe c) as IHc.
  specialize (v_subs_typesafe v_s) as IHvs.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeFun. eapply IHc.
  assumption. rewrite Si. exact gets. apply v_shift_typesafe.
  assumption. inv H0. assumption.
+ specialize (h_subs_typesafe h) as IHh.
  specialize (c_subs_typesafe c) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeHandler.
  - eapply IHc. assumption. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption. inv H0. inv H3. assumption.
  - eapply IHh. assumption. exact gets. assumption.
}{
intros orig gets vs_types. apply TypeC; inv orig.
assumption. assumption. destruct c.
+ specialize (v_subs_typesafe v) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. apply TypeRet. eapply IHv.
  assumption. exact gets. assumption.
+ specialize (v_subs_typesafe v) as IHv.
  specialize (c_subs_typesafe c) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeΠMatch.
  - eapply IHv. exact H7. exact gets. assumption.
  - eapply IHc. assumption. rewrite SSi. exact gets. 
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H7; inv H2; assumption.
+ specialize (v_subs_typesafe v) as IHv.
  specialize (c_subs_typesafe c1) as IHc1.
  specialize (c_subs_typesafe c2) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeΣMatch.
  - eapply IHv. exact H9. exact gets. assumption.
  - eapply IHc1. assumption. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H9. inv H2. assumption. 
  - eapply IHc2. assumption. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H9. inv H2. assumption. 
+ specialize (v_subs_typesafe v) as IHv.
  specialize (v_subs_typesafe v0) as IHv0.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeApp.
  - eapply IHv. exact H5. exact gets. assumption.
  - eapply IHv0. assumption. exact gets. assumption.
+ specialize (v_subs_typesafe v) as IHv.
  specialize (c_subs_typesafe c) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeOp. exact H8.
  - eapply IHv. assumption. exact gets. assumption.
  - eapply IHc. assumption. rewrite Si. exact gets. 
    apply v_shift_typesafe. assumption.
    inv H10. inv H1. assumption.
+ specialize (c_subs_typesafe c1) as IHc1.
  specialize (c_subs_typesafe c2) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeLetRec.
  - rewrite SSi. eapply IHc1. exact H8. exact gets.
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H8; inv H1. 2: assumption. inv H6. assumption. 
  - eapply IHc2. assumption. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H9. inv H1. assumption.
+ specialize (c_subs_typesafe c1) as IHc1.
  specialize (c_subs_typesafe c2) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeDoBind.
  - eapply IHc1. exact H7. exact gets. assumption.
  - eapply IHc2. assumption. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H7. inv H2. assumption.
+ specialize (v_subs_typesafe v) as IHv.
  specialize (c_subs_typesafe c) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H1. eapply TypeHandle.
  - eapply IHv. exact H5. exact gets. assumption.
  - eapply IHc. assumption. exact gets. assumption.
}{
intros orig gets vs_types; simpl; apply TypeH; inv orig.
assumption. assumption. assumption.
destruct h.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  inv H2. apply TypeCasesØ.
+ specialize (h_subs_typesafe h) as IHh.
  specialize (c_subs_typesafe c) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. inv H2. apply TypeCasesU.
  - assert (forall h,
      find_op_case h o = None ->
      find_op_case (Sub.h_sub h (i, v_s)) o = None) as no_find.
    * intros h' orig. induction h'; auto.
      simpl in *. destruct (o==o0). discriminate.
      apply IHh'. assumption.
    * apply no_find. assumption.
  - eapply IHh. exact H12. exact gets. assumption.
  - rewrite SSi. eapply IHc. assumption. exact gets.
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. inv H12. apply WfFun; assumption.
}
Qed.


Lemma h_has_case Γ h Σ D op A_op B_op:
  has_htype Γ h Σ D ->
  get_op_type Σ op = Some (A_op, B_op) ->
  exists x k c_op, find_op_case h op = Some (x, k, c_op).
Proof.
revert Γ Σ. induction h; intros Γ Σ typed gets;
inv typed; inv H1; inv H2.
+ simpl in gets. discriminate.
+ simpl in *. destruct (op==o).
  - injection gets. intros. subst.
    exists v. exists v0. exists c. reflexivity.
  - apply IHh in H14; assumption.
Qed.
