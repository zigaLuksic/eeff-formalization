Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas subtyping subtyping_lemmas wellfounded_lemmas.

Ltac inv H := inversion H; clear H; subst.


Fixpoint v_insert_typesafe 
  Γ v A (orig : has_vtype Γ v A) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_vtype (ctx_insert_var Γ A_ins i) (Sub.v_shift v 1 i) A

with c_insert_typesafe 
  Γ c C (orig : has_ctype Γ c C) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_ctype (ctx_insert_var Γ A_ins i) (Sub.c_shift c 1 i) C

with h_insert_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_htype (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D.
Proof.
{
intros wfins. apply TypeV.
{ apply ctx_insert_wf. inv orig. assumption. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeUnit.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeInt.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. destruct (i <=? num) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv1.
  specialize (v_insert_typesafe _ _ _ H2) as IHv2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypePair. 
  - apply IHv1; assumption.
  - apply IHv2; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeInl. apply IHv; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeInr. apply IHv; assumption.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeFun. rewrite ctx_insert_extend.
  apply IHc; assumption.
+ specialize (h_insert_typesafe _ _ _ _ H2) as IHh.
  specialize (c_insert_typesafe _ _ _ H1) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. 
  - apply IHc; assumption. 
  - apply IHh; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  eapply TypeVSubtype. apply IHv. all: assumption.
}{
intros wfins. apply TypeC.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply ctx_insert_wf. inv orig. assumption. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
inv orig. destruct H1.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeRet. apply IHv; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  eapply TypeΠMatch.
  apply IHv. assumption.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend.
  assert (i+1+1=i+2) by omega. rewrite H3. apply IHc; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc1.
  specialize (c_insert_typesafe _ _ _ H3) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeΣMatch.
  - apply IHv. assumption.
  - rewrite ctx_insert_extend. apply IHc1; assumption. 
  - rewrite ctx_insert_extend. apply IHc2; assumption. 
+ specialize (c_insert_typesafe _ _ _ H1) as IHc1.
  specialize (c_insert_typesafe _ _ _ H2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeDoBind.
  - apply IHc1. assumption.
  - rewrite ctx_insert_extend. apply IHc2; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (v_insert_typesafe _ _ _ H2) as IHv0.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeApp.
  - apply IHv. assumption.
  - apply IHv0; assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeHandle.
  - apply IHv. assumption.
  - apply IHc; assumption.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc1.
  specialize (c_insert_typesafe _ _ _ H2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeLetRec.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H3. apply IHc1. assumption.
  - rewrite ctx_insert_extend.  apply IHc2; assumption.
+ specialize (v_insert_typesafe _ _ _ H2) as IHv.
  specialize (c_insert_typesafe _ _ _ H3) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. eapply TypeOp.
  - exact H1.
  - apply IHv; assumption.
  - rewrite ctx_insert_extend. apply IHc; assumption.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  eapply TypeCSubtype. apply IHc. all: assumption.
}{
intros wfins. apply TypeH.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply ctx_insert_wf. inv orig. assumption. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  inv orig. assumption. }
inv orig. destruct H2.
+ simpl. clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  apply TypeCasesØ.
+ specialize (h_insert_typesafe _ _ _ _ H3) as IHh.
  specialize (c_insert_typesafe _ _ _ H4) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  simpl. apply TypeCasesU.
  - assert (forall h op,
      find_op_case h op = None ->
      find_op_case (Sub.h_shift h 1 i) op = None).
    * intros h' op' orig. induction h'; auto.
      simpl in *. destruct (op'==o). discriminate.
      apply IHh'. assumption.
    * apply H5. assumption.
  - apply IHh; assumption.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H5. apply IHc; assumption.
+ specialize (h_insert_typesafe _ _ _ _ H2) as IHh.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  eapply TypeHSubtype. apply IHh. all: assumption.
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


Fixpoint v_negshift_typesafe 
  Γ v A (orig : has_vtype Γ v A) i {struct orig} :
  v_no_var_j v i ->
  has_vtype (ctx_remove_var Γ i) (Sub.v_negshift v 1 i) A

with c_negshift_typesafe 
  Γ c C (orig : has_ctype Γ c C) i {struct orig} :
  c_no_var_j c i ->
  has_ctype (ctx_remove_var Γ i) (Sub.c_negshift c 1 i) C

with h_negshift_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) i {struct orig} :
  h_no_var_j h i ->
  has_htype (ctx_remove_var Γ i) (Sub.h_negshift h 1 i) Σ D.
Proof.
{
intros no_var. simpl in no_var. apply TypeV; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct H1.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeUnit.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeInt.
+ clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl.
  assert (
    (if i <=? num then (name, num - 1) else (name, num))
      = (name, if i <=? num then num - 1 else num) ) 
    as same by (destruct (i<=?num); reflexivity).
  rewrite same. destruct (i <=? num) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct num. destruct no_var. omega.
      simpl. assert (num-0=num) by omega. rewrite H2. assumption.
    * destruct cmp.
      ++ destruct no_var. reflexivity.
      ++ omega.
  - apply TypeVar. rewrite <-get_ctx_remove_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv1.
  specialize (v_negshift_typesafe _ _ _ H2) as IHv2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. apply TypePair. 
  apply IHv1; assumption. apply IHv2; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeInl. apply IHv. assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeInr. apply IHv. assumption.
+ specialize (c_negshift_typesafe _ _ _ H1) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeFun. rewrite ctx_remove_extend.
  apply IHc; assumption.
+ specialize (h_negshift_typesafe _ _ _ _ H2) as IHh.
  specialize (c_negshift_typesafe _ _ _ H1) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var.
  apply TypeHandler. rewrite ctx_remove_extend.
  apply IHc; assumption. apply IHh; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  eapply TypeVSubtype.
  - apply IHv. assumption.
  - assumption.
}{
intros no_var. simpl in no_var. apply TypeC; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct H1.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeRet. apply IHv; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  specialize (c_negshift_typesafe _ _ _ H2) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeΠMatch.
  - apply IHv. assumption.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) as SSi by omega. rewrite SSi. apply IHc; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  specialize (c_negshift_typesafe _ _ _ H2) as IHc1.
  specialize (c_negshift_typesafe _ _ _ H3) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. destruct H5.
  eapply TypeΣMatch.
  - apply IHv. assumption.
  - rewrite ctx_remove_extend. apply IHc1; assumption. 
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ specialize (c_negshift_typesafe _ _ _ H1) as IHc1.
  specialize (c_negshift_typesafe _ _ _ H2) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeDoBind.
  - apply IHc1. assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  specialize (v_negshift_typesafe _ _ _ H2) as IHv0.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeApp.
  - apply IHv. assumption.
  - apply IHv0; assumption.
+ specialize (v_negshift_typesafe _ _ _ H1) as IHv.
  specialize (c_negshift_typesafe _ _ _ H2) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeHandle.
  - apply IHv. assumption.
  - apply IHc; assumption.
+ specialize (c_negshift_typesafe _ _ _ H1) as IHc1.
  specialize (c_negshift_typesafe _ _ _ H2) as IHc2.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeLetRec.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) as SSi by omega. rewrite SSi.
    apply IHc1. assumption.
  - rewrite ctx_remove_extend.  apply IHc2; assumption.
+ specialize (v_negshift_typesafe _ _ _ H2) as IHv.
  specialize (c_negshift_typesafe _ _ _ H3) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. destruct no_var. eapply TypeOp. exact H1.
  - apply IHv; assumption.
  - rewrite ctx_remove_extend. apply IHc; assumption.
+ specialize (c_negshift_typesafe _ _ _ H1) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  eapply TypeCSubtype.
  - apply IHc. assumption.
  - assumption.
}{
intros no_var; simpl; apply TypeH; inv orig.
apply ctx_remove_wf. assumption. assumption. assumption.
destruct H2.
+ simpl. clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  apply TypeCasesØ.
+ specialize (h_negshift_typesafe _ _ _ _ H3) as IHh.
  specialize (c_negshift_typesafe _ _ _ H4) as IHc.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeCasesU.
  - assert (forall h op,
      find_op_case h op = None ->
      find_op_case (Sub.h_negshift h 1 i) op = None).
    * intros h' op' orig. induction h'; auto.
      simpl in *. destruct (op'==o). discriminate.
      apply IHh'. assumption.
    * apply H5. assumption.
  - apply IHh. destruct no_var. assumption.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H5.
    apply IHc. destruct no_var. assumption.
+ specialize (h_negshift_typesafe _ _ _ _ H2) as IHh.
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  eapply TypeHSubtype. apply IHh. all: assumption.
}
Qed.

Fixpoint v_subs_typesafe 
  Γ v A (orig: has_vtype Γ v A) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe
  Γ c C (orig: has_ctype Γ c C) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe
  Γ h Σ D (orig: has_htype Γ h Σ D) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
all: assert (forall i, i+1=S i) as Si by (intro; omega).
all: assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
{
intros gets vs_types. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeUnit.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeInt.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. destruct (num =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv vs_types. assumption.
  - apply TypeVar. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv1.
  specialize (v_subs_typesafe _ _ _ H2) as IHv2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypePair.
  eapply IHv1. exact gets. assumption.
  eapply IHv2. exact gets. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeInl. eapply IHv. exact gets. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeInr. eapply IHv. exact gets. assumption.
+ specialize (c_subs_typesafe _ _ _ H1) as IHc.
  specialize (v_subs_typesafe _ _ _ vs_types) as IHvs.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeFun. eapply IHc.
  rewrite Si. exact gets.
  apply v_shift_typesafe. assumption. inv H0. assumption.
+ specialize (h_subs_typesafe _ _ _ _ H2) as IHh.
  specialize (c_subs_typesafe _ _ _ H1) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeHandler.
  - eapply IHc. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption. inv H0. inv H5. assumption.
  - eapply IHh. exact gets. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  eapply TypeVSubtype.
  - eapply IHv. exact gets. assumption.
  - assumption. 
}{
intros gets vs_types. apply TypeC; inv orig.
assumption. assumption. destruct H1.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeRet. eapply IHv. exact gets. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeΠMatch.
  - eapply IHv. exact gets. assumption.
  - eapply IHc. rewrite SSi. exact gets. 
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc1.
  specialize (c_subs_typesafe _ _ _ H3) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeΣMatch.
  - eapply IHv. exact gets. assumption.
  - eapply IHc1. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H1. inv H5. assumption. 
  - eapply IHc2. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H1. inv H5. assumption. 
+ specialize (c_subs_typesafe _ _ _ H1) as IHc1.
  specialize (c_subs_typesafe _ _ _ H2) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeDoBind.
  - eapply IHc1. exact gets. assumption.
  - eapply IHc2. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H1. inv H4. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (v_subs_typesafe _ _ _ H2) as IHv0.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeApp.
  - eapply IHv. exact gets. assumption.
  - eapply IHv0. exact gets. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeHandle.
  - eapply IHv. exact gets. assumption.
  - eapply IHc. exact gets. assumption.
+ specialize (c_subs_typesafe _ _ _ H1) as IHc1.
  specialize (c_subs_typesafe _ _ _ H2) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeLetRec.
  - rewrite SSi. eapply IHc1. exact gets.
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H1. inv H3. assumption.
+ specialize (v_subs_typesafe _ _ _ H2) as IHv.
  specialize (c_subs_typesafe _ _ _ H3) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeOp. exact H1.
  - eapply IHv. exact gets. assumption.
  - eapply IHc. rewrite Si. exact gets. 
    apply v_shift_typesafe. assumption.
    inv H3. inv H4. assumption.
+ specialize (c_subs_typesafe _ _ _ H1) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  eapply TypeCSubtype.
  - eapply IHc. exact gets. assumption.
  - assumption.
}{
intros gets vs_types; simpl; apply TypeH; inv orig.
assumption. assumption. assumption.
destruct H2.
+ clear v_subs_typesafe c_subs_typesafe h_subs_typesafe. apply TypeCasesØ.
+ specialize (h_subs_typesafe _ _ _ _ H3) as IHh.
  specialize (c_subs_typesafe _ _ _ H4) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeCasesU.
  - assert (forall h o,
      find_op_case h o = None ->
      find_op_case (Sub.h_sub h (i, v_s)) o = None) as no_find.
    * intros h' o orig. induction h'; auto.
      simpl in *. destruct (o==o0). discriminate.
      apply IHh'. assumption.
    * apply no_find. assumption.
  - eapply IHh. exact gets. assumption.
  - rewrite SSi. eapply IHc. exact gets.
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfFun; assumption.
+ specialize (h_subs_typesafe _ _ _ _ H2) as IHh.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  eapply TypeHSubtype. eapply IHh. exact gets. all: assumption.
}
Qed.

(* 
Lemma h_has_case Γ h Σ D op A_op B_op:
  has_htype Γ h Σ D ->
  get_op_type Σ op = Some (A_op, B_op) ->
  exists x k c_op, find_op_case h op = Some (x, k, c_op).
Proof.
revert Γ Σ. induction h; intros Γ Σ typed gets;
inv typed; inv H1; inv H2.
+ simpl in gets. discriminate.
+ eapply sig_subtype_gets_Some in gets. 2: exact H6.
  destruct gets as [A' [B' [gets']]]. rewrite gets in 
+ simpl in *. destruct (op==o).
  - injection gets. intros. subst.
    exists v. exists v0. exists c. reflexivity.
  - apply IHh in H14; assumption.
Qed. *)
