(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export substitution_lemmas subtyping subtyping_lemmas wf_lemmas.

Ltac inv H := inversion H; clear H; subst.


Fixpoint v_shift_too_high Γ v A n cut :
  has_vtype Γ v A -> cut >= ctx_len Γ -> Sub.v_shift v n cut = v
with c_shift_too_high Γ c C n cut :
  has_ctype Γ c C -> cut >= ctx_len Γ -> Sub.c_shift c n cut = c
with h_shift_too_high Γ h Σ D n cut :
  has_htype Γ h Σ D -> cut >= ctx_len Γ -> Sub.h_shift h n cut = h.
Proof.
{
intros types high. destruct v; simpl.
+ destruct v. eapply shape_var in types. destruct types as [A'[gets]].
  apply ctx_len_gets in gets. destruct (cut <=? v0) eqn:cmp. 
  apply leb_complete in cmp. omega. reflexivity.
+ reflexivity.
+ reflexivity.
+ eapply shape_inl_full in types. 2: reflexivity. destruct types as [A'[B']].
  f_equal. eapply v_shift_too_high. 2: eauto. destruct H. eauto.
+ eapply shape_inr_full in types. 2: reflexivity. destruct types as [A'[B']].
  f_equal. eapply v_shift_too_high. 2: eauto. destruct H. eauto.
+ eapply shape_pair_full in types. 2: reflexivity. destruct types as [A'[B']].
  destruct H as [s[ty1]]. f_equal; eapply v_shift_too_high; eauto.
+ eapply shape_fun_full in types. 2: reflexivity. destruct types as [A'[C']].
  f_equal. eapply c_shift_too_high. destruct H. eauto. simpl. omega.
+ eapply shape_handler_full in types. 2: reflexivity.
  destruct types as [A'[Σ[E[D[Σ'[D'[_[cty[hty]]]]]]]]].
  f_equal. eapply c_shift_too_high. eauto. simpl. omega.
  eapply h_shift_too_high. eauto. omega.
}{
intros types high. destruct c; simpl.
+ destruct C as (A, Σ, E). eapply shape_ret_full in types; eauto.
  f_equal. eapply v_shift_too_high; eauto.
+ eapply shape_absurd in types. f_equal. eapply v_shift_too_high; eauto.
+ eapply shape_prodmatch in types. destruct types as [A[B[vty]]].
  f_equal. eapply v_shift_too_high; eauto. eapply c_shift_too_high. eauto.
  simpl. omega.
+ eapply shape_summatch in types. destruct types as [A[B[vty[c1ty]]]].
  f_equal. eapply v_shift_too_high; eauto. all: eapply c_shift_too_high; eauto;
  simpl; omega.
+ eapply shape_app_full in types. 2: reflexivity. destruct types as [A[vty]].
  f_equal; eapply v_shift_too_high; eauto.
+ destruct C as (A, Σ, E). eapply shape_op in types.
  destruct types as [Aop[Bop[gets[arg]]]]. f_equal.
  eapply v_shift_too_high; eauto. eapply c_shift_too_high; eauto. simpl. omega.
+ eapply shape_letrec in types. destruct types as [A'[C'[cty]]].
  f_equal; eapply c_shift_too_high; eauto; simpl; omega.
+ destruct C as (A,Σ,E). eapply shape_dobind in types.
  destruct types as [A'[cty]]. f_equal; eapply c_shift_too_high; eauto.
  simpl. omega.
+ eapply shape_handle in types. destruct types as [C'[vty]].
  f_equal. eapply v_shift_too_high; eauto. eapply c_shift_too_high; eauto.
}{
intros types high. destruct h; simpl. reflexivity.
inv types. inv H2. f_equal.
+ eapply h_shift_too_high; eauto.
+ eapply c_shift_too_high. eauto. simpl. omega.
}
Qed.


Lemma handle_tmpl_shift Γ Z h i T Σ:
  wf_tmpl Γ Z T Σ ->
  handle_tmpl (Sub.h_shift (Sub.h_shift h 1 i) (ctx_len Γ + tctx_len Z) 0) T
  = Sub.c_shift 
      (handle_tmpl (Sub.h_shift h (ctx_len Γ + tctx_len Z) 0) T)
      1 (i + (ctx_len Γ + tctx_len Z)).
Proof.
revert Γ i. induction T; intros Γ i wf; simpl; inv wf.
+ apply tctx_len_gets in H5 as zlen.
  destruct (i + (ctx_len Γ + tctx_len Z) <=? num) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. apply eq_sym. eapply v_shift_too_high. eauto. omega.
+ f_equal. apply eq_sym. eapply v_shift_too_high. eauto. omega.
+ f_equal.
  - apply eq_sym. eapply v_shift_too_high. eauto. omega.
  - eapply (IHT _ i) in H7. simpl in H7. 
    assert (S(S(ctx_len Γ+tctx_len Z))=ctx_len Γ+tctx_len Z+2) by omega.
    rewrite H in H7. do 2 rewrite h_shift_shift in *. rewrite H7.
    f_equal. omega.
+ f_equal.
  - apply eq_sym. eapply v_shift_too_high. eauto. omega.
  - eapply (IHT1 _ i) in H8. simpl in H8.
    assert (S(ctx_len Γ+tctx_len Z)=ctx_len Γ+tctx_len Z+1) by omega.
    rewrite H in H8. do 2 rewrite h_shift_shift in *. rewrite H8.
    f_equal. omega.
  - eapply (IHT2 _ i) in H9. simpl in H9.
    assert (S(ctx_len Γ+tctx_len Z)=ctx_len Γ+tctx_len Z+1) by omega.
    rewrite H in H9. do 2 rewrite h_shift_shift in *. rewrite H9.
    f_equal. omega.
+ destruct (find_op_case h o) eqn:find.
  - remember (ctx_len Γ + tctx_len Z) as len.
    destruct p as (p', cop). destruct p' as (x, k).
    assert (find_op_case (Sub.h_shift (Sub.h_shift h 1 i) len 0) o 
      = Some (x, k, Sub.c_shift (Sub.c_shift cop 1 (i + 2)) len 2) ).
    { eapply (h_shift_find_op_Some _ _ 1 i) in find.
      eapply (h_shift_find_op_Some _ _ len 0) in find.
      rewrite find. f_equal. }
    assert (find_op_case (Sub.h_shift h len 0) o 
      = Some (x, k, Sub.c_shift cop len 2) ).
    { eapply (h_shift_find_op_Some _ _ len 0) in find.
      rewrite find. f_equal. }
    rewrite H. rewrite H0. simpl. rewrite Heqlen.
    rewrite IHT.
    * unfold c_sub2_out. unfold c_sub_out.
      rewrite c_shift_sub. f_equal.
      { rewrite c_shift_sub. f_equal. rewrite c_shift_comm_aux.
        f_equal. omega. omega. 
        erewrite (v_shift_too_high _ (Sub.v_shift v 1 0)). reflexivity.
        eauto. admit. admit. omega. }
      { simpl. f_equal.



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
  has_htype (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D

with respects_insert_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) A_ins i {struct orig} :
  wf_vtype A_ins ->
  respects (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D E

with veq_insert_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  veq A (ctx_insert_var Γ A_ins i) (Sub.v_shift v1 1 i) (Sub.v_shift v2 1 i)

with ceq_insert_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  ceq C (ctx_insert_var Γ A_ins i) (Sub.c_shift c1 1 i) (Sub.c_shift c2 1 i).

Proof.
{
intros wfins. apply TypeV.
{ apply ctx_insert_wf. inv orig. assumption. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeUnit.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeInt.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv1.
  specialize (v_insert_typesafe _ _ _ H2) as IHv2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypePair; auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeInl. auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeInr. auto.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (h_insert_typesafe _ _ _ _ H2) as IHh.
  specialize (c_insert_typesafe _ _ _ H1) as IHc.
  specialize (respects_insert_typesafe _ _ _ _ _ H3) as IHres.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  eapply TypeVSubtype; auto.
}{
intros wfins. apply TypeC.
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeRet. auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeAbsurd. auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe. 
  simpl. eapply TypeΠMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend.
  assert (i+1+1=i+2) by omega.  rewrite H3. auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc1.
  specialize (c_insert_typesafe _ _ _ H3) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeΣMatch. auto. all: rewrite ctx_insert_extend; auto.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc1.
  specialize (c_insert_typesafe _ _ _ H2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeDoBind. auto. rewrite ctx_insert_extend. auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (v_insert_typesafe _ _ _ H2) as IHv0.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeApp; auto.
+ specialize (v_insert_typesafe _ _ _ H1) as IHv.
  specialize (c_insert_typesafe _ _ _ H2) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeHandle; auto.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc1.
  specialize (c_insert_typesafe _ _ _ H2) as IHc2.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H3. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (v_insert_typesafe _ _ _ H2) as IHv.
  specialize (c_insert_typesafe _ _ _ H3) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. eapply TypeOp. 3: rewrite ctx_insert_extend. all: eauto.
+ specialize (c_insert_typesafe _ _ _ H1) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  eapply TypeCSubtype; auto.
}{
intros wfins. apply TypeH.
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig. assumption. }
{ inv orig. assumption. }
inv orig. destruct H2.
+ simpl. clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  apply TypeCasesØ.
+ specialize (h_insert_typesafe _ _ _ _ H3) as IHh.
  specialize (c_insert_typesafe _ _ _ H4) as IHc.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  simpl. apply TypeCasesU.
  - assert (forall h op,
      find_op_case h op = None -> find_op_case (Sub.h_shift h 1 i) op = None).
    * intros h' op' orig. induction h'; auto.
      simpl in *. destruct (op'==o). discriminate. auto.
    * auto.
  - auto.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H5. auto.
}{
intros wfins. apply Respects.
{ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv orig. assumption. }
inv orig. destruct H3.
+ clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  apply RespectEqsØ.
+ specialize (respects_insert_typesafe _ _ _ _ _ H3) as IHres.
  clear v_insert_typesafe c_insert_typesafe h_insert_typesafe.
  clear respects_insert_typesafe veq_insert_typesafe ceq_insert_typesafe.
  apply RespectEqsU. auto.
  rewrite join_ctxs_insert_var. rewrite join_ctx_tctx_insert_var.
  rewrite h_shift_shift.


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
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct n. destruct no_var. omega.
      simpl. assert (n-0=n) by omega. rewrite H2. assumption.
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
  clear v_negshift_typesafe c_negshift_typesafe h_negshift_typesafe.
  simpl. apply TypeAbsurd. apply IHv; assumption.
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
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv vs_types. assumption.
  - apply TypeVar. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv1.
  specialize (v_subs_typesafe _ _ _ H2) as IHv2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypePair.
  eapply IHv1; eauto.
  eapply IHv2; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeInl. eapply IHv; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeInr. eapply IHv; eauto.
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
  - eapply IHh; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  eapply TypeVSubtype.
  - eapply IHv; eauto.
  - assumption. 
}{
intros gets vs_types. apply TypeC; inv orig.
assumption. assumption. destruct H1.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeRet. eapply IHv; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. apply TypeAbsurd. eapply IHv; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeΠMatch.
  - eapply IHv; eauto.
  - eapply IHc. rewrite SSi. exact gets. 
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc1.
  specialize (c_subs_typesafe _ _ _ H3) as IHc2.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeΣMatch.
  - eapply IHv; eauto.
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
  - eapply IHc1; eauto.
  - eapply IHc2. rewrite Si. exact gets.
    apply v_shift_typesafe. assumption.
    inv H1. inv H4. assumption.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (v_subs_typesafe _ _ _ H2) as IHv0.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeApp.
  - eapply IHv; eauto.
  - eapply IHv0; eauto.
+ specialize (v_subs_typesafe _ _ _ H1) as IHv.
  specialize (c_subs_typesafe _ _ _ H2) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  simpl. eapply TypeHandle.
  - eapply IHv; eauto.
  - eapply IHc; eauto.
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
  - eapply IHv; eauto.
  - eapply IHc. rewrite Si. exact gets. 
    apply v_shift_typesafe. assumption.
    inv H3. inv H4. assumption.
+ specialize (c_subs_typesafe _ _ _ H1) as IHc.
  clear v_subs_typesafe c_subs_typesafe h_subs_typesafe.
  eapply TypeCSubtype.
  - eapply IHc; eauto.
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
  - eapply IHh; eauto.
  - rewrite SSi. eapply IHc. exact gets.
    rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfTyFun; assumption.
}
Qed.
