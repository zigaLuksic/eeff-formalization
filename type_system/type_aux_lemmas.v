Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export syntax_lemmas substitution_lemmas subtyping_lemmas.

Ltac inv H := inversion H; clear H; subst.

(* ==================== Typing and No/Under Var ==================== *)

Lemma has_vtype_is_under_ctx Γ v A:
  has_vtype Γ v A -> v_under_var v (ctx_len Γ)
with has_ctype_is_under_ctx Γ c C:
  has_ctype Γ c C -> c_under_var c (ctx_len Γ)
with has_htype_is_under_ctx Γ h Σ D:
  has_htype Γ h Σ D -> h_under_var h (ctx_len Γ).
Proof.
{
intro types. destruct types. destruct H1; simpl; auto.
all: try constructor; eauto. eapply ctx_len_gets. eauto.
all: assert (S (ctx_len Γ) = ctx_len (CtxU Γ A)) as cA by (simpl; reflexivity).
all: rewrite cA; eauto.
}{
intro types. destruct types. destruct H1; simpl.
all: try constructor; try constructor; try eauto.
all: assert (forall A Γ, S(ctx_len Γ) = ctx_len (CtxU Γ A)) as ext by auto.
all: erewrite ext; eauto; erewrite ext; eauto.
}{
intro types. destruct types. destruct H2; simpl. auto. constructor; eauto.
assert (S(S(ctx_len Γ)) = ctx_len(CtxU(CtxU Γ (TyFun B_op D)) A_op)) by auto.
rewrite H5. eauto.
}
Qed.


Lemma wf_is_under_ctx_tctx Γ Z T Σ:
  wf_t Γ Z T Σ -> 
  t_under_var T (ctx_len Γ) /\ t_under_tvar T (tctx_len Z).
Proof.
revert Γ. induction T; intros Γ wf.
+ destruct v as (x, i). inv wf. simpl. constructor.
  - eapply has_vtype_is_under_ctx. eauto.
  - apply tctx_len_gets in H6. omega.
+ inv wf. simpl. constructor. 2: auto.
  eapply has_vtype_is_under_ctx. eauto.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT in H7; destruct H7; assumption.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT1 in H8; apply IHT2 in H9; destruct H8; destruct H9; auto.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT in H8; destruct H8; assumption.
Qed.


Lemma handle_t_no_var h i Γ Z T Σ:
  h_no_var h i -> wf_t Γ Z T Σ ->
  c_no_var (handle_t (ctx_len Γ) (tctx_len Z) h T) 
    (i + ctx_len Γ + tctx_len Z).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (i+ctx_len Γ+tctx_len Z=tctx_len Z+(i+ctx_len Γ)) as comm by omega.
all: assert (S(S(i+ctx_len Γ+tctx_len Z))=(i+S(S(ctx_len Γ)))+tctx_len Z) 
  as ssctx by omega.
all: assert (S(i+ctx_len Γ+tctx_len Z)=(i+S(ctx_len Γ))+tctx_len Z)
  as sctx by (simpl; omega).
+ destruct v as (x, d). constructor; apply wf_is_under_ctx_tctx in H0;
  destruct H0; simpl in *. omega. rewrite comm. apply v_no_var_shift.
  eapply v_under_var_no_var. all: omega || eauto.
+ rewrite comm. apply v_no_var_shift. apply wf_is_under_ctx_tctx in H0.
  destruct H0. eapply v_under_var_no_var. all: omega || eauto.
+ constructor; inv H0.
  - rewrite comm. apply v_no_var_shift. eapply v_under_var_no_var.
    eapply has_vtype_is_under_ctx. all: omega || eauto.
  - assert (S(S(ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) B)) by (simpl; omega).
    rewrite ssctx, H0. auto.
+ inv H0. constructor. 2: constructor.
  - rewrite comm. apply v_no_var_shift. eapply v_under_var_no_var.
    eapply has_vtype_is_under_ctx. eauto. all: omega.
  - assert (S(ctx_len Γ)=ctx_len (CtxU Γ A)).
    simpl. omega. rewrite sctx, H0. auto.
  - assert (S(ctx_len Γ)=ctx_len (CtxU Γ B)).
    simpl. omega. rewrite sctx, H0. auto.
+ destruct (find_case h o) eqn:finds; inv H0.
  - destruct p as ((x, k), c_op). unfold c_subs2_out. unfold c_subs_out.
    apply c_no_var_subs. apply c_no_var_subs. all: omega || simpl.
    * eapply find_case_no_var in finds. 2: eauto. simpl.
      assert (S(S(i+ctx_len Γ+tctx_len Z))=ctx_len Γ+tctx_len Z+(2+i)) by omega.
      rewrite H0. apply c_no_var_shift. eauto. omega.
    * assert (S(i+ctx_len Γ+tctx_len Z)=tctx_len Z+1+(ctx_len Γ+i)) by omega.
      rewrite v_shift_shift, H0. apply v_no_var_shift; try omega.
      eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. eauto. omega.
    * simpl. assert (S(i+ctx_len Γ+tctx_len Z)=i+(S (ctx_len Γ))+tctx_len Z).
      omega. assert (S (ctx_len Γ) = ctx_len (CtxU Γ B_op)). simpl. omega.
      rewrite H0, H1. auto.
  - simpl. constructor.
    * rewrite comm. eapply v_under_var_no_var.
      eapply has_vtype_is_under_ctx. eauto. all: omega.
    * rewrite sctx. assert (S (ctx_len Γ) = ctx_len (CtxU Γ B_op)).
      simpl. omega. rewrite H0. auto.
Qed.

(* ==================== Handling and Shifts. ==================== *)

Lemma handle_t_shift Γ' Γ Z h T Σ D i:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (Sub.h_shift h 1 i) T
  = Sub.c_shift (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + ctx_len Γ + tctx_len Z).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (i+ctx_len Γ+tctx_len Z=tctx_len Z+(i+ctx_len Γ)) as comm by omega.
+ apply tctx_len_gets in H5 as zlen.
  destruct ((i + ctx_len Γ + tctx_len Z) <=? num) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. apply eq_sym. eapply v_shift_too_high.
    apply has_vtype_is_under_ctx in H3. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
+ f_equal. apply eq_sym. eapply v_shift_too_high.
    apply has_vtype_is_under_ctx in H2. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
+ f_equal.
  - apply eq_sym. eapply v_shift_too_high. 
    apply has_vtype_is_under_ctx in H6. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - assert (S(S(i+ctx_len Γ+tctx_len Z))=i+ctx_len(CtxU(CtxU Γ A)B)+tctx_len Z)
    as clen by (simpl; omega).
    assert (S(S(ctx_len Γ)) = ctx_len (CtxU(CtxU Γ A) B)) as clen' by omega.
    rewrite clen, clen', IHT; auto.
+ f_equal.
  - apply eq_sym. eapply v_shift_too_high. 
    apply has_vtype_is_under_ctx in H7. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - eapply (IHT1 _) in H8. simpl in H8.
    assert (S(i+ctx_len Γ+tctx_len Z)=i+S (ctx_len Γ)+tctx_len Z) by omega.
    rewrite H. eauto. assumption.
  - eapply (IHT2 _) in H9. simpl in H9.
    assert (S(i+ctx_len Γ+tctx_len Z)=i+S (ctx_len Γ)+tctx_len Z) by omega.
    rewrite H. eauto. assumption.
+ eapply h_has_case in H6 as find. 2: exact types.
  destruct find as [x[k[cop]]]. rename H into find.
  erewrite shift_find_Some, find; eauto. unfold c_subs2_out. unfold c_subs_out.
  rewrite c_shift_subs. 2: omega. f_equal.
  * rewrite c_shift_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+ctx_len Γ+tctx_len Z))=(ctx_len Γ+tctx_len Z)+S(S i))
    as cext by omega. rewrite cext.
    apply (c_shift_comm 1 (S(S i)) _ (ctx_len Γ+tctx_len Z)). omega.
    rewrite v_shift_shift, (v_shift_too_high (Sub.v_shift v (tctx_len Z+1) 0)).
    2:assert (S(i+ctx_len Γ+tctx_len Z)=(tctx_len Z+1)+(i+ctx_len Γ)) as comm'.
    reflexivity. omega. rewrite comm'. apply v_under_var_shift.
    apply has_vtype_is_under_ctx in H7. eapply v_under_var_weaken.
    all: omega || eauto.
  * f_equal. simpl. 
    assert (S(ctx_len Γ)=ctx_len (CtxU Γ B_op)) by (simpl;omega).
    assert (S(i+ctx_len Γ+tctx_len Z)=i+ctx_len (CtxU Γ B_op)+tctx_len Z).
    simpl. omega. rewrite H, H0, IHT. f_equal. all: assumption.
Qed.


Lemma handle_t_negshift Γ' Γ Z h T Σ D i:
  h_no_var h i -> wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (Sub.h_negshift h 1 i) T
  = Sub.c_negshift (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + ctx_len Γ + tctx_len Z).
Proof.
revert Γ h i. induction T; intros Γ h i novar wf types; simpl; inv wf.
all: assert (i+ctx_len Γ+tctx_len Z=tctx_len Z+(i+ctx_len Γ)) as comm by omega.
+ apply tctx_len_gets in H5 as zlen.
  destruct ((i + ctx_len Γ + tctx_len Z) <=? num) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. apply eq_sym. eapply v_negshift_too_high.
    apply has_vtype_is_under_ctx in H3. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
+ f_equal. apply eq_sym. eapply v_negshift_too_high.
    apply has_vtype_is_under_ctx in H2. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
+ f_equal.
  - apply eq_sym. eapply v_negshift_too_high. 
    apply has_vtype_is_under_ctx in H6. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - assert 
      (S(S(i+ctx_len Γ+tctx_len Z))=i+ctx_len(CtxU(CtxU Γ A) B)+tctx_len Z)
    as clen by (simpl; omega).
    assert (S(S(ctx_len Γ)) = ctx_len (CtxU(CtxU Γ A) B)) as clen' by omega.
    rewrite clen, clen', IHT; auto.
+ f_equal;
  assert (S(i + ctx_len Γ+tctx_len Z)=i+S (ctx_len Γ)+tctx_len Z) by omega.
  - apply eq_sym. eapply v_negshift_too_high.
    apply has_vtype_is_under_ctx in H7. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - eapply (IHT1 _) in H8. simpl in H8. rewrite H. all: eauto.
  - eapply (IHT2 _) in H9. simpl in H9. rewrite H. all: eauto.
+ eapply h_has_case in H6 as find. 2: exact types.
  destruct find as [x[k[cop]]]. rename H into find.
  erewrite find, negshift_find_Some. unfold c_subs2_out. unfold c_subs_out.
  2: eauto. rewrite c_negshift_subs. 2: omega. f_equal.
  * rewrite c_negshift_subs. 2: omega. f_equal; simpl.
    - assert (S(S(i+ctx_len Γ+tctx_len Z))=(ctx_len Γ+tctx_len Z)+S(S i))
      as cext by omega. rewrite cext.
      apply c_shift_negshift_comm. eapply find_case_no_var; eauto. omega.
    - rewrite v_shift_shift,(v_negshift_too_high(Sub.v_shift v(tctx_len Z+1)0)).
      2: assert (S(i+ctx_len Γ+tctx_len Z)=(tctx_len Z+1)+(i+ctx_len Γ))
      as comm' by omega. reflexivity. rewrite comm'.
      apply v_under_var_shift. 2: omega. apply has_vtype_is_under_ctx in H7.
      eapply v_under_var_weaken. eauto. omega.
    - assert (S(S(i+ctx_len Γ+tctx_len Z))=(ctx_len Γ+tctx_len Z)+S(S i)).
      omega. simpl. rewrite H. apply c_no_var_shift.
      eapply find_case_no_var; eauto. omega.
    - rewrite v_shift_shift. simpl. 
      assert (S(i+ctx_len Γ+tctx_len Z)=(tctx_len Z+1)+(i+ctx_len Γ)) by omega.
      rewrite H. apply v_no_var_shift. apply has_vtype_is_under_ctx in H7.
      eapply v_under_var_no_var. eauto. omega. omega.
  * simpl. f_equal. 
    assert (S(ctx_len Γ)=ctx_len (CtxU Γ B_op)) by (simpl;omega).
    assert (S(i+ctx_len Γ+tctx_len Z)=i+ctx_len (CtxU Γ B_op)+tctx_len Z).
    simpl. omega. rewrite H, H0, IHT. f_equal. all: assumption.
  * clear IHT. eapply c_no_var_subs; simpl. 3: omega.
    - assert (S(S(i+ctx_len Γ+tctx_len Z))=ctx_len Γ + tctx_len Z + (2+i)).
      omega. rewrite H. apply c_no_var_shift.
      eapply find_case_no_var; eauto. omega.
    - eapply v_under_var_no_var. rewrite v_shift_shift.
      eapply v_under_var_shift. eapply has_vtype_is_under_ctx. 
      all: omega || eauto.
  * assert (S(ctx_len Γ)=ctx_len (CtxU Γ B_op)) by (simpl;omega).
    assert (S(i+ctx_len Γ+tctx_len Z)=i+ctx_len (CtxU Γ B_op)+tctx_len Z).
    simpl. omega. simpl. rewrite H0, H. eapply handle_t_no_var; eauto.
Qed.


Lemma handle_t_sub Γ' Γ Z h T Σ D i v_s:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D ->
    handle_t (ctx_len Γ) (tctx_len Z) (Sub.h_sub h (i, v_s)) T
  = Sub.c_sub (handle_t (ctx_len Γ) (tctx_len Z) h T)
      (i+ctx_len Γ+tctx_len Z, Sub.v_shift v_s (ctx_len Γ+tctx_len Z) 0).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (i+ctx_len Γ+tctx_len Z=tctx_len Z+(i+ctx_len Γ)) as comm by omega.
+ apply tctx_len_gets in H5 as zlen.
  destruct ((i + ctx_len Γ + tctx_len Z) <=? num) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. apply eq_sym. assert (num=?i+ctx_len Γ+tctx_len Z=false).
    * apply leb_complete_conv in cmp. apply Nat.eqb_neq. omega.
    * rewrite H. reflexivity.
    * rewrite comm. rewrite v_sub_too_high.
      reflexivity. apply v_under_var_shift. 2: omega.
      eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
+ f_equal. apply eq_sym. eapply v_sub_too_high.
    apply has_vtype_is_under_ctx in H2. rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
+ f_equal.
  - apply eq_sym. eapply v_sub_too_high. apply has_vtype_is_under_ctx in H6.
    rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - assert 
      (S(S(i+ctx_len Γ+tctx_len Z))=i+ctx_len(CtxU(CtxU Γ A) B)+tctx_len Z)
    as clen by (simpl; omega).
    assert (S(S(ctx_len Γ)) = ctx_len (CtxU(CtxU Γ A) B)) as clen' by omega.
    rewrite clen, clen', IHT, v_shift_shift; auto. do 3 f_equal. simpl. omega.
+ f_equal.
  - apply eq_sym. eapply v_sub_too_high. apply has_vtype_is_under_ctx in H7.
    rewrite comm. apply v_under_var_shift.
    eapply v_under_var_weaken. eauto. all: omega.
  - eapply (IHT1 _) in H8. simpl in H8.
    assert (S(i + ctx_len Γ+tctx_len Z)=i+S (ctx_len Γ)+tctx_len Z) by omega.
    rewrite H, H8, v_shift_shift. do 3 f_equal. omega. assumption.
  - eapply (IHT2 _) in H9. simpl in H9.
    assert (S(i + ctx_len Γ+tctx_len Z)=i+S (ctx_len Γ)+tctx_len Z) by omega.
    rewrite H, H9, v_shift_shift. do 3 f_equal. omega. assumption.
+ eapply h_has_case in H6 as find. 2: exact types.
  destruct find as [x[k[cop]]]. rename H into find.
  erewrite sub_find_Some, find. 2:eauto. unfold c_subs2_out. unfold c_subs_out.
  rewrite c_sub_subs. 2:omega. f_equal.
  * rewrite c_sub_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+ctx_len Γ+tctx_len Z))=(ctx_len Γ+tctx_len Z)+S(S i))
    as cext by omega. rewrite cext. rewrite c_shift_sub.
    do 2 f_equal. do 3 rewrite v_shift_shift. f_equal. omega. omega.
    rewrite v_shift_shift, (v_sub_too_high (Sub.v_shift v (tctx_len Z + 1) 0)).
    reflexivity. assert (S(i+ctx_len Γ+tctx_len Z)=(tctx_len Z+1)+(i+ctx_len Γ))
    as comm' by omega. rewrite comm'. apply v_under_var_shift. 2: omega.
    apply has_vtype_is_under_ctx in H7. eapply v_under_var_weaken. eauto. omega.
  * simpl. f_equal. 
    assert (S(ctx_len Γ)=ctx_len (CtxU Γ B_op)) by (simpl;omega).
    assert (S(i+ctx_len Γ+tctx_len Z)=i+ctx_len (CtxU Γ B_op)+tctx_len Z).
    simpl. omega. rewrite H, H0, IHT. do 2 f_equal. rewrite v_shift_shift.
    f_equal. omega. all: assumption.
Qed.

(* ==================== Safety and Shifts. ==================== *)

Fixpoint v_insert_typesafe 
  Γ v A (orig : has_vtype Γ v A) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_vtype (ctx_insert Γ A_ins i) (Sub.v_shift v 1 i) A

with c_insert_typesafe 
  Γ c C (orig : has_ctype Γ c C) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_ctype (ctx_insert Γ A_ins i) (Sub.c_shift c 1 i) C

with h_insert_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_htype (ctx_insert Γ A_ins i) (Sub.h_shift h 1 i) Σ D

with respects_insert_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) A_ins i {struct orig} :
  has_htype Γ h Σ D -> wf_vtype A_ins ->
  respects (ctx_insert Γ A_ins i) (Sub.h_shift h 1 i) Σ D E

with veq_insert_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  veq A (ctx_insert Γ A_ins i) (Sub.v_shift v1 1 i) (Sub.v_shift v2 1 i)

with ceq_insert_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  ceq C (ctx_insert Γ A_ins i) (Sub.c_shift c1 1 i) (Sub.c_shift c2 1 i).

Proof.
all: rename v_insert_typesafe into V; rename c_insert_typesafe into CI.
all: rename h_insert_typesafe into HC; rename respects_insert_typesafe into R.
all: rename veq_insert_typesafe into VE; rename ceq_insert_typesafe into CE.
{
intros wfins. apply TypeV.
{ apply ctx_insert_wf. inv orig. assumption. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE. simpl. apply TypeUnit.
+ clear V CI HC R VE CE. simpl. apply TypeInt.
+ clear V CI HC R VE CE.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (V _ _ _ H1) as IHv1. specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE. simpl. apply TypePair; auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeInl. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeInr. auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (HC _ _ _ _ H2) as IHh. specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHres.
  clear V CI HC R VE CE.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. eapply TypeVSubtype; auto.
}{
intros wfins. apply TypeC.
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeRet. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeAbsurd. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. eapply TypeΠMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE.
  simpl. eapply TypeΣMatch. auto. all: rewrite ctx_insert_extend; auto.
+ specialize (CI _ _ _ H1) as IHc1. specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE.
  simpl. eapply TypeDoBind. auto. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE. simpl. eapply TypeApp; auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. eapply TypeHandle; auto.
+ specialize (CI _ _ _ H1) as IHc1.
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE. simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H2) as IHv. specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE.
  simpl. eapply TypeOp. 3: rewrite ctx_insert_extend. all: eauto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE. eapply TypeCSubtype; auto.
}{
intros wfins. apply TypeH.
{ apply ctx_insert_wf. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear V CI HC R VE CE. apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE.
  simpl. apply TypeCasesU. 2: auto.
  - apply shift_find_None. assumption.
  - do 2 rewrite ctx_insert_extend. auto.
}{
intros types wfins. apply Respects.
{ clear V CI HC R VE CE. apply ctx_insert_wf. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H3.
+ clear V CI HC R VE CE. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ H3) as IHres. specialize (CE _ _ _ _ H4) as IHeq.
  clear V CI HC R VE CE. apply RespectEqsU. auto.
  rewrite join_ctxs_insert, join_ctx_tctx_insert.
  erewrite handle_t_shift. erewrite handle_t_shift.
  assert (tctx_len Z+(ctx_len Γ'+i) = i+ctx_len Γ'+tctx_len Z) by omega.
  rewrite H5. apply IHeq.
  all: inv H2. all: try eassumption.
}{
intros wfins. apply Veq.
{ inv orig. assumption. }
{ apply ctx_insert_wf. inv orig. all: assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE. apply VRefl. f_equal. assumption.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. apply VSym. auto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. eapply VTrans; eauto.
+ clear V CI HC R VE CE. simpl. apply InUnit.
+ clear V CI HC R VE CE. simpl. apply InInt. auto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. simpl. apply InPair; auto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElPairL; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElPairR; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InInr; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElInr; eauto.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InFun.
  rewrite ctx_insert_extend. auto.
}{
intros wfins. apply Ceq.
{ inv orig. assumption. }
{ apply ctx_insert_wf. inv orig. all: assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE. apply CRefl. f_equal. assumption.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. apply CSym. auto.
+ specialize (CE _ _ _ _ H1) as IH1.
  specialize (CE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. eapply CTrans; eauto.
}
Qed.


Fixpoint v_shift_typesafe v (Γ:ctx) A0 A :
  has_vtype Γ v A -> wf_vtype A0 ->
  has_vtype (CtxU Γ A0) (Sub.v_shift v 1 0) A

with c_shift_typesafe c (Γ:ctx) A0 C :
  has_ctype Γ c C -> wf_vtype A0 ->
  has_ctype (CtxU Γ A0) (Sub.c_shift c 1 0) C

with h_shift_typesafe h (Γ:ctx) A0 Σ D :
  has_htype Γ h Σ D -> wf_vtype A0 ->
  has_htype (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D

with respects_shift_typesafe Γ h Σ D E A0 :
  respects Γ h Σ D E -> has_htype Γ h Σ D -> wf_vtype A0 ->
  respects (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D E

with veq_shift_typesafe Γ A v1 v2 A0 :
  veq A Γ v1 v2 -> wf_vtype A0 ->
  veq A (CtxU Γ A0) (Sub.v_shift v1 1 0) (Sub.v_shift v2 1 0)

with ceq_shift_typesafe Γ C c1 c2 A0 :
  ceq C Γ c1 c2 -> wf_vtype A0 ->
  ceq C (CtxU Γ A0) (Sub.c_shift c1 1 0) (Sub.c_shift c2 1 0).

Proof.
all: intros orig;
assert (ctx_insert Γ A0 0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H.
apply v_insert_typesafe. assumption.
apply c_insert_typesafe. assumption.
apply h_insert_typesafe. assumption.
apply respects_insert_typesafe. assumption.
apply veq_insert_typesafe. assumption.
apply ceq_insert_typesafe. assumption.
Qed.


Lemma v_join_ctx_tctx_typesafe Γ Z D v A :
  has_vtype Γ v A -> wf_tctx Z -> wf_ctype D ->
  has_vtype (join_ctx_tctx Γ Z D) (Sub.v_shift v (tctx_len Z) 0) A.
Proof.
intros; induction Z; simpl.
+ rewrite v_shift_0. assumption.
+ assert (S(tctx_len Z)=tctx_len Z+1) by omega. rewrite H2.
  rewrite <-v_shift_shift. apply v_shift_typesafe.
  all: inv H0; try apply WfTyFun; auto.
Qed.


Lemma v_join_ctxs_typesafe Γ Γ' v A :
  has_vtype Γ v A -> wf_ctx Γ' -> 
  has_vtype (join_ctxs Γ Γ') (Sub.v_shift v (ctx_len Γ') 0) A.
Proof.
intros; induction Γ'; simpl.
+ rewrite v_shift_0. assumption.
+ assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H1.
  rewrite <-v_shift_shift. apply v_shift_typesafe; inv H0; auto.
Qed.


Lemma v_join_all_ctxs_typesafe Γ Γ' Z D v A :
  has_vtype Γ v A -> wf_ctx Γ' -> wf_tctx Z -> wf_ctype D ->
  has_vtype (join_ctx_tctx (join_ctxs Γ Γ') Z D)
    (Sub.v_shift v (ctx_len Γ'+tctx_len Z) 0) A.
Proof.
intros; induction Γ'; simpl.
+ apply v_join_ctx_tctx_typesafe; auto.
+ assert (S(ctx_len Γ'+tctx_len Z)=S(ctx_len Γ')+tctx_len Z) by omega.
  rewrite H3, <-v_shift_shift. apply v_join_ctx_tctx_typesafe; auto.
  assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H4.
  rewrite <-v_shift_shift. apply v_shift_typesafe; inv H0; auto.
  apply v_join_ctxs_typesafe; auto.
Qed.


Fixpoint v_sub_typesafe 
  Γ v A (orig: has_vtype Γ v A) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A

with c_sub_typesafe
  Γ c C (orig: has_ctype Γ c C) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C

with h_sub_typesafe
  Γ h Σ D (orig: has_htype Γ h Σ D) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D

with respects_sub_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) i v_s A_s {struct orig} :
  has_htype Γ h Σ D -> get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  respects Γ (Sub.h_sub h (i, v_s)) Σ D E

with veq_sub_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  veq A Γ (Sub.v_sub v1 (i, v_s)) (Sub.v_sub v2 (i, v_s))

with ceq_sub_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  ceq C Γ (Sub.c_sub c1 (i, v_s)) (Sub.c_sub c2 (i, v_s)).
Proof.
all: rename v_sub_typesafe into V; rename c_sub_typesafe into CI.
all: rename h_sub_typesafe into HC; rename respects_sub_typesafe into R.
all: rename veq_sub_typesafe into VE; rename ceq_sub_typesafe into CE.
{
intros gets vsty. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear V CI HC R VE CE. 
  simpl. apply TypeUnit.
+ clear V CI HC R VE CE. 
  simpl. apply TypeInt.
+ clear V CI HC R VE CE.
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv vsty. assumption.
  - apply TypeVar. assumption.
+ specialize (V _ _ _ H1) as IHv1. 
  specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE. simpl. apply TypePair; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE. apply TypeInl; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE. apply TypeInr; eauto.
+ specialize (CI _ _ _ H1) as IHc. 
  specialize (V _ _ _ vsty) as IHvs.
  clear V CI HC R VE CE. simpl.
  apply TypeFun. eapply IHc. eauto. inv H0. apply v_shift_typesafe; auto.
+ specialize (HC _ _ _ _ H2) as IHh. 
  specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE. simpl. apply TypeHandler; eauto. eapply IHc. 
  exact gets. inv H0. inv H6. apply v_shift_typesafe; assumption.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. eapply TypeVSubtype; eauto.
}{
intros gets vsty. apply TypeC; inv orig.
assumption. assumption. destruct H1.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE. apply TypeRet; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE. apply TypeAbsurd; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. eapply TypeΠMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE. simpl. eapply TypeΣMatch. eauto.
  - eapply IHc1. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
  - eapply IHc2. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE. simpl. eapply TypeDoBind. eauto.
  eapply IHc2. exact gets. inv H1. inv H4. apply v_shift_typesafe; auto. 
+ specialize (V _ _ _ H1) as IHv. 
  specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE. simpl. eapply TypeApp; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. eapply TypeHandle; eauto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE. simpl. eapply TypeLetRec.
  - eapply IHc1. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. exact gets. inv H1. inv H3. apply v_shift_typesafe; auto.
+ specialize (V _ _ _ H2) as IHv. 
  specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE. simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H3. inv H4. apply v_shift_typesafe; auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE. eapply TypeCSubtype; eauto.
}{
intros gets vsty; simpl; apply TypeH; inv orig.
all: try assumption.
destruct H2.
+ clear V CI HC R VE CE. 
  apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. 
  specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE. simpl. apply TypeCasesU; eauto.
  - rewrite sub_find_None; auto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfTyFun; assumption.
}{
intros htys gets vsty; simpl. apply Respects; inv orig.
all: try assumption.
destruct H3.
+ clear V CI HC R VE CE. 
  apply RespectEqsØ.
+ specialize (CE _ _ _ _ H4) as IHc. 
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE.
  apply RespectEqsU. eauto. erewrite handle_t_sub. erewrite handle_t_sub.
  eapply IHc. all: inv H2; eauto. clear IHc IHr.
  * erewrite <-get_join_ctx_tctx, <-get_join_ctxs. eauto.
  * eapply v_join_all_ctxs_typesafe; auto.
}{
intros gets types. apply Veq.
{ inv orig. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE. apply VRefl. f_equal. assumption.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. apply VSym. eauto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. eapply VTrans; eauto.
+ clear V CI HC R VE CE. simpl. apply InUnit.
+ clear V CI HC R VE CE. simpl. apply InInt. auto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. simpl. apply InPair; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElPairL; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElPairR; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InInr; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl in *. eapply ElInr; eauto.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. simpl. eapply InFun. eapply IH.
  - simpl. eauto.
  - inv H. apply v_shift_typesafe; auto.
}{
intros gets types. apply Ceq.
{ inv orig. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE. apply CRefl. f_equal. assumption.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE. apply CSym. eauto.
+ specialize (CE _ _ _ _ H1) as IH1.
  specialize (CE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE. eapply CTrans; eauto.
}
Qed.


Fixpoint v_subs_typesafe 
  Γ Γ' v A i v_s A_s (orig: has_vtype Γ' v A) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_vtype Γ (v_subs v v_s i) A

with c_subs_typesafe
  Γ Γ' c C i v_s A_s (orig: has_ctype Γ' c C) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_ctype Γ (c_subs c v_s i) C

with h_subs_typesafe
  Γ Γ' h Σ D i v_s A_s (orig: has_htype Γ' h Σ D) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_htype Γ (h_subs h v_s i) Σ D

with respects_subs_typesafe
  Γ Γ' h Σ D E i v_s A_s (orig: respects Γ' h Σ D E) {struct orig} :
  has_htype Γ' h Σ D -> has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i ->
  ctx_len Γ >= i ->
  respects Γ (h_subs h v_s i) Σ D E

with veq_subs_typesafe
  Γ Γ' A v1 v2 i v_s A_s (orig: veq A Γ' v1 v2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  veq A Γ (v_subs v1 v_s i) (v_subs v2 v_s i)

with ceq_subs_typesafe
  Γ Γ' C c1 c2 i v_s A_s (orig: ceq C Γ' c1 c2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c1 v_s i) (c_subs c2 v_s i).
Proof.
all: rename v_subs_typesafe into V; rename c_subs_typesafe into CI.
all: rename h_subs_typesafe into HC; rename respects_subs_typesafe into R.
all: rename veq_subs_typesafe into VE; rename ceq_subs_typesafe into CE.
{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear V CI HC R VE CE. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeUnit.
+ clear V CI HC R VE CE. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInt.
+ clear V CI HC R VE CE. 
  apply TypeV; auto; unfold v_subs; simpl. destruct (n=?i) eqn:ni.
  - apply Nat.eqb_eq in ni. subst.
    rewrite v_negshift_shift, v_shift_0. rewrite get_ctx_insert_new in H1.
    inv tyvs. inv H1. assumption. auto. omega.
  - subst. simpl. destruct (i<=?n) eqn:cmp; apply TypeVar.
    * erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. omega.
+ specialize (V Γ Γ0 v1 _ i _ _ H1 tyvs geq) as IH1.
  specialize (V Γ Γ0 v2 _ i _ _ H2 tyvs geq) as IH2.
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypePair; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInl; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInr; auto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  inv H0. specialize (v_shift_typesafe _ Γ A _ tyvs H5) as tyvs'.
  specialize (CI _ _ c _ (1+i) _ _ H1 tyvs') as IH. 
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. apply WfTyFun; auto. apply TypeFun. 
  rewrite v_shift_comm. apply IH. simpl. f_equal. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; inv H7; assumption).
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (CI _ _ c_ret _ (1+i) _ _ H1 tyvs' H4) as IHc. 
  specialize (HC _ _ h _ _ i _ _ H2 tyvs geq) as IHh. 
  specialize (R _ _ h _ _ _ i _ _ H3 H2 tyvs) as IHr.
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeHandler. 
  rewrite v_shift_comm. apply IHc. simpl. omega. omega. auto. auto.
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE.
  apply TypeV; auto; unfold v_subs; simpl. 
  eapply TypeVSubtype; eauto.
}{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1. 
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeRet. auto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeAbsurd. auto.
+ assert (CtxU (CtxU Γ0 A) B = ctx_insert (CtxU (CtxU Γ A) B) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (V _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CI _ _ c _ (2+i) _ _ H2 tyvs'' H3) as IHc.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeΠMatch. eauto. 
  rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc.
  simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)) as geqa.
  { simpl. f_equal. auto. }
  assert (CtxU Γ0 B = ctx_insert (CtxU Γ B) A_s (1+i)) as geqb.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (V _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CI _ _ cl _ (1+i) _ _ H2 tyvsa geqa) as IHc1.
  specialize (CI _ _ cr _ (1+i) _ _ H3 tyvsb geqb) as IHc2.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeΣMatch. eauto. 
  - rewrite v_shift_comm. apply IHc1. simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)) as geqa.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (CI _ _ c1 _ i _ _ H1 tyvs geq) as IHc1.
  specialize (CI _ _ c2 _ (1+i) _ _ H2 tyvsa geqa) as IHc2.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeDoBind. eauto. 
  rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ specialize (V _ _ v1 _ i _ _ H1 tyvs) as IH1.
  specialize (V _ _ v2 _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeApp. eauto. eauto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IHv.
  specialize (CI _ _ c _ i _ _ H2 tyvs) as IHc.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeHandle. eauto. eauto.
+ assert (CtxU (CtxU Γ0 A) (TyFun A C) 
    = ctx_insert (CtxU (CtxU Γ A) (TyFun A C)) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (CtxU Γ0 (TyFun A C) = ctx_insert (CtxU Γ (TyFun A C)) A_s (1+i)).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; inv H10; auto).
  assert (wf_ctype C) as wfc by (inv H1; inv H5; inv H10; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' (WfTyFun A C wfa wfc)) 
  as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs (WfTyFun A C wfa wfc)) 
  as tyvs'''.
  specialize (CI _ _ c1 _ (2+i) _ _ H1 tyvs'' H3) as IHc1.
  specialize (CI _ _ c2 _ (1+i) _ _ H2 tyvs''' H4) as IHc2.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeLetRec. 
  - rewrite v_shift_shift in IHc1. rewrite v_shift_comm. apply IHc1. 
    simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU Γ0 B_op = ctx_insert (CtxU Γ B_op) A_s (1+i)) as geqb.
  { simpl. f_equal. auto. }
  assert (wf_vtype B_op) as wfb by (inv H3; inv H4; auto).
  specialize (v_shift_typesafe _ _ B_op _ tyvs wfb) as tyvsb.
  specialize (V _ _ v _ i _ _ H2 tyvs geq) as IHv.
  specialize (CI _ _ c _ (1+i) _ _ H3 tyvsb geqb) as IHc.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CI Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubtype; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2. 
+ clear V CI HC R VE CE.
  apply TypeH; auto; unfold h_subs; simpl. apply TypeCasesØ.
+ assert (CtxU (CtxU Γ0 (TyFun B_op D)) A_op 
    = ctx_insert (CtxU (CtxU Γ (TyFun B_op D)) A_op) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A_op) as wfa by (inv H0; auto).
  assert (wf_vtype (TyFun B_op D)) as wfb by (inv H0; apply WfTyFun; auto).
  specialize (v_shift_typesafe _ _ (TyFun B_op D) _ tyvs wfb) as tyvs'.
  specialize (v_shift_typesafe _ _ A_op _ tyvs' wfa) as tyvs''.
  specialize (HC _ _ h _ _ i _ _ H3 tyvs geq) as IHh.
  specialize (CI _ _ c_op _ (2+i) _ _ H4 tyvs'' H5) as IHc.
  clear V CI HC R VE CE.
  apply TypeH; auto; unfold h_subs; simpl. eapply TypeCasesU.
  - apply negshift_find_None. apply sub_find_None. assumption.
  - auto. 
  - rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
    simpl. omega. omega.
}{
intros tysh tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H3. 
+ clear V CI HC R VE CE.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ _ i v_s _ H3 tysh tyvs geq) as IHr.
  specialize (CE (join_ctx_tctx (join_ctxs Γ Γ') Z D) (join_ctx_tctx (join_ctxs Γ0 Γ') Z D) D (handle_t (ctx_len Γ') (tctx_len Z) h T1) (handle_t (ctx_len Γ') (tctx_len Z) h T2) (ctx_len Γ' + tctx_len Z + i) (Sub.v_shift v_s (ctx_len Γ' + tctx_len Z) 0) A_s H4) as IHc.
  all: clear V CI HC R VE CE.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsU. auto.
  assert (i + ctx_len Γ' + tctx_len Z = ctx_len Γ' + tctx_len Z + i) by omega. 
  erewrite handle_t_negshift, handle_t_sub, v_shift_comm.
  erewrite handle_t_negshift, handle_t_sub, (v_shift_comm 1 i).
  rewrite H5. eapply IHc.
  all: omega || (inv H2; eauto).
  - apply v_join_all_ctxs_typesafe; auto.
  - assert (ctx_len Γ' + tctx_len Z + i = tctx_len Z + (ctx_len Γ'+i)) by omega.
    rewrite H2, <-join_ctx_tctx_insert. f_equal.
    rewrite <-join_ctxs_insert. f_equal.
  - rewrite join_ctx_tctx_len, join_ctxs_len. omega.
  - apply h_sub_makes_no_var. apply v_shift_makes_no_var.
  - eapply h_sub_typesafe; eauto. apply get_ctx_insert_new. auto.
    eapply v_insert_typesafe; auto. inv tyvs. auto.
  - apply h_sub_makes_no_var. apply v_shift_makes_no_var.
  - eapply h_sub_typesafe; eauto. apply get_ctx_insert_new. auto.
    eapply v_insert_typesafe; auto. inv tyvs. auto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear V CI HC R VE CE. subst.
  apply Veq; auto; unfold v_subs; simpl. apply VRefl. auto.
+ specialize (VE _ _ _ v1 v2 i _ _ H1 tyvs) as IHv.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. apply VSym. auto.
+ specialize (VE _ _ _ v1 v2 i _ _ H1 tyvs) as IHv1.
  specialize (VE _ _ _ v2 v3 i _ _ H2 tyvs) as IHv2.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. eapply VTrans; eauto.
+ clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. apply InUnit.
+ clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. apply InInt. auto.
+ specialize (VE _ _ _ v1 v1' i _ _ H1 tyvs) as IH1.
  specialize (VE _ _ _ v2 v2' i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. apply InPair; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto. unfold v_subs in *. simpl in *. eapply ElPairL; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto. unfold v_subs in *. simpl in *. eapply ElPairR; eauto.
+ specialize (VE _ _ _ v v' i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. eapply InInl; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs in *; simpl in *. eapply ElInl; eauto.
+ specialize (VE _ _ _ v v' i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs; simpl. eapply InInr; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE.
  apply Veq; auto; unfold v_subs in *; simpl in *. eapply ElInr; eauto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  inv H. specialize (v_shift_typesafe _ _ A _ tyvs H5) as tyvs'.
  specialize (CE _ _ _ _ _ (1+i) _ _ H1 tyvs') as IH.
  clear V CI HC R VE CE.
  apply Veq; auto. apply WfTyFun; auto.
  unfold v_subs. unfold c_subs in IH. simpl. eapply InFun. 
  rewrite v_shift_comm. eapply IH. all: simpl; omega || eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear V CI HC R VE CE. subst.
  apply Ceq; auto; unfold c_subs; simpl; apply CRefl. auto.
+ specialize (CE _ _ _ c1 c2 i _ _ H1 tyvs) as IHv.
  clear V CI HC R VE CE.
  apply Ceq; auto; unfold c_subs; simpl. apply CSym. auto.
+ specialize (CE _ _ _ c1 c2 i _ _ H1 tyvs) as IHc1.
  specialize (CE _ _ _ c2 c3 i _ _ H2 tyvs) as IHc2.
  clear V CI HC R VE CE.
  apply Ceq; auto; unfold c_subs; simpl. eapply CTrans; eauto.
}
Qed.