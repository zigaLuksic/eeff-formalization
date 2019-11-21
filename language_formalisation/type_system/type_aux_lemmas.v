Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

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
  clear V CI HC R VE CE. inv orig. inv H1.
}{
  clear V CI HC R VE CE. inv orig. inv H1.
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


Fixpoint v_remove_typesafe 
  Γ v A (orig : has_vtype Γ v A) i {struct orig} :
  v_no_var v i ->
  has_vtype (ctx_remove Γ i) (Sub.v_negshift v 1 i) A

with c_remove_typesafe 
  Γ c C (orig : has_ctype Γ c C) i {struct orig} :
  c_no_var c i ->
  has_ctype (ctx_remove Γ i) (Sub.c_negshift c 1 i) C

with h_remove_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) i {struct orig} :
  h_no_var h i ->
  has_htype (ctx_remove Γ i) (Sub.h_negshift h 1 i) Σ D

with respects_remove_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) A_ins i {struct orig} :
  has_htype Γ h Σ D -> h_no_var h i -> wf_vtype A_ins ->
  respects (ctx_remove Γ i) (Sub.h_negshift h 1 i) Σ D E

with veq_remove_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) A_ins i {struct orig} :
  wf_vtype A_ins -> v_no_var v1 i -> v_no_var v2 i ->
  veq A (ctx_remove Γ i) (Sub.v_negshift v1 1 i) (Sub.v_negshift v2 1 i)

with ceq_remove_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) A_ins i {struct orig} :
  wf_vtype A_ins -> c_no_var c1 i -> c_no_var c2 i ->
  ceq C (ctx_remove Γ i) (Sub.c_negshift c1 1 i) (Sub.c_negshift c2 1 i).
Proof.
all: rename v_remove_typesafe into V; rename c_remove_typesafe into CI.
all: rename h_remove_typesafe into HC; rename respects_remove_typesafe into R.
all: rename veq_remove_typesafe into VE; rename ceq_remove_typesafe into CE.
{
intros no_var. simpl in no_var. apply TypeV; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct H1.
+ clear V CI HC R VE CE. simpl. 
  apply TypeUnit.
+ clear V CI HC R VE CE. simpl. 
  apply TypeInt.
+ clear V CI HC R VE CE. simpl. 
  destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct n. destruct no_var. omega.
      simpl. assert (n-0=n) by omega. rewrite H2. assumption.
    * destruct cmp. destruct no_var. reflexivity. omega.
  - apply TypeVar. rewrite <-get_ctx_remove_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (V _ _ _ H1) as IHv1. specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE. simpl. destruct no_var. apply TypePair; auto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE. apply TypeInl. auto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE. apply TypeInr. auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE. simpl. 
  apply TypeFun. rewrite ctx_remove_extend. auto.
+ specialize (HC _ _ _ _ H2) as IHh. 
  specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE. simpl. destruct no_var.
  apply TypeHandler. rewrite ctx_remove_extend. all: eauto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. eapply TypeVSubtype; auto.
}{
intros no_var. simpl in no_var. apply TypeC; inv orig.
{ apply ctx_remove_wf. assumption. }
{ assumption. }
destruct H1.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeRet. apply IHv; assumption.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE. simpl. apply TypeAbsurd. apply IHv; assumption.
+ specialize (V _ _ _ H1) as IHv.
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeΠMatch; auto.
  do 2 rewrite ctx_remove_extend. auto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE. simpl. destruct no_var. destruct H5.
  eapply TypeΣMatch; try rewrite ctx_remove_extend; auto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeDoBind; auto.
  rewrite ctx_remove_extend. auto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeApp; auto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeHandle; auto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeLetRec.
  - do 2 rewrite ctx_remove_extend. auto.
  - rewrite ctx_remove_extend. auto.
+ specialize (V _ _ _ H2) as IHv. 
  specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE. simpl. destruct no_var. eapply TypeOp; eauto.
  rewrite ctx_remove_extend. auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE. eapply TypeCSubtype; auto.
}{
intros no_var; simpl; apply TypeH; inv orig.
apply ctx_remove_wf. all: auto. destruct H2.
+ simpl. clear V CI HC R VE CE. apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. 
  specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE. simpl. apply TypeCasesU; inv no_var; auto.
  - apply negshift_find_None. auto.
  - do 2 rewrite ctx_remove_extend. auto.
}{
intros types no_var wfins. apply Respects.
{ clear V CI HC R VE CE. apply ctx_remove_wf. inv types. assumption. }
all: try (inv orig; assumption).
inv orig. destruct H3.
+ clear V CI HC R VE CE. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ H3) as IHres. 
  specialize (CE _ _ _ _ H4) as IHeq.
  clear V CI HC R VE CE. apply RespectEqsU. eauto.
  rewrite join_ctxs_remove. rewrite join_ctx_tctx_remove.
  erewrite handle_t_negshift. erewrite handle_t_negshift.
  all: eauto; inv H2; auto.
  assert (tctx_len Z+(ctx_len Γ'+i) = i+ctx_len Γ'+tctx_len Z) by omega.
  rewrite H2. eapply IHeq. eauto. all: eapply handle_t_no_var; eauto.
}{
  clear V CI HC R VE CE. inv orig. inv H1.
}{
  clear V CI HC R VE CE. inv orig. inv H1.
}
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
  clear V CI HC R VE CE. inv orig. inv H1.
}{
  clear V CI HC R VE CE. inv orig. inv H1.
}
Qed.
