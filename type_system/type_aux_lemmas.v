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
  ceq C (ctx_insert Γ A_ins i) (Sub.c_shift c1 1 i) (Sub.c_shift c2 1 i)
  
with heq_insert_typesafe
  Γ Σ D h1 h2 (orig: heq Σ D Γ h1 h2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  heq Σ D (ctx_insert Γ A_ins i) (Sub.h_shift h1 1 i) (Sub.h_shift h2 1 i).

Proof.
all: rename v_insert_typesafe into V; rename c_insert_typesafe into CI.
all: rename h_insert_typesafe into HC; rename respects_insert_typesafe into R.
all: rename veq_insert_typesafe into VE; rename ceq_insert_typesafe into CE.
all: rename heq_insert_typesafe into HE.
{
intros wfins. apply TypeV.
{ apply ctx_insert_wf. inv orig. assumption. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE HE. simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE. simpl. apply TypeInt.
+ clear V CI HC R VE CE HE.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (V _ _ _ H1) as IHv1. specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE. simpl. apply TypePair; auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. simpl. apply TypeInl. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. simpl. apply TypeInr. auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (HC _ _ _ _ H2) as IHh. specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHres.
  clear V CI HC R VE CE HE.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. eapply TypeVSubtype; auto.
}{
intros wfins. apply TypeC.
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. simpl. apply TypeRet. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. simpl. apply TypeAbsurd. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply TypeΠMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE.
  simpl. eapply TypeΣMatch. auto. all: rewrite ctx_insert_extend; auto.
+ specialize (CI _ _ _ H1) as IHc1. specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE.
  simpl. eapply TypeDoBind. auto. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE HE. simpl. eapply TypeApp; auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply TypeHandle; auto.
+ specialize (CI _ _ _ H1) as IHc1.
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H2) as IHv. specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE.
  simpl. eapply TypeOp. 3: rewrite ctx_insert_extend. all: eauto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE. eapply TypeCSubtype; auto.
}{
intros wfins. apply TypeH.
{ apply ctx_insert_wf. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear V CI HC R VE CE HE. apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE.
  simpl. apply TypeCasesU. 2: auto.
  - apply shift_find_None. assumption.
  - do 2 rewrite ctx_insert_extend. auto.
}{
intros types wfins. apply Respects.
{ clear V CI HC R VE CE HE. apply ctx_insert_wf. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H3.
+ clear V CI HC R VE CE HE. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ H3) as IHres. specialize (CE _ _ _ _ H4) as IHeq.
  clear V CI HC R VE CE HE. apply RespectEqsU. auto.
  rewrite join_ctxs_insert, join_ctx_tctx_insert.
  erewrite handle_t_shift. erewrite handle_t_shift.
  assert (tctx_len Z+(ctx_len Γ'+i) = i+ctx_len Γ'+tctx_len Z) by omega.
  rewrite H5. apply IHeq.
  all: inv H2. all: try eassumption.
}{
intros wfins. apply Veq.
{ inv orig. assumption. }
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H3.
+ clear V CI HC R VE CE HE. apply VeqRefl. f_equal. assumption.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. apply VeqSym. auto.
+ specialize (VE _ _ _ _ H3) as IH1.
  specialize (VE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE. subst. simpl.
  destruct (i <=? j) eqn:cmp; eapply VeqVar; eauto.
  - erewrite <-get_ctx_insert_changed. auto. apply leb_complete in cmp. auto.
  - erewrite <-get_ctx_insert_unchanged. assumption. 
    apply leb_complete_conv in cmp. assumption.
+ clear V CI HC R VE CE HE. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE. simpl. apply VeqInt. auto.
+ specialize (VE _ _ _ _ H3) as IH1.
  specialize (VE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. simpl. apply VeqPair; auto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqInr; eauto.
+ specialize (CE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqFun.
  rewrite ctx_insert_extend. auto.
+ specialize (CE _ _ _ _ H3) as IHc.
  specialize (HE _ _ _ _ _ H4) as IHh.
  clear V CI HC R VE CE HE. simpl. eapply VeqHandler; eauto.
  rewrite ctx_insert_extend. auto.
+ clear V CI HC R VE CE HE. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE. simpl. rewrite <-v_shift_comm. apply ηFun. omega.
}{
intros wfins. apply Ceq.
{ inv orig. assumption. }
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H3.
+ clear V CI HC R VE CE HE. apply CeqRefl. f_equal. assumption.
+ specialize (CE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. apply CeqSym. auto.
+ specialize (CE _ _ _ _ H3) as IH1.
  specialize (CE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqRet. auto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqAbsurd. auto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqΠMatch. auto.
  do 2 rewrite ctx_insert_extend. auto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc1.
  specialize (CE _ _ _ _ H5) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply CeqΣMatch. auto.
  all: rewrite ctx_insert_extend; auto.
+ specialize (CE _ _ _ _ H3) as IHc1.
  specialize (CE _ _ _ _ H4) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply CeqDoBind. eauto.
  rewrite ctx_insert_extend; auto.
+ specialize (VE _ _ _ _ H3) as IHv1.
  specialize (VE _ _ _ _ H4) as IHv2.
  clear V CI HC R VE CE HE. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqHandle; eauto.
+ specialize (CE _ _ _ _ H3) as IHc1.
  specialize (CE _ _ _ _ H4) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply CeqLetRec.
  do 2 rewrite ctx_insert_extend; auto.
  rewrite ctx_insert_extend; auto.
+ specialize (VE _ _ _ _ H4) as IHv.
  specialize (CE _ _ _ _ H5) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqOp; eauto.
  rewrite ctx_insert_extend; auto.
+ clear V CI HC R VE CE HE. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  simpl. rewrite <-c_shift_comm. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. simpl. rewrite <-c_shift_comm. 
  eapply βDoBind_Op. omega.
+ clear V CI HC R VE CE HE. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  simpl. rewrite <-c_shift_comm, <-h_shift_comm.
  eapply rule. apply shift_find_Some. eauto. all: omega.
}{
intros wfins. apply Heq.
{ inv orig. assumption. }
{ inv orig. assumption. }
{ apply ctx_insert_wf. inv orig. all: assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H4.
+ clear V CI HC R VE CE HE. apply HeqRefl. f_equal. assumption.
+ specialize (HE _ _ _ _ _ H4) as IH.
  clear V CI HC R VE CE HE. apply HeqSym. auto.
+ specialize (HE _ _ _ _ _ H4) as IH1.
  specialize (HE _ _ _ _ _ H5) as IH2.
  clear V CI HC R VE CE HE. eapply HeqTrans; eauto.
+ clear V CI HC R VE CE HE. eapply HeqSigØ.
+ specialize (CE _ _ _ _ H6) as IH1.
  specialize (HE _ _ _ _ _ H7) as IH2.
  clear V CI HC R VE CE HE. eapply HeqSigU; eauto.
  - eapply shift_find_Some in H4. eauto.
  - eapply shift_find_Some in H5. eauto.
  - rewrite ctx_insert_extend, ctx_insert_extend. eauto.
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
  ceq C (CtxU Γ A0) (Sub.c_shift c1 1 0) (Sub.c_shift c2 1 0)

with heq_shift_typesafe Γ Σ D h1 h2 A0 :
  heq Σ D Γ h1 h2 -> wf_vtype A0 ->
  heq Σ D (CtxU Γ A0) (Sub.h_shift h1 1 0) (Sub.h_shift h2 1 0).

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
apply heq_insert_typesafe. assumption.
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
  ceq C Γ (Sub.c_sub c1 (i, v_s)) (Sub.c_sub c2 (i, v_s))

with heq_sub_typesafe
  Γ Σ D h1 h2 (orig: heq Σ D Γ h1 h2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  heq Σ D Γ (Sub.h_sub h1 (i, v_s)) (Sub.h_sub h2 (i, v_s)).

Proof.
all: rename v_sub_typesafe into V; rename c_sub_typesafe into CI.
all: rename h_sub_typesafe into HC; rename respects_sub_typesafe into R.
all: rename veq_sub_typesafe into VE; rename ceq_sub_typesafe into CE.
all: rename heq_sub_typesafe into HE.
{
intros gets vsty. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear V CI HC R VE CE HE. 
  simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE. 
  simpl. apply TypeInt.
+ clear V CI HC R VE CE HE.
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv vsty. assumption.
  - apply TypeVar. assumption.
+ specialize (V _ _ _ H1) as IHv1. 
  specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE. simpl. apply TypePair; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE HE. apply TypeInl; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE HE. apply TypeInr; eauto.
+ specialize (CI _ _ _ H1) as IHc. 
  specialize (V _ _ _ vsty) as IHvs.
  clear V CI HC R VE CE HE. simpl.
  apply TypeFun. eapply IHc. eauto. inv H0. apply v_shift_typesafe; auto.
+ specialize (HC _ _ _ _ H2) as IHh. 
  specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE HE. simpl. apply TypeHandler; eauto. eapply IHc. 
  exact gets. inv H0. inv H6. apply v_shift_typesafe; assumption.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE. eapply TypeVSubtype; eauto.
}{
intros gets vsty. apply TypeC; inv orig.
assumption. assumption. destruct H1.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE HE. apply TypeRet; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE HE. apply TypeAbsurd; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply TypeΠMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply TypeΣMatch. eauto.
  - eapply IHc1. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
  - eapply IHc2. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply TypeDoBind. eauto.
  eapply IHc2. exact gets. inv H1. inv H4. apply v_shift_typesafe; auto. 
+ specialize (V _ _ _ H1) as IHv. 
  specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE HE. simpl. eapply TypeApp; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply TypeHandle; eauto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply TypeLetRec.
  - eapply IHc1. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. exact gets. inv H1. inv H3. apply v_shift_typesafe; auto.
+ specialize (V _ _ _ H2) as IHv. 
  specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H3. inv H4. apply v_shift_typesafe; auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE. eapply TypeCSubtype; eauto.
}{
intros gets vsty; simpl; apply TypeH; inv orig.
all: try assumption.
destruct H2.
+ clear V CI HC R VE CE HE. 
  apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. 
  specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE. simpl. apply TypeCasesU; eauto.
  - rewrite sub_find_None; auto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfTyFun; assumption.
}{
intros htys gets vsty; simpl. apply Respects; inv orig.
all: try assumption.
destruct H3.
+ clear V CI HC R VE CE HE. 
  apply RespectEqsØ.
+ specialize (CE _ _ _ _ H4) as IHc. 
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE HE.
  apply RespectEqsU. eauto. erewrite handle_t_sub. erewrite handle_t_sub.
  eapply IHc. all: inv H2; eauto. clear IHc IHr.
  * erewrite <-get_join_ctx_tctx, <-get_join_ctxs. eauto.
  * eapply v_join_all_ctxs_typesafe; auto.
}{
intros gets vsty. apply Veq.
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H3.
+ clear V CI HC R VE CE HE. apply VeqRefl. f_equal. assumption.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. apply VeqSym. eauto.
+ specialize (VE _ _ _ _ H3) as IH1.
  specialize (VE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE. subst. simpl.
  destruct (j =? i) eqn:cmp.
  - eapply VeqRefl. reflexivity.
  - eapply VeqVar; eauto.
+ clear V CI HC R VE CE HE. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE. simpl. apply VeqInt. auto.
+ specialize (VE _ _ _ _ H3) as IH1.
  specialize (VE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. simpl. apply VeqPair; eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqInr; eauto.
+ specialize (CE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. eapply VeqFun. eapply IH.
  - simpl. eauto.
  - inv H. apply v_shift_typesafe; auto.
+ specialize (CE _ _ _ _ H3) as IHc.
  specialize (HE _ _ _ _ _ H4) as IHh.
  clear V CI HC R VE CE HE. simpl. eapply VeqHandler; eauto. eapply IHc.
  - simpl. eauto.
  - inv H. inv H7. apply v_shift_typesafe; auto.
+ clear V CI HC R VE CE HE. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE. simpl. rewrite <-v_shift_sub. apply ηFun. omega.
}{
intros gets vtys. apply Ceq.
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H3.
+ clear V CI HC R VE CE HE. apply CeqRefl. f_equal. assumption.
+ specialize (CE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. apply CeqSym. eauto.
+ specialize (CE _ _ _ _ H3) as IH1.
  specialize (CE _ _ _ _ H4) as IH2.
  clear V CI HC R VE CE HE. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqRet. eauto.
+ specialize (VE _ _ _ _ H3) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqAbsurd. eauto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqΠMatch. eauto. eapply IHc.
  - simpl. eauto.
  - inv H3. inv H5. rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe; auto. apply v_shift_typesafe; auto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc1.
  specialize (CE _ _ _ _ H5) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply CeqΣMatch. eauto. all: inv H3; inv H6.
  - eapply IHc1. simpl. eauto. apply v_shift_typesafe; assumption.
  - eapply IHc2. simpl. eauto. apply v_shift_typesafe; assumption.
+ specialize (CE _ _ _ _ H3) as IHc1.
  specialize (CE _ _ _ _ H4) as IHc2.
  clear V CI HC R VE CE HE. simpl. eapply CeqDoBind. eauto. eapply IHc2.
  - simpl. eauto.
  - inv H3. inv H5. apply v_shift_typesafe; assumption.
+ specialize (VE _ _ _ _ H3) as IHv1.
  specialize (VE _ _ _ _ H4) as IHv2.
  clear V CI HC R VE CE HE. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ H3) as IHv.
  specialize (CE _ _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqHandle; eauto.
+ specialize (CE _ _ _ _ H3) as IHc1.
  specialize (CE _ _ _ _ H4) as IHc2.
  clear V CI HC R VE CE HE. simpl. inv H4. inv H6. eapply CeqLetRec.
  - eapply IHc1. simpl. eauto. rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe; auto. inv H12. apply v_shift_typesafe; auto.
  - eapply IHc2. simpl. eauto. apply v_shift_typesafe; assumption.
+ specialize (VE _ _ _ _ H4) as IHv.
  specialize (CE _ _ _ _ H5) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqOp; eauto.
  eapply IHc. simpl. eauto. apply v_shift_typesafe. assumption.
  apply get_op_type_wf in H3. destruct H3. assumption. inv H. assumption.
+ clear V CI HC R VE CE HE. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  simpl. rewrite v_shift_comm, <-c_shift_sub, v_shift_shift. 
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βDoBind_Op as rule.
  simpl. rewrite v_shift_comm, <-c_shift_sub. 
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  simpl. rewrite v_shift_comm, <-c_shift_sub, <-h_shift_sub.
  simpl in rule. eapply rule. apply sub_find_Some. eauto. all: omega.
}{
intros gets vtys. apply Heq.
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H4.
+ clear V CI HC R VE CE HE. apply HeqRefl. f_equal. assumption.
+ specialize (HE _ _ _ _ _ H4) as IH.
  clear V CI HC R VE CE HE. apply HeqSym. eauto.
+ specialize (HE _ _ _ _ _ H4) as IH1.
  specialize (HE _ _ _ _ _ H5) as IH2.
  clear V CI HC R VE CE HE. eapply HeqTrans; eauto.
+ clear V CI HC R VE CE HE. eapply HeqSigØ.
+ specialize (CE _ _ _ _ H6) as IH1.
  specialize (HE _ _ _ _ _ H7) as IH2.
  clear V CI HC R VE CE HE. eapply HeqSigU.
  - eapply sub_find_Some in H4. eauto.
  - eapply sub_find_Some in H5. eauto.
  - eapply IH1. simpl. eauto. 
    rewrite <-(v_shift_shift 1 1). eapply v_shift_typesafe. 
    eapply v_shift_typesafe. all: inv H. 2 : apply WfTyFun. all: auto.
  - eauto.
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
  ceq C Γ (c_subs c1 v_s i) (c_subs c2 v_s i)

with heq_subs_typesafe
  Γ Γ' Σ D h1 h2 i v_s A_s (orig: heq Σ D Γ' h1 h2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h1 v_s i) (h_subs h2 v_s i).

Proof.
all: rename v_subs_typesafe into V; rename c_subs_typesafe into CI.
all: rename h_subs_typesafe into HC; rename respects_subs_typesafe into R.
all: rename veq_subs_typesafe into VE; rename ceq_subs_typesafe into CE.
all: rename heq_subs_typesafe into HE.
{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear V CI HC R VE CE HE. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInt.
+ clear V CI HC R VE CE HE. 
  apply TypeV; auto; unfold v_subs; simpl. destruct (n=?i) eqn:ni.
  - apply Nat.eqb_eq in ni. subst.
    rewrite v_negshift_shift, v_shift_0. erewrite get_ctx_insert_new in H1.
    inv tyvs. inv H1. assumption. auto. omega.
  - subst. simpl. destruct (i<=?n) eqn:cmp; apply TypeVar.
    * erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. omega.
+ specialize (V Γ Γ0 v1 _ i _ _ H1 tyvs geq) as IH1.
  specialize (V Γ Γ0 v2 _ i _ _ H2 tyvs geq) as IH2.
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypePair; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInl; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInr; auto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  inv H0. specialize (v_shift_typesafe _ Γ A _ tyvs H5) as tyvs'.
  specialize (CI _ _ c _ (1+i) _ _ H1 tyvs') as IH. 
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. apply WfTyFun; auto. apply TypeFun. 
  rewrite v_shift_comm. apply IH. simpl. f_equal. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; inv H7; assumption).
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (CI _ _ c_ret _ (1+i) _ _ H1 tyvs' H4) as IHc. 
  specialize (HC _ _ h _ _ i _ _ H2 tyvs geq) as IHh. 
  specialize (R _ _ h _ _ _ i _ _ H3 H2 tyvs) as IHr.
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeHandler. 
  rewrite v_shift_comm. apply IHc. simpl. omega. omega. auto. auto.
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE.
  apply TypeV; auto; unfold v_subs; simpl. 
  eapply TypeVSubtype; eauto.
}{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1. 
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeRet. auto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeAbsurd. auto.
+ assert (CtxU (CtxU Γ0 A) B = ctx_insert (CtxU (CtxU Γ A) B) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (V _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CI _ _ c _ (2+i) _ _ H2 tyvs'' H3) as IHc.
  clear V CI HC R VE CE HE.
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
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeΣMatch. eauto. 
  - rewrite v_shift_comm. apply IHc1. simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)) as geqa.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (CI _ _ c1 _ i _ _ H1 tyvs geq) as IHc1.
  specialize (CI _ _ c2 _ (1+i) _ _ H2 tyvsa geqa) as IHc2.
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeDoBind. eauto. 
  rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ specialize (V _ _ v1 _ i _ _ H1 tyvs) as IH1.
  specialize (V _ _ v2 _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeApp. eauto. eauto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IHv.
  specialize (CI _ _ c _ i _ _ H2 tyvs) as IHc.
  clear V CI HC R VE CE HE.
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
  clear V CI HC R VE CE HE.
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
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CI Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubtype; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2. 
+ clear V CI HC R VE CE HE.
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
  clear V CI HC R VE CE HE.
  apply TypeH; auto; unfold h_subs; simpl. eapply TypeCasesU.
  - apply negshift_find_None. apply sub_find_None. assumption.
  - auto. 
  - rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
    simpl. omega. omega.
}{
intros tysh tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H3. 
+ clear V CI HC R VE CE HE.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ _ i v_s _ H3 tysh tyvs geq) as IHr.
  specialize (CE (join_ctx_tctx (join_ctxs Γ Γ') Z D) (join_ctx_tctx (join_ctxs Γ0 Γ') Z D) D (handle_t (ctx_len Γ') (tctx_len Z) h T1) (handle_t (ctx_len Γ') (tctx_len Z) h T2) (ctx_len Γ' + tctx_len Z + i) (Sub.v_shift v_s (ctx_len Γ' + tctx_len Z) 0) A_s H4) as IHc.
  all: clear V CI HC R VE CE HE.
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
intros tyvs geq len. apply Veq.
{ inv orig. assumption. }
{ inv tyvs. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H3.
+ clear V CI HC R VE CE HE. apply VeqRefl. f_equal. assumption.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. apply VeqSym. apply IH; auto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH1.
  specialize (VE _ _ _ _ _ i _ _ H4 tyvs) as IH2.
  clear V CI HC R VE CE HE. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE. subst. unfold v_subs. simpl.
  destruct (j =? i) eqn:cmp. 
  - rewrite v_negshift_shift, v_shift_0. eapply VeqRefl; eauto. omega.
  - simpl. destruct (i<=?j) eqn:ilj; eapply VeqVar; omega || eauto.
    * apply Nat.eqb_neq in cmp. apply leb_complete in ilj.
      erewrite get_ctx_insert_changed.
      assert (1+(j-1)=j) by omega. rewrite H3. eauto. omega. 
    * apply Nat.eqb_neq in cmp. apply leb_complete_conv in ilj.
      erewrite get_ctx_insert_unchanged. eauto. omega.
+ clear V CI HC R VE CE HE. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE. simpl. apply VeqInt. auto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH1.
  specialize (VE _ _ _ _ _ i _ _ H4 tyvs) as IH2.
  clear V CI HC R VE CE HE. unfold v_subs. simpl. apply VeqPair; auto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. unfold v_subs. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. unfold v_subs. simpl. eapply VeqInr; eauto.
+ assert (wf_vtype A) as wfa by (inv H; assumption).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (CE _ _ _ _ _ (S i) _ _ H3 tyvs') as IH.
  clear V CI HC R VE CE HE. unfold v_subs. simpl. eapply VeqFun.
  rewrite v_shift_comm. apply IH. simpl. f_equal. assumption.
  all: simpl; omega.
+ assert (wf_vtype A) as wfa by (inv H; inv H7; assumption).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (CE _ _ _ _ _ (S i) _ _ H3 tyvs') as IHc.
  specialize (HE _ _ _ _ _ _ i _ _ H4 tyvs) as IHh.
  clear V CI HC R VE CE HE. unfold v_subs. simpl. eapply VeqHandler; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. assumption.
  all: simpl; omega.
+ clear V CI HC R VE CE HE. unfold v_subs. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE. unfold v_subs. simpl.
  rewrite <-v_shift_sub, <-v_shift_negshift_comm. apply ηFun.
  apply v_sub_makes_no_var. apply v_shift_makes_no_var. omega. omega. 
}{
intros tyvs geq len. apply Ceq.
{ inv orig. assumption. }
{ inv tyvs. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H3.
+ clear V CI HC R VE CE HE. apply CeqRefl. f_equal. assumption.
+ specialize (CE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. apply CeqSym. eauto.
+ specialize (CE _ _ _ _ _ i _ _ H3 tyvs) as IH1.
  specialize (CE _ _ _ _ _ i _ _ H4 tyvs) as IH2.
  clear V CI HC R VE CE HE. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqRet. auto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IH.
  clear V CI HC R VE CE HE. simpl. apply CeqAbsurd. auto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H3; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H3; inv H5; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H4 tyvs'') as IHc.
  clear V CI HC R VE CE HE. unfold c_subs. simpl. eapply CeqΠMatch. auto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IHc.
  simpl. do 2 f_equal. assumption.
  simpl. omega. omega.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H3; inv H6; auto).
  assert (wf_vtype B) as wfb by (inv H3; inv H6; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CE _ _ _ _ _ (S i) _ _ H4 tyvsa) as IHc1.
  specialize (CE _ _ _ _ _ (S i) _ _ H5 tyvsb) as IHc2.
  clear V CI HC R VE CE HE. unfold c_subs. simpl. eapply CeqΣMatch. auto.
  all: rewrite v_shift_comm; omega || apply IHc1 || apply IHc2.
  all: simpl; try omega; f_equal; assumption.
+ assert (wf_vtype B) as wfb by (inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CE _ _ _ _ _ i _ _ H3 tyvs) as IHc1.
  specialize (CE _ _ _ _ _ (S i) _ _ H4 tyvsb) as IHc2.
  clear V CI HC R VE CE HE. unfold c_subs. simpl. eapply CeqDoBind. eauto.
  rewrite v_shift_comm. apply IHc2. simpl.  f_equal. assumption.
  simpl. omega. omega.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IHv1.
  specialize (VE _ _ _ _ _ i _ _ H4 tyvs) as IHv2.
  clear V CI HC R VE CE HE. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H3 tyvs) as IHv.
  specialize (CE _ _ _ _ _ i _ _ H4 tyvs) as IHc.
  clear V CI HC R VE CE HE. simpl. eapply CeqHandle; eauto.
+ assert (wf_vtype A) as wfa by (inv H4; inv H6; inv H12; auto).
  assert (wf_vtype (TyFun A C)) as wff by (inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' wff) as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs wff) as tyvs'''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H3 tyvs'') as IHc1.
  specialize (CE _ _ _ _ _ (1+i) _ _ H4 tyvs''') as IHc2.
  clear V CI HC R VE CE HE. unfold c_subs. simpl. eapply CeqLetRec.
  all: rewrite v_shift_comm; omega || auto.
  - rewrite <-(v_shift_shift 1 1). eapply IHc1. simpl. do 2 f_equal. auto.
    simpl. omega.
  - apply IHc2. simpl. f_equal. auto. simpl. omega.
+ assert (wf_vtype B_op) as wfb by (inv H5; inv H7; auto).
  specialize (v_shift_typesafe _ _ B_op _ tyvs wfb) as tyvsb.
  specialize (VE _ _ _ _ _ i _ _ H4 tyvs) as IHv.
  specialize (CE _ _ _ _ _ (S i) _ _ H5 tyvsb) as IHc.
  clear V CI HC R VE CE HE. unfold c_subs. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. auto. simpl. omega. omega.
+ clear V CI HC R VE CE HE. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ΠMatch (Pair v1 v2) x y c) v_s i 
    = ΠMatch (Pair (v_subs v1 v_s i) (v_subs v2 v_s i)) 
        x y (c_subs c (Sub.v_shift v_s 2 0) (2+i))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm. reflexivity. omega. }  
  rewrite H3. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inl v) xl cl xr cr) v_s i 
    = ΣMatch (Inl (v_subs v v_s i)) 
        xl (c_subs cl (Sub.v_shift v_s 1 0) (1+i))
        xr (c_subs cr (Sub.v_shift v_s 1 0) (1+i))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H3. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inr v) xl cl xr cr) v_s i 
    = ΣMatch (Inr (v_subs v v_s i)) 
        xl (c_subs cl (Sub.v_shift v_s 1 0) (1+i))
        xr (c_subs cr (Sub.v_shift v_s 1 0) (1+i))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H3. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (App (Fun x c) v) v_s i 
    = App (Fun x (c_subs c (Sub.v_shift v_s 1 0) (1+i))) (v_subs v v_s i)).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H3. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (LetRec f x c1 c2) v_s i
    = LetRec f x (c_subs c1 (Sub.v_shift v_s 2 0) (2 + i))
        (c_subs c2 (Sub.v_shift v_s 1 0) (1 + i))).
  { unfold c_subs. simpl. do 2 f_equal; rewrite v_shift_comm; auto || omega. }  
  rewrite H3. clear H3.
  assert ( v_subs (Fun x (LetRec f x (Sub.c_shift c1 1 2) c1)) v_s i
    = Fun x (LetRec f x
       (Sub.c_shift (c_subs c1 (Sub.v_shift v_s 2 0) (2 + i)) 1 2)
       (c_subs c1 (Sub.v_shift v_s 2 0) (2 + i))) ).
  { unfold c_subs. unfold v_subs. simpl. do 2 f_equal.
    rewrite v_shift_comm, <-c_shift_sub, c_shift_negshift_comm.
    do 2 f_equal. rewrite v_shift_comm. auto. omega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var. all: try omega.
    do 3 f_equal. rewrite v_shift_shift, v_shift_comm; auto || omega. }
  rewrite H3. clear H3. apply rule. omega.  
+ clear V CI HC R VE CE HE. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (DoBind x (Ret v) c) v_s i 
    = DoBind x (Ret (v_subs v v_s i)) (c_subs c (Sub.v_shift v_s 1 0) (1+i))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H3. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βDoBind_Op as rule.
  unfold c_subs_out in *. unfold c_subs. simpl. rewrite v_shift_comm. 
  specialize (rule x op_id 
    (Sub.v_negshift (Sub.v_sub v_arg (i, Sub.v_shift v_s 1 i)) 1 i) y
    (Sub.c_negshift
      (Sub.c_sub c1 (S i, Sub.v_shift (Sub.v_shift v_s 1 0) 1 (1 + i)))
      1 (S i))
    (Sub.c_negshift
      (Sub.c_sub c2 (S i, Sub.v_shift (Sub.v_shift v_s 1 0) 1 (1 + i))) 1
      (S i))).
  rewrite c_shift_negshift_comm, c_shift_sub in rule. simpl.
  assert (Sub.v_shift (Sub.v_shift (Sub.v_shift v_s 1 0) 1 (S i)) 1 0
    = Sub.v_shift (Sub.v_shift (Sub.v_shift v_s 1 0) 1 (S i)) 1 1).
  { rewrite <-v_shift_comm, v_shift_comm. all: omega || auto. }
  rewrite H3. apply rule. all: try omega. clear rule.
  apply c_sub_makes_no_var. apply v_shift_makes_no_var.
+ clear V CI HC R VE CE HE. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (Handle (Handler x c_r h) (Ret v)) v_s i
    = Handle (Handler x 
      (c_subs c_r (Sub.v_shift v_s 1 0) (1+i)) (h_subs h v_s i)) 
      (Ret (v_subs v v_s i) ) ).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H3. apply rule. all: omega.
+ clear V CI HC R VE CE HE. specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (Handle (Handler x c_r h) (Op op_id v_arg y c_k)) v_s i =
    Handle (Handler x (c_subs c_r (Sub.v_shift v_s 1 0) (1+i)) (h_subs h v_s i))
    (Op op_id (v_subs v_arg v_s i) y (c_subs c_k (Sub.v_shift v_s 1 0) (1+i)))).
  { unfold c_subs. unfold v_subs. simpl. do 5 f_equal;
    apply v_shift_comm; omega. }
  rewrite H4. clear H4.
  assert (v_subs (Fun y
    (Handle (Handler x (Sub.c_shift c_r 1 1) (Sub.h_shift h 1 0)) c_k)) v_s i
  = Fun y (Handle (Sub.v_shift (Handler x (c_subs c_r (Sub.v_shift v_s 1 0) (1+i)) (h_subs h v_s i)) 1 0) (c_subs c_k (Sub.v_shift v_s 1 0) (1+i)))).
  { clear rule. unfold v_subs. unfold c_subs. unfold h_subs. 
    simpl. do 3 f_equal.
    rewrite c_shift_negshift_comm, c_shift_sub. do 3 f_equal.
    rewrite v_shift_comm. f_equal. apply v_shift_comm. all: try omega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite h_shift_negshift_comm, h_shift_sub. f_equal. omega.
    apply h_sub_makes_no_var. apply v_shift_makes_no_var. omega.
    rewrite v_shift_comm. reflexivity. omega. }
  rewrite H4, v_shift_shift, <-v_shift_subs_alt. clear H4. simpl.
  eapply rule. unfold h_subs. 
  apply negshift_find_Some. rewrite <-(v_shift_comm 1 i 0). 
  apply sub_find_Some. eauto. all: omega.
}{
intros tyvs geq len. apply Heq.
{ inv orig. assumption. }
{ inv orig. assumption. }
{ inv tyvs. assumption. }
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H4.
+ clear V CI HC R VE CE HE. apply HeqRefl. f_equal. assumption.
+ specialize (HE _ _ _ _ _ _ i _ _ H4 tyvs) as IH.
  clear V CI HC R VE CE HE. apply HeqSym. eauto.
+ specialize (HE _ _ _ _ _ _ i _ _ H4 tyvs) as IH1.
  specialize (HE _ _ _ _ _ _ i _ _ H5 tyvs) as IH2.
  clear V CI HC R VE CE HE. eapply HeqTrans; eauto.
+ clear V CI HC R VE CE HE. eapply HeqSigØ.
+ assert (wf_vtype A) as wfa by (inv H; auto).
  assert (wf_vtype (TyFun B D)) as wff by (inv H6; inv H9; inv H14; auto).    
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs wff) as tyvs'.
  specialize (v_shift_typesafe _ _ A _ tyvs' wfa) as tyvs''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H6 tyvs'') as IH1.
  specialize (HE _ _ _ _ _ _ i _ _ H7 tyvs) as IH2.
  clear V CI HC R VE CE HE. eapply HeqSigU.
  - unfold h_subs. eapply negshift_find_Some. eapply sub_find_Some. eauto.
  - unfold h_subs. eapply negshift_find_Some. eapply sub_find_Some. eauto.
  - rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IH1.
    simpl. do 2 f_equal. assumption. simpl. omega. omega.
  - eauto.
}
Qed.