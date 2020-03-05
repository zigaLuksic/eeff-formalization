Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic". *)

Require Export subtyping_lemmas substitution_lemmas logic_aux_lemmas.

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
all: try constructor; eauto. eapply ctx_len_get_Some. eauto.
all: assert (S (ctx_len Γ) = ctx_len (CtxU Γ A)) as cA by (simpl; reflexivity).
all: rewrite cA; eauto.
}{
intro types. destruct types. destruct H1; simpl.
all: try constructor; try constructor; try eauto.
all: assert (forall A Γ, S(ctx_len Γ) = ctx_len (CtxU Γ A)) as ext by auto.
all: erewrite ext; eauto; erewrite ext; eauto.
}{
intro types. destruct types. destruct H2; simpl. auto. constructor; eauto.
assert (S(S(ctx_len Γ)) = ctx_len(CtxU(CtxU Γ (TyFun Bop D)) Aop)) by auto.
rewrite H5. eauto.
}
Admitted.


Lemma wf_is_under_ctx_tctx Γ Z T Σ:
  wf_t Γ Z T Σ -> 
  t_under_var T (ctx_len Γ) /\ t_under_tvar T (tctx_len Z).
Proof.
revert Γ. induction T; intros Γ wf.
+ inv wf. simpl. constructor.
  - eapply has_vtype_is_under_ctx. eauto.
  - apply tctx_len_get_Some in H5. omega.
+ inv wf. simpl. constructor. 2: auto.
  eapply has_vtype_is_under_ctx. eauto.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT in H5; destruct H5; assumption.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT1 in H6; apply IHT2 in H7; destruct H6; destruct H7; auto.
+ inv wf. simpl. constructor. 2: constructor. constructor. 2: constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT1 in H6 as IH1; destruct IH1; auto.
  all: apply IHT2 in H7 as IH2; destruct IH2; auto.
+ inv wf. simpl. constructor. constructor.
  eapply has_ctype_is_under_ctx. eauto.
  all: apply IHT in H5; destruct H5; auto.
+ inv wf. simpl. constructor. constructor.
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT in H7; destruct H7; assumption.
Admitted.


Lemma handle_t_no_var h i Γ Z T Σ:
  h_no_var h i -> wf_t Γ Z T Σ ->
  c_no_var 
    (handle_t (ctx_len Γ) (tctx_len Z) h T)
    (i + tctx_len Z + ctx_len Γ).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ constructor.
  all: apply wf_is_under_ctx_tctx in H0; destruct H0; simpl in *.
  omega. eapply v_under_var_no_var; eaomega.
+ apply wf_is_under_ctx_tctx in H0. destruct H0.
  eapply v_under_var_no_var; eaomega.
+ constructor; inv H0.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
  - rewrite slen, slen, (sctx A), (sctx B). eauto.
+ inv H0. constructor. 2: constructor.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
  - rewrite slen, (sctx A). auto. 
  - rewrite slen, (sctx B). auto. 
+ inv H0. constructor. 2: aconstructor.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ inv H0. constructor.
  - eapply c_under_var_no_var. eapply has_ctype_is_under_ctx. all: eaomega.
  - rewrite slen, (sctx A). auto.
+ destruct (get_case h o) eqn:finds; inv H0.
  - unfold c_subs2_out. unfold c_subs_out. 
    apply c_no_var_subs. apply c_no_var_subs. all: omega || simpl.
    * eapply get_case_no_var in finds; eauto.
      assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+(2+i)).
      omega. rewrite H0. apply c_no_var_shift; eaomega.
    * apply v_no_var_shift. eapply v_under_var_no_var.
      eapply has_vtype_is_under_ctx. all: eaomega.
    * rewrite slen, (sctx Bop). eauto.
  - simpl. constructor.
    * eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
    * rewrite slen, (sctx Bop). eauto.
Admitted.


Lemma handle_t_under_var h i Γ Z T Σ:
  h_under_var h i -> wf_t Γ Z T Σ ->
  c_under_var (handle_t (ctx_len Γ) (tctx_len Z) h T) 
    (i + tctx_len Z + ctx_len Γ).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ constructor.
  all: apply wf_is_under_ctx_tctx in H0; destruct H0; simpl in *. 
  omega. eapply v_under_var_weaken; eaomega.
+ apply wf_is_under_ctx_tctx in H0. destruct H0.
  eapply v_under_var_weaken; eaomega.
+ constructor; inv H0.
  - eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
  - rewrite slen, slen, (sctx A), (sctx B). eauto.
+ inv H0. constructor. 2: constructor.
  - eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
  - rewrite slen, (sctx A). auto. 
  - rewrite slen, (sctx B). auto. 
+ inv H0. constructor. 2: aconstructor.
  - eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ inv H0. constructor.
  - eapply c_under_var_weaken. eapply has_ctype_is_under_ctx. all: eaomega.
  - rewrite slen, (sctx A). auto.
+ destruct (get_case h o) eqn:finds; inv H0.
  - apply c_under_var_subs. apply c_under_var_subs. all: omega || simpl.
    * eapply get_case_under_var in finds; eauto.
      assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+(2+i)).
      omega. rewrite H0. apply c_under_var_shift; eaomega.
    * apply v_under_var_shift. eapply v_under_var_weaken.
      eapply has_vtype_is_under_ctx. all: eaomega.
    * rewrite slen, (sctx Bop). eauto.
  - simpl. constructor.
    * eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
    * rewrite slen, (sctx Bop). eauto.
Admitted.

(* ==================== Handling and Shifts. ==================== *)

Lemma handle_t_shift Γ' Γ Z h T Σ D i:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (h_shift h 1 i) T
  = c_shift 
      (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + tctx_len Z + ctx_len Γ).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ simpl. apply tctx_len_get_Some in H5 as zlen. 
  destruct ((i + tctx_len Z + ctx_len Γ) <=? ctx_len Γ + n) eqn:cmp.
  { apply leb_complete in cmp. omega. }
  f_equal. rewrite v_shift_too_high. auto.
  eapply has_vtype_is_under_ctx in H3.  
  eapply v_under_var_weaken; eaomega.
+ f_equal. rewrite v_shift_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken; eaomega.
+ f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken; eaomega.
  - rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - rewrite slen, (sctx A). auto.
  - rewrite slen, (sctx B). auto.
+ f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - auto.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ f_equal.
  - rewrite c_shift_too_high. auto.
    apply has_ctype_is_under_ctx in H3.
    eapply c_under_var_weaken; eaomega.
  - rewrite slen, (sctx A). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  erewrite shift_get_case_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_shift_subs. 2: omega. f_equal; simpl. 
  * rewrite c_shift_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+tctx_len Z+ctx_len Γ))=(tctx_len Z+ctx_len Γ)+S(S i))
    as cext by omega. rewrite cext.
    rewrite c_shift_comm. f_equal. omega. omega.
    rewrite (v_shift_too_high (v_shift v 1 0)). auto.
    apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_weaken. all: eaomega. 
  * f_equal. rewrite slen, (sctx Bop). auto. 
Admitted.


Lemma handle_t_negshift Γ' Γ Z h T Σ D i:
  h_no_var h i -> wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (h_negshift h 1 i) T
  = c_negshift 
      (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + tctx_len Z + ctx_len Γ).
Proof.
revert Γ h i. induction T; intros Γ h i novar wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ apply tctx_len_get_Some in H5 as zlen. simpl.
  destruct ((i + tctx_len Z + ctx_len Γ) <=? ctx_len Γ + n) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. rewrite v_negshift_too_high. auto.
    eapply has_vtype_is_under_ctx in H3.  
    eapply v_under_var_weaken; eaomega.
+ f_equal. rewrite v_negshift_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken; eaomega.
+ f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken; eaomega.
  - rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - rewrite slen, (sctx A). auto.
  - rewrite slen, (sctx B). auto.
+ f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - auto.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ f_equal.
  - rewrite c_negshift_too_high. auto.
    apply has_ctype_is_under_ctx in H3.
    eapply c_under_var_weaken; eaomega.
  - rewrite slen, (sctx A). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+S(S i))
  as cext by omega.
  eapply get_case_no_var in find as cop_novar; eauto.
  erewrite negshift_get_case_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_negshift_subs. 2: omega. f_equal; simpl. 
  * rewrite c_negshift_subs. 2: omega. f_equal; simpl.
    rewrite cext, c_shift_negshift_comm. f_equal. auto. omega.
    rewrite v_negshift_too_high. auto.
    - apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
      eapply v_under_var_weaken. all: eaomega. 
    - simpl. rewrite cext. apply c_no_var_shift. eauto. omega.
    - apply v_no_var_shift. apply has_vtype_is_under_ctx in H6.
      eapply v_under_var_no_var. all: eaomega. 
  * f_equal. rewrite slen, (sctx Bop). auto.
  * apply c_no_var_subs. simpl. rewrite cext.
    apply c_no_var_shift; eaomega. 
    apply v_no_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_no_var. all: eaomega.
  * simpl. rewrite slen, (sctx Bop). eapply handle_t_no_var; eauto.
Admitted.


Lemma handle_t_sub Γ' Γ Z h T Σ D i v_s:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D ->
    handle_t (ctx_len Γ) (tctx_len Z) (h_sub h (i, v_s)) T
  = c_sub 
      (handle_t (ctx_len Γ) (tctx_len Z) h T)
      (i+tctx_len Z+ctx_len Γ, v_shift v_s (tctx_len Z+ctx_len Γ) 0).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ apply tctx_len_get_Some in H5 as zlen. simpl.
  destruct (ctx_len Γ + n =? i + tctx_len Z + ctx_len Γ) eqn:cmp.
  - apply Nat.eqb_eq in cmp. omega.
  - f_equal. rewrite v_sub_too_high. auto.
    eapply has_vtype_is_under_ctx in H3. 
    eapply v_under_var_weaken; eaomega.
+ f_equal. rewrite v_sub_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken; eaomega.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken; eaomega.
  - assert (tctx_len Z + ctx_len Γ + 2 = tctx_len Z + S(S(ctx_len Γ))) as same.
    omega. rewrite v_shift_shift, same.
    rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. rewrite v_shift_shift, same, slen, (sctx A). auto.
  - assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. rewrite v_shift_shift, same, slen, (sctx B). auto.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken; eaomega.
  - auto.
  - assert (tctx_len Z + ctx_len Γ + 2 = tctx_len Z + S(S(ctx_len Γ))) as same.
    omega. rewrite v_shift_shift, same.
    rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ f_equal.
  - rewrite c_sub_too_high. auto.
    apply has_ctype_is_under_ctx in H3.
    eapply c_under_var_weaken; eaomega.
  - assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. rewrite v_shift_shift, same.
    rewrite slen, (sctx A). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  erewrite sub_get_case_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_sub_subs. 2: omega. f_equal; simpl. 
  * rewrite c_sub_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+S(S i))
    as cext by omega. rewrite cext.
    rewrite c_shift_sub, v_shift_shift. do 2 f_equal. simpl.
    rewrite (v_shift_comm _ _ 0). f_equal. all: try omega.
    rewrite v_sub_too_high. auto.
    apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_weaken. all: eaomega. 
  * assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. f_equal. rewrite v_shift_shift, same, slen, (sctx Bop). auto.
Admitted.


(* ==================== Safety and Shifts. ==================== *)

Fixpoint v_insert_typesafe 
  Γ v A (orig : has_vtype Γ v A) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_vtype (ctx_insert Γ i A_ins) (v_shift v 1 i) A

with c_insert_typesafe 
  Γ c C (orig : has_ctype Γ c C) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_ctype (ctx_insert Γ i A_ins) (c_shift c 1 i) C

with h_insert_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_htype (ctx_insert Γ i A_ins) (h_shift h 1 i) Σ D

with respects_insert_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) A_ins i {struct orig} :
  has_htype Γ h Σ D -> wf_vtype A_ins ->
  respects (ctx_insert Γ i A_ins) (h_shift h 1 i) Σ D E

with judg_insert_typesafe
  Γ Ψ φ (orig: judg Γ Ψ φ) A_ins i {struct orig} :
  wf_vtype A_ins ->
  judg (ctx_insert Γ i A_ins) (hyp_shift Ψ 1 i) (form_shift φ 1 i)

with wf_hypotheses_insert_typesafe
  Γ Ψ (orig: wf_hypotheses Γ Ψ) A_ins i {struct orig} :
  wf_vtype A_ins ->
  wf_hypotheses (ctx_insert Γ i A_ins) (hyp_shift Ψ 1 i)

with wf_form_insert_typesafe
  Γ φ (orig: wf_formula Γ φ) A_ins i {struct orig} :
  wf_vtype A_ins ->
  wf_formula (ctx_insert Γ i A_ins) (form_shift φ 1 i)

with wf_inst_insert_typesafe
  Γ Γ' I (orig: wf_inst Γ I Γ') A_ins i {struct orig} : 
  wf_vtype A_ins ->
  wf_inst (ctx_insert Γ i A_ins) (inst_shift I 1 i) Γ'.

Proof.
all: rename v_insert_typesafe into VL; rename c_insert_typesafe into CL.
all: rename h_insert_typesafe into HL; rename respects_insert_typesafe into RL.
all: rename judg_insert_typesafe into JL.
all: rename wf_hypotheses_insert_typesafe into WFHL.
all: rename wf_form_insert_typesafe into WFFL.
all: rename wf_inst_insert_typesafe into WFIL.
{
intros wfins. apply TypeV.
{ apply wf_ctx_insert. inv orig. all: auto. }
{ inv orig. auto. }
inv orig. destruct H1.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeInt.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    auto. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    auto. apply leb_iff_conv in cmp. auto.
+ specialize (VL _ _ _ H1) as IHv1.
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypePair; auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeInl. auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeInr. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeListNil.
+ specialize (VL _ _ _ H1) as IHv1.
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeListCons; auto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (HL _ _ _ _ H2) as IHh.
  specialize (CL _ _ _ H1) as IHc.
  specialize (RL _ _ _ _ _ H3) as IHres.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeVSubtype; auto.
}{
intros wfins. apply TypeC.
{ apply wf_ctx_insert. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeRet. auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeAbsurd. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeΠMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeΣMatch. auto.
  all: rewrite ctx_insert_extend; auto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeListMatch; auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (CL _ _ _ H1) as IHc1.
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeDoBind. auto. rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (VL _ _ _ H2) as IHv0.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeApp; auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeHandle; auto.
+ specialize (CL _ _ _ H1) as IHc1.
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H2) as IHv.
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeOp. 3: rewrite ctx_insert_extend. all: eauto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeCSubtype; auto.
}{
intros wfins. apply TypeH.
{ apply wf_ctx_insert. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear VL CL HL RL JL WFHL WFFL WFIL. apply TypeCasesØ.
+ specialize (HL _ _ _ _ H3) as IHh.
  specialize (CL _ _ _ H4) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCasesU. 2: auto.
  - apply shift_get_case_None. assumption.
  - do 2 rewrite ctx_insert_extend. auto.
}{
intros types wfins. apply Respects.
{ clear VL CL HL RL JL WFHL WFFL WFIL. apply wf_ctx_insert. inv orig. all: auto. }
all: inv orig; auto.
destruct H3.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply RespectEqsØ.
+ specialize (RL _ _ _ _ _ H3) as IHres. specialize (JL _ _ _ H4) as IHeq.
  clear VL CL HL RL JL WFHL WFFL WFIL. apply RespectEqsU. auto.
  rewrite join_ctxs_insert, join_ctxs_insert.
  erewrite handle_t_shift. erewrite handle_t_shift.
  rewrite <-len_tctx_to_ctx.
  assert (ctx_len Γ+(tctx_len Z+i) = i+tctx_len Z+ctx_len Γ) by omega.
  rewrite H5. apply IHeq.
  all: inv H2. all: eauto.
}{
intros wfins. apply WfJudg.
{ destruct orig; eauto. }
{ destruct orig; eauto. }
destruct orig. destruct H1.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. eauto.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  subst. simpl. rename i0 into j.
  destruct (i <=? j) eqn:cmp; eapply VeqVar; eauto.
  - erewrite <-get_ctx_insert_changed. auto. apply leb_complete in cmp. auto.
  - erewrite <-get_ctx_insert_unchanged. auto. 
    apply leb_complete_conv in cmp. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqInt.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqPair; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqInl; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqInr; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
simpl. eapply VeqListNil.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqListCons; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqFun.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H1) as IHc.
  specialize (JL _ _ _ H2) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqHandler; eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. rewrite <-v_shift_comm. apply ηFun. omega.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd. eauto.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqΠMatch. eauto.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqΣMatch. eauto.
  all: rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqListMatch; eauto.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H1) as IHc1.
  specialize (JL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqDoBind. eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H1) as IHv1.
  specialize (JL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp; eauto.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle; eauto.
+ specialize (JL _ _ _ H1) as IHc1.
  specialize (JL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqLetRec.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqOp; eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (WFIL _ _ _ H2) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply OOTB; eauto.
  rewrite <-c_shift_inst. rewrite H3. simpl. auto.
  rewrite <-c_shift_inst. rewrite H4. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl. 
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Cons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  simpl. rewrite <-c_shift_comm. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl. rewrite <-c_shift_comm. 
  eapply βDoBind_Op. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  simpl. rewrite <-c_shift_comm, <-h_shift_comm.
  eapply rule. apply shift_get_case_Some. eauto. all: omega.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs, c_shift_subs. simpl.
    assert (S(S(S i))=2+(S i)) as same by omega.
    rewrite same, <-c_shift_comm. all: try omega.
    eapply ηPair. specialize (ctx_len_insert_trivial Γ i A_ins) as triv. omega.
    rewrite <-ctx_insert_comm; try omega. auto.  
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt, c_shift_subs_alt.
    assert (S(S i)=2+i) as samei by omega.
    assert (1+S(S n)=2+(S n)) as samen by omega.
    rewrite samei, samen, <-c_shift_comm. all: try omega.
    eapply ηPair. rewrite ctx_len_insert; omega.
    rewrite ctx_insert_comm; try omega. auto.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs, c_shift_subs, c_shift_subs. simpl.
    assert (S(S i)=1+(S i)) as same by omega.
    rewrite same, <-c_shift_comm. all: aomega.
    eapply ηSum. specialize (ctx_len_insert_trivial Γ i A_ins) as triv. omega.
    rewrite <-ctx_insert_comm; aomega.  
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt, c_shift_subs_alt, c_shift_subs_alt. simpl.
    rewrite <-c_shift_comm. all: aomega.
    eapply ηSum. rewrite ctx_len_insert; omega.
    rewrite ctx_insert_comm; aomega.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs, c_shift_subs, c_shift_subs. simpl.
    assert (S(S(S i))=2+(S i)) as same by omega.
    rewrite same, <-c_shift_comm. all: try omega.
    eapply ηList. specialize (ctx_len_insert_trivial Γ i A_ins) as triv. omega.
    rewrite <-ctx_insert_comm; try omega. auto.  
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt, c_shift_subs_alt, c_shift_subs_alt.
    assert (S(S i)=2+i) as samei by omega.
    assert (1+S(S n)=2+(S n)) as samen by omega.
    rewrite samei, samen, <-c_shift_comm. all: try omega.
    eapply ηList. rewrite ctx_len_insert; omega.
    rewrite ctx_insert_comm; try omega. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηDoBind.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigØ. 
+ specialize (JL _ _ _ H3) as IHc.
  specialize (JL _ _ _ H4) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigU.
  - eapply shift_get_case_Some in H1. eauto.
  - eapply shift_get_case_Some in H2. eauto.
  - rewrite ctx_insert_extend, ctx_insert_extend, hyp_shift_comm; eaomega.
  - eauto.
}{
intros wfins. inv orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply WfHypØ.
  apply wf_ctx_insert; auto.
+ specialize (WFHL _ _ H) as IHhy.
  specialize (WFFL _ _ H0) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfHypU; auto.
}{
intros wfins. inv orig.
+ specialize (VL _ _ _ H) as IHv1.
  specialize (VL _ _ _ H0) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfVeq; eauto.
+ specialize (CL _ _ _ H) as IHc1.
  specialize (CL _ _ _ H0) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfCeq; eauto.
+ specialize (HL _ _ _ _ H2) as IHh1.
  specialize (HL _ _ _ _ H3) as IHh2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply WfHeq. 2: exact H0. all: eauto.
}{
intros wfins. inv orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply WfInstØ.
  apply wf_ctx_insert; auto.
+ specialize (VL _ _ _ H) as IHv.
  specialize (WFIL _ _ _ H0) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstU; auto.
}
Admitted.

(* ==================== Shorter definitions ==================== *)

Fixpoint v_shift_typesafe v (Γ:ctx) A0 A :
  has_vtype Γ v A -> wf_vtype A0 ->
  has_vtype (CtxU Γ A0) (v_shift v 1 0) A

with c_shift_typesafe c (Γ:ctx) A0 C :
  has_ctype Γ c C -> wf_vtype A0 ->
  has_ctype (CtxU Γ A0) (c_shift c 1 0) C

with h_shift_typesafe h (Γ:ctx) A0 Σ D :
  has_htype Γ h Σ D -> wf_vtype A0 ->
  has_htype (CtxU Γ A0) (h_shift h 1 0) Σ D

with respects_shift_typesafe Γ h Σ D E A0 :
  respects Γ h Σ D E -> has_htype Γ h Σ D -> wf_vtype A0 ->
  respects (CtxU Γ A0) (h_shift h 1 0) Σ D E

with judg_shift_typesafe Γ Ψ φ A0 :
  judg Γ Ψ φ -> wf_vtype A0 ->
  judg (CtxU Γ A0) (hyp_shift Ψ 1 0) (form_shift φ 1 0)

with wf_hypotheses_shift_typesafe Γ Ψ A0 :
  wf_hypotheses Γ Ψ -> wf_vtype A0 ->
  wf_hypotheses (CtxU Γ A0) (hyp_shift Ψ 1 0)

with wf_form_shift_typesafe Γ φ A0 :
  wf_formula Γ φ -> wf_vtype A0 ->
  wf_formula (CtxU Γ A0) (form_shift φ 1 0)

with wf_inst_shift_typesafe Γ Γ' I A0 : 
  wf_inst Γ I Γ' -> wf_vtype A0 ->
  wf_inst (CtxU Γ A0) (inst_shift I 1 0) Γ'.

Proof.
all: intros orig;
assert (ctx_insert Γ 0 A0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H.
apply v_insert_typesafe. assumption.
apply c_insert_typesafe. assumption.
apply h_insert_typesafe. assumption.
apply respects_insert_typesafe. assumption.
apply judg_insert_typesafe. assumption.
apply wf_hypotheses_insert_typesafe. assumption.
apply wf_form_insert_typesafe. assumption.
apply wf_inst_insert_typesafe. assumption.
Admitted.


Lemma v_join_ctxs_typesafe_left Γ Γ' v A :
  has_vtype Γ v A -> wf_ctx Γ' -> 
  has_vtype (join_ctxs Γ Γ') (v_shift v (ctx_len Γ') 0) A.
Proof.
intros; induction Γ'; simpl.
+ rewrite v_shift_0. assumption.
+ assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H1.
  rewrite <-v_shift_shift. apply v_shift_typesafe; inv H0; auto.
Admitted.


Lemma c_join_ctxs_typesafe_left Γ Γ' c C :
  has_ctype Γ c C -> wf_ctx Γ' -> 
  has_ctype (join_ctxs Γ Γ') (c_shift c (ctx_len Γ') 0) C.
Proof.
intros; induction Γ'; simpl.
+ rewrite c_shift_0. assumption.
+ assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H1.
  rewrite <-c_shift_shift. apply c_shift_typesafe; inv H0; auto.
Admitted.


Fixpoint v_join_ctxs_typesafe_right Γ Γ' v A {struct Γ'}:
  has_vtype Γ v A -> wf_ctx Γ' -> 
  has_vtype (join_ctxs Γ' Γ) v A.
Proof.
intros; destruct Γ'; simpl.
+ rewrite join_ctxs_CtxØ. assumption.
+ rewrite join_ctxs_CtxU.
  apply v_join_ctxs_typesafe_right. 
  rewrite <-(v_shift_too_high _ 1 (ctx_len Γ)).
  apply v_insert_typesafe. auto. inv H0. auto.
  eapply has_vtype_is_under_ctx. eauto. inv H0. auto.
Admitted.


Fixpoint c_join_ctxs_typesafe_right Γ Γ' c C {struct Γ'}:
  has_ctype Γ c C -> wf_ctx Γ' -> 
  has_ctype (join_ctxs Γ' Γ) c C.
Proof.
intros; destruct Γ'; simpl.
+ rewrite join_ctxs_CtxØ. assumption.
+ rewrite join_ctxs_CtxU.
  apply c_join_ctxs_typesafe_right. 
  rewrite <-(c_shift_too_high _ 1 (ctx_len Γ)).
  apply c_insert_typesafe. auto. inv H0. auto.
  eapply has_ctype_is_under_ctx. eauto. inv H0. auto.
Admitted.


Lemma v_join_all_ctxs_typesafe Γ Γ' Z D v A :
  has_vtype Γ' v A -> wf_ctx Γ -> wf_tctx Z -> wf_ctype D ->
  has_vtype 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (v_shift v (tctx_len Z+ctx_len Γ) 0) A.
Proof.
intros. 
rewrite <-v_shift_shift.
apply v_join_ctxs_typesafe_left; auto.
erewrite len_tctx_to_ctx. apply v_join_ctxs_typesafe_left. auto.
apply wf_tctx_to_ctx; auto.
Admitted.


Lemma c_join_all_ctxs_typesafe Γ Γ' Z D c C :
  has_ctype Γ' c C -> wf_ctx Γ -> wf_tctx Z -> wf_ctype D ->
  has_ctype 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (c_shift c (tctx_len Z+ctx_len Γ) 0) C.
Proof.
intros. 
rewrite <-c_shift_shift.
apply c_join_ctxs_typesafe_left; auto.
erewrite len_tctx_to_ctx. apply c_join_ctxs_typesafe_left. auto.
apply wf_tctx_to_ctx; auto.
Admitted.

(* ==================== Hypotheses weakening. ==================== *)

Fixpoint hypotheses_weakening Γ Ψ φ (orig: judg Γ Ψ φ) Ψ' {struct orig}:
  wf_hypotheses Γ Ψ' -> hyp_subset Ψ Ψ' -> judg Γ Ψ' φ.
Proof.
intros wfh subset.
apply WfJudg. destruct orig. auto. auto.
destruct orig. destruct H1.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply VeqVar; eauto.
+ apply VeqUnit.
+ apply VeqInt.
+ apply VeqPair; eauto.
+ apply VeqInl. eauto.
+ apply VeqInr. eauto.
+ apply VeqListNil. 
+ apply VeqListCons; eauto.
+ apply VeqFun. eapply hypotheses_weakening. eauto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H1. apply wf_hyp_ctx in H3. inv H3. auto.
  - apply hyp_subset_shift. auto.
+ eapply VeqHandler; eauto. eapply hypotheses_weakening. eauto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H1. apply wf_hyp_ctx in H5. inv H5. auto.
  - apply hyp_subset_shift. auto.
+ apply ηUnit.
+ apply ηFun.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto.
+ eapply CeqΠMatch; eauto.
  eapply hypotheses_weakening. eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hypotheses_shift_typesafe; auto.
    apply wf_hypotheses_shift_typesafe; auto.
    all: inv H2; apply wf_hyp_ctx in H4; inv H4. inv H7. auto. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqΣMatch; eauto.
  all: eapply hypotheses_weakening; eauto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H2. apply wf_hyp_ctx in H5. inv H5. auto.
  - apply hyp_subset_shift. auto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H3. apply wf_hyp_ctx in H5. inv H5. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqListMatch; eauto.
  eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hypotheses_shift_typesafe; auto.
    apply wf_hypotheses_shift_typesafe; auto.
    all: inv H3; apply wf_hyp_ctx in H5; inv H5. inv H9. auto. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqDoBind; eauto.
  eapply hypotheses_weakening. eauto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H2. apply wf_hyp_ctx in H4. inv H4. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec. 
  instantiate (1:=C). instantiate (1:=A).
  all: eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hypotheses_shift_typesafe; auto.
    apply wf_hypotheses_shift_typesafe; auto.
    all: inv H1; apply wf_hyp_ctx in H4; inv H4. inv H8. auto. auto.
  - apply hyp_subset_shift. auto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H1. apply wf_hyp_ctx in H4. inv H4. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqOp; eauto.
  eapply hypotheses_weakening. eauto.
  - apply wf_hypotheses_shift_typesafe; auto.
    inv H3. apply wf_hyp_ctx in H5. inv H5. auto.
  - apply hyp_subset_shift. auto.
+ eapply OOTB; eauto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βListMatch_Nil.
+ eapply βListMatch_Cons.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. auto.
+ eapply ηPair; eauto.
+ eapply ηSum; eauto.
+ eapply ηList; eauto.
+ eapply ηDoBind; eauto.
+ eapply HeqSigØ.
+ eapply HeqSigU; eauto.
  eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hypotheses_shift_typesafe; auto.
    apply wf_hypotheses_shift_typesafe; auto.
    all: inv H3; apply wf_hyp_ctx in H6; inv H6. inv H9. auto. auto.
  - apply hyp_subset_shift. auto.
Qed.

(* ==================== Better Logic Reflexivity. ==================== *)

(* Defined here because we need it in next proof.*)

Lemma veq_refl Γ Ψ v A : 
  has_vtype Γ v A   -> wf_hypotheses Γ Ψ -> judg Γ Ψ (Veq A v v)
with ceq_refl Γ Ψ c C : 
  has_ctype Γ c C   -> wf_hypotheses Γ Ψ -> judg Γ Ψ (Ceq C c c)
with heq_refl Γ Ψ h Σ D : 
  has_htype Γ h Σ D -> wf_hypotheses Γ Ψ -> judg Γ Ψ (Heq Σ D h h).
Proof.
all: intros.
1: apply veq_refl_raw in H. 2: apply ceq_refl_raw in H.
3: apply heq_refl_raw in H.
all: eapply hypotheses_weakening; eauto. all: apply SubsetHypØ.
Qed.


(* ==================== Safety and Sub. ==================== *)


Fixpoint v_sub_typesafe 
  Γ v A (orig: has_vtype Γ v A) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_vtype Γ (v_sub v (i, v_s)) A

with c_sub_typesafe
  Γ c C (orig: has_ctype Γ c C) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_ctype Γ (c_sub c (i, v_s)) C

with h_sub_typesafe
  Γ h Σ D (orig: has_htype Γ h Σ D) i v_s A_s {struct orig}:
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  has_htype Γ (h_sub h (i, v_s)) Σ D

with respects_sub_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) i v_s A_s {struct orig} :
  has_htype Γ h Σ D -> get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  respects Γ (h_sub h (i, v_s)) Σ D E

with judg_sub_typesafe
  Γ Ψ φ (orig: judg Γ Ψ φ) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  judg Γ (hyp_sub Ψ (i, v_s)) (form_sub φ (i, v_s))

  with wf_hypotheses_sub_typesafe
  Γ Ψ (orig: wf_hypotheses Γ Ψ) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_hypotheses Γ (hyp_sub Ψ (i, v_s))

  with wf_form_sub_typesafe
  Γ φ (orig: wf_formula Γ φ) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_formula Γ (form_sub φ (i, v_s))

with wf_inst_sub_typesafe
  Γ I Γ' (orig: wf_inst Γ I Γ') i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_inst Γ (inst_sub I (i, v_s)) Γ'.

Proof.
all: rename v_sub_typesafe into VL; rename c_sub_typesafe into CL.
all: rename h_sub_typesafe into HL; rename respects_sub_typesafe into RL.
all: rename judg_sub_typesafe into JL.
all: rename wf_hypotheses_sub_typesafe into WFHL.
all: rename wf_form_sub_typesafe into WFFL.
all: rename wf_inst_sub_typesafe into WFIL.
{
intros gets tyvs. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  simpl. apply TypeUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  simpl. apply TypeInt.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv tyvs. assumption.
  - apply TypeVar. assumption.
+ specialize (VL _ _ _ H1) as IHv1. 
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypePair; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeInl; eauto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeInr; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeListNil; eauto.
+ specialize (VL _ _ _ H1) as IHv1. 
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeListCons; eauto.
+ specialize (CL _ _ _ H1) as IHc. 
  specialize (VL _ _ _ tyvs) as IHvs.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeFun. eapply IHc. eauto.
  inv H0. apply v_shift_typesafe; auto.
+ specialize (HL _ _ _ _ H2) as IHh. 
  specialize (CL _ _ _ H1) as IHc.
  specialize (RL _ _ _ _ _ H3) as IHr.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeHandler; eauto. eapply IHc. 
  exact gets. inv H0. inv H6. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeVSubtype; eauto.
}{
intros gets tyvs. apply TypeC; inv orig. auto. auto. destruct H1.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeRet; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeAbsurd; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeΠMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeΣMatch. eauto.
  - eapply IHc1. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
  - eapply IHc2. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeListMatch. eauto.
  - eapply IHc1. exact gets. auto.
  - eapply IHc2. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1. inv H5. all:auto.
+ specialize (CL _ _ _ H1) as IHc1. 
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeDoBind. eauto.
  eapply IHc2. exact gets. inv H1. inv H4. apply v_shift_typesafe; auto. 
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (VL _ _ _ H2) as IHv0.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeApp; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeHandle; eauto.
+ specialize (CL _ _ _ H1) as IHc1. 
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeLetRec.
  - eapply IHc1. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. exact gets. inv H1. inv H3. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H2) as IHv. 
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H3. inv H4. apply v_shift_typesafe; auto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeCSubtype; eauto.
}{
intros gets tyvs; simpl; apply TypeH; inv orig. auto. auto. auto.
destruct H2.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply TypeCasesØ.
+ specialize (HL _ _ _ _ H3) as IHh. 
  specialize (CL _ _ _ H4) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCasesU; eauto.
  - rewrite <-sub_get_case_None; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfTyFun; assumption.
}{
intros htys gets tyvs; simpl. apply Respects; inv orig; auto.
destruct H3.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply RespectEqsØ.
+ specialize (JL _ _ _ H4) as IHc. 
  specialize (RL _ _ _ _ _ H3) as IHr.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply RespectEqsU. eauto. erewrite handle_t_sub. erewrite handle_t_sub.
  eapply IHc. all: inv H2; eauto. clear IHc IHr.
  * assert (i+tctx_len Z+ctx_len Γ=ctx_len Γ+(tctx_len Z+i)) as same by omega.
    erewrite same, <-get_join_ctxs_left, len_tctx_to_ctx, <-get_join_ctxs_left. 
    eauto.
  * eapply v_join_all_ctxs_typesafe; auto.
}{
intros gets tyvs. apply WfJudg.
{ destruct orig; eauto. }
{ destruct orig; eauto. }
destruct orig. destruct H1.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. eauto.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqTrans; simpl in IH1; simpl in IH2; eauto.
+ specialize (WFHL _ _ H0) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  subst. simpl.
  destruct (i0 =? i) eqn:cmp.
  - apply (veq_refl _ (hyp_sub Ψ (i, v_s))) in tyvs; auto.
    inv H1. apply Nat.eqb_eq in cmp. subst. rewrite gets in H4.
    inv H4. eapply veq_subtype in tyvs; eauto. inv tyvs. assumption.
    inv H. inv H5. auto. eauto.
  - eapply VeqVar; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqInt.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqPair; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqInl; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqInr; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqListNil; eauto.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
    simpl. apply VeqListCons; eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqFun. rewrite hyp_shift_sub. eapply IH.
  - simpl. eauto.
  - apply v_shift_typesafe; auto. inv H. inv H5. inv H2. auto.
  - omega.
+ specialize (JL _ _ _ H1) as IHc.
  specialize (JL _ _ _ H2) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqHandler; eauto. 2: eauto. rewrite hyp_shift_sub. eapply IHc.
  - simpl. eauto.
  - apply v_shift_typesafe; auto. inv H. inv H7. inv H4. inv H8. auto.
  - omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. rewrite <-v_shift_sub. apply ηFun. omega.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ H1) as IH1.
  specialize (JL _ _ _ H2) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans. eapply IH1; eauto. eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. eauto.
+ specialize (JL _ _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd. eauto.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqΠMatch. eapply IHv; eauto.
  rewrite hyp_shift_sub. eapply IHc.
  - simpl. eauto.
  - rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe; auto. apply v_shift_typesafe; auto.
    all: inv H2; apply wf_hyp_ctx in H4; inv H4. inv H7. auto. auto.
  - omega.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqΣMatch. eauto. all: inv H1; inv H4.
  - eapply IHc1. simpl. eauto. inv H7. apply v_shift_typesafe; assumption.
  - eapply IHc2. simpl. eauto. inv H7. apply v_shift_typesafe; assumption.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqListMatch. eauto.
  - eapply IHc1; eauto.
  - eapply IHc2. simpl. eauto. rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe. apply v_shift_typesafe. auto.
    all: inv H1; inv H4. inv H7. auto. auto.
+ specialize (JL _ _ _ H1) as IHc1.
  specialize (JL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqDoBind. eauto. eapply IHc2.
  - simpl. eauto.
  - inv H1. inv H3. inv H6. apply v_shift_typesafe; assumption.
+ specialize (JL _ _ _ H1) as IHv1.
  specialize (JL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp; eauto.
+ specialize (JL _ _ _ H1) as IHv.
  specialize (JL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle; eauto.
+ specialize (JL _ _ _ H1) as IHc1.
  specialize (JL _ _ _ H2) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. inv H2. inv H4. eapply CeqLetRec.
  - eapply IHc1. simpl. eauto. rewrite <-(v_shift_shift 1 1).
    inv H2. apply v_shift_typesafe; auto. inv H10. apply v_shift_typesafe; auto.
  - eapply IHc2. simpl. eauto. inv H2. apply v_shift_typesafe; assumption.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqOp; eauto.
  eapply IHc. simpl. eauto. apply v_shift_typesafe. assumption.
  apply get_op_type_wf in H1. destruct H1. assumption. inv H. inv H5. auto.
+ specialize (WF _ _ _ H2) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  clear H2. eapply OOTB; eauto.
  rewrite <-c_sub_inst. rewrite H3. simpl. auto.
  rewrite <-c_sub_inst. rewrite H4. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Cons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  simpl. rewrite v_shift_comm, <-c_shift_sub, v_shift_shift. 
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoBind_Op as rule.
  simpl. rewrite v_shift_comm, <-c_shift_sub. 
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  simpl. rewrite v_shift_comm, <-c_shift_sub, <-h_shift_sub.
  simpl in rule. eapply rule. apply sub_get_case_Some. eauto. all: omega.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs. simpl.
    assert (S(S n)=2+n) as samen by omega.
    assert (S(S(S i))=2+(S i)) as samei by omega.
    rewrite samei, samen, <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηPair. auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt; aomega.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(S n)=2+n) as samen by omega.
    simpl. rewrite samei, samen, <-v_shift_comm, <-c_shift_sub; aomega.
    eapply ηPair. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs, c_sub_subs; aomega. simpl.
    assert (S(S i)=1+(S i)) as samei by omega.
    rewrite samei, <-v_shift_comm, <-c_shift_sub; aomega.
    eapply ηSum. auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt, c_sub_subs_alt. simpl.
    rewrite <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηSum. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
+ specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs, c_sub_subs; aomega. simpl.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(2+i)=2+(S i)) as sameii by omega.
    assert (S(S n)=2+n) as samen by omega.
    rewrite samei, samen, <-v_shift_comm, sameii, <-c_shift_sub; aomega.
    eapply ηList. auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt, c_sub_subs_alt. simpl.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(S n)=2+n) as samen by omega.
    rewrite samei, samen, <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηList. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H2. 
      apply wf_ctx_insert_vtype in H3. auto. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl. apply ηDoBind.
}{
intros gets vtys.
inv orig. destruct H4.
+ specialize (HL _ _ _ _ H2) as IH1.
  specialize (HL _ _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply Heq. 2: exact H0. all: eauto. apply HeqSigØ. 
+ specialize (HL _ _ _ _ H2) as IH1.
  specialize (HL _ _ _ _ H3) as IH2.
  specialize (JL _ _ _ H6) as IHc.
  specialize (JL _ _ _ H7) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply Heq. 2: exact H0. all: eauto. eapply HeqSigU.
  - eapply sub_get_case_Some in H4. eauto.
  - eapply sub_get_case_Some in H5. eauto.
  - eapply IHc. simpl. eauto. rewrite <-(v_shift_shift 1 1). 
    apply v_shift_typesafe. apply v_shift_typesafe; auto.
    all: inv H6; inv H8; inv H6. inv H14. all: auto.
  - eauto.
}{
intros gets vtys. destruct orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstØ. auto.
+ specialize (VL _ _ _ H) as IHv.
  specialize (WF _ _ _ orig) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL. 
  simpl. apply WfInstU; eauto.
}
Admitted.


(* ==================== Safety and Subs. ==================== *)

(*
Fixpoint v_subs_typesafe 
  Γ Γ' v A i v_s A_s (orig: has_vtype Γ' v A) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  has_vtype Γ (v_subs v i v_s) A

with c_subs_typesafe
  Γ Γ' c C i v_s A_s (orig: has_ctype Γ' c C) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  has_ctype Γ (c_subs c i v_s) C

with h_subs_typesafe
  Γ Γ' h Σ D i v_s A_s (orig: has_htype Γ' h Σ D) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  has_htype Γ (h_subs h i v_s) Σ D

with respects_subs_typesafe
  Γ Γ' h Σ D E i v_s A_s (orig: respects Γ' h Σ D E) {struct orig} :
  has_htype Γ' h Σ D -> has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s ->
  ctx_len Γ >= i ->
  respects Γ (h_subs h i v_s) Σ D E

with veq_subs_typesafe
  Γ Γ' A v1 v2 i v_s A_s (orig: veq A Γ' v1 v2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  veq A Γ (v_subs v1 i v_s) (v_subs v2 i v_s)

with ceq_subs_typesafe
  Γ Γ' C c1 c2 i v_s A_s (orig: ceq C Γ' c1 c2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c1 i v_s) (c_subs c2 i v_s)

with heq_subs_typesafe
  Γ Γ' Σ D h1 h2 i v_s A_s (orig: heq Σ D Γ' h1 h2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h1 i v_s) (h_subs h2 i v_s)

with wf_inst_subs_typesafe
  Γ Γ' I Γ0 i v_s A_s (orig: wf_inst Γ' I Γ0) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  wf_inst Γ (inst_subs I i v_s) Γ0.

Proof.
all: rename v_subs_typesafe into VL; rename c_subs_typesafe into CL.
all: rename h_subs_typesafe into HL; rename respects_subs_typesafe into RL.
all: rename veq_subs_typesafe into JL;ename ceq_subs_typesafe into JL.ll: rename heq_subs_typesafe into JL;ame wf_inst_subs_typesafe into WF.
{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeInt.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply TypeV; auto; unfold v_subs; simpl.
  destruct (n=?i) eqn:ni.
  - apply Nat.eqb_eq in ni. subst.
    rewrite v_negshift_shift, v_shift_0. erewrite get_ctx_insert_new in H1.
    inv tyvs. inv H1. assumption. auto. omega.
  - subst. simpl. destruct (i<=?n) eqn:cmp;
    apply TypeVar.
    * erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. omega.
+ specialize (VL Γ Γ0 v1 _ i _ _ H1 tyvs geq) as IH1.
  specialize (VL Γ Γ0 v2 _ i _ _ H2 tyvs geq) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypePair; auto.  
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeInl; auto.  
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeInr; auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeListNil; auto.
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH1.
  specialize (VL Γ Γ0 vs _ i _ _ H2 tyvs geq) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeListCons; auto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s).
  { simpl. f_equal. auto. }
  inv H0. specialize (v_shift_typesafe _ Γ A _ tyvs H5) as tyvs'.
  specialize (CL _ _ c _ (1+i) _ _ H1 tyvs') as IH. 
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl. apply WfTyFun; auto.
  apply TypeFun. rewrite v_shift_comm. apply IH.
  simpl. f_equal. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; inv H7; assumption).
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (CL _ _ cr _ (1+i) _ _ H1 tyvs' H4) as IHc. 
  specialize (HL _ _ h _ _ i _ _ H2 tyvs geq) as IHh. 
  specialize (RL _ _ h _ _ _ i _ _ H3 H2 tyvs) as IHr.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeHandler. rewrite v_shift_comm. apply IHc. simpl. all: aomega.
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl. 
  eapply TypeVSubtype; eauto.
}{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1. 
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  apply TypeRet. auto.
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  apply TypeAbsurd. auto.
+ assert (CtxU (CtxU Γ0 A) B = ctx_insert (CtxU (CtxU Γ A) B) (2+i) A_s).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (VL _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CL _ _ c _ (2+i) _ _ H2 tyvs'' H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeΠMatch. eauto. 
  rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc.
  simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s) as geqa.
  { simpl. f_equal. auto. }
  assert (CtxU Γ0 B = ctx_insert (CtxU Γ B) (1+i) A_s) as geqb.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (VL _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CL _ _ c1 _ (1+i) _ _ H2 tyvsa geqa) as IHc1.
  specialize (CL _ _ c2 _ (1+i) _ _ H3 tyvsb geqb) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeΣMatch. eauto. 
  - rewrite v_shift_comm. apply IHc1. simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU (CtxU Γ0 A) (TyList A) 
    = ctx_insert (CtxU (CtxU Γ A) (TyList A)) (2+i) A_s).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H6; auto).
  assert (wf_vtype (TyList A)) as wfla by (inv H1; auto).
  specialize (VL _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyList A) _ tyvs' wfla) as tyvs''.
  specialize (CL _ _ c1 _ i _ _ H2 tyvs geq) as IHc1.
  specialize (CL _ _ c2 _ (2+i) _ _ H3 tyvs'' H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeListMatch; eauto. 
  rewrite v_shift_shift in IHc2. rewrite v_shift_comm. apply IHc2.
  simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s) as geqa.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (CL _ _ c1 _ i _ _ H1 tyvs geq) as IHc1.
  specialize (CL _ _ c2 _ (1+i) _ _ H2 tyvsa geqa) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeDoBind. eauto. 
  rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ specialize (VL _ _ v1 _ i _ _ H1 tyvs) as IH1.
  specialize (VL _ _ v2 _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeApp. eauto. eauto.
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IHv.
  specialize (CL _ _ c _ i _ _ H2 tyvs) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeHandle. eauto. eauto.
+ assert (CtxU (CtxU Γ0 A) (TyFun A C) 
    = ctx_insert (CtxU (CtxU Γ A) (TyFun A C)) (2+i) A_s).
  { simpl. f_equal. f_equal. auto. }
  assert (CtxU Γ0 (TyFun A C) = ctx_insert (CtxU Γ (TyFun A C)) (1+i) A_s).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; inv H10; auto).
  assert (wf_ctype C) as wfc by (inv H1; inv H5; inv H10; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' (WfTyFun A C wfa wfc)) 
  as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs (WfTyFun A C wfa wfc)) 
  as tyvs'''.
  specialize (CL _ _ c1 _ (2+i) _ _ H1 tyvs'' H3) as IHc1.
  specialize (CL _ _ c2 _ (1+i) _ _ H2 tyvs''' H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeLetRec. 
  - rewrite v_shift_shift in IHc1. rewrite v_shift_comm. apply IHc1. 
    simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU Γ0 Bop = ctx_insert (CtxU Γ Bop) (1+i) A_s) as geqb.
  { simpl. f_equal. auto. }
  assert (wf_vtype Bop) as wfb by (inv H3; inv H4; auto).
  specialize (v_shift_typesafe _ _ Bop _ tyvs wfb) as tyvsb.
  specialize (VL _ _ v _ i _ _ H2 tyvs geq) as IHv.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyvsb geqb) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CL Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubtype; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2. 
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeH; auto; unfold h_subs; simpl.
  apply TypeCasesØ.
+ assert (CtxU (CtxU Γ0 (TyFun Bop D)) Aop 
    = ctx_insert (CtxU (CtxU Γ (TyFun Bop D)) Aop) (2+i) A_s).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype Aop) as wfa by (inv H0; auto).
  assert (wf_vtype (TyFun Bop D)) as wfb by (inv H0; apply WfTyFun; auto).
  specialize (v_shift_typesafe _ _ (TyFun Bop D) _ tyvs wfb) as tyvs'.
  specialize (v_shift_typesafe _ _ Aop _ tyvs' wfa) as tyvs''.
  specialize (HL _ _ h _ _ i _ _ H3 tyvs geq) as IHh.
  specialize (CL _ _ cop _ (2+i) _ _ H4 tyvs'' H5) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeH; auto; unfold h_subs; simpl.
  eapply TypeCasesU; auto.
  - apply negshift_get_case_None. apply sub_get_case_None. auto.
  - rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
    simpl. omega. omega.
}{
intros tysh tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H3. 
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsØ.
+ specialize (RL _ _ _ _ _ _ i v_s _ H3 tysh tyvs geq) as IHr.
  specialize (JL    (join_ctxs (join_ctxs Γ (tctx_to_ctx Z D)) Γ0) 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ0) 
    D (handle_t (ctx_len Γ0) (tctx_len Z) h T1) 
    (handle_t (ctx_len Γ0) (tctx_len Z) h T2) 
    (i + tctx_len Z + ctx_len Γ0) 
    (v_shift v_s (tctx_len Z+ctx_len Γ0) 0) A_s H4) as IHc.
  all: clear VL CL HL RL JL WFHL WFFL WFIL.
  apply Respects; auto; unfold h_subs; simpl.
  apply RespectEqsU. auto.
  erewrite handle_t_negshift, handle_t_sub, v_shift_comm.
  erewrite handle_t_negshift, handle_t_sub, (v_shift_comm 1 i).
  assert (tctx_len Z+ctx_len Γ0+i=i+tctx_len Z+ctx_len Γ0) as s by omega.
  rewrite s. eapply IHc. all: clear IHc.
  all: omega || (inv H2; eauto).
  - apply v_join_all_ctxs_typesafe; auto.
  - assert (i+tctx_len Z+ctx_len Γ0=ctx_len Γ0+(tctx_len Z+i)) as ss by omega.
    rewrite ss, <-join_ctxs_insert. f_equal.
    erewrite len_tctx_to_ctx, <-join_ctxs_insert. auto.
  - rewrite len_join_ctxs, len_join_ctxs, <-len_tctx_to_ctx. omega.
  - apply h_sub_makes_no_var. apply v_shift_makes_no_var.
  - eapply h_sub_typesafe; eauto. apply get_ctx_insert_new. auto.
    eapply v_insert_typesafe; auto. inv tyvs. auto.
  - apply h_sub_makes_no_var. apply v_shift_makes_no_var.
  - eapply h_sub_typesafe; eauto. apply get_ctx_insert_new. auto.
    eapply v_insert_typesafe; auto. inv tyvs. auto.
}{
intros tyvs geq len. apply Veq.
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H1.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. apply IH; auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL. subst. unfold v_subs. simpl.
  rename i0 into j. destruct (j =? i) eqn:cmp. 
  - rewrite v_negshift_shift, v_shift_0. 
    apply veq_refl in tyvs. inv H0. apply Nat.eqb_eq in cmp. subst. 
    erewrite get_ctx_insert_new in H1. inv H1.
    eapply veq_subtype in tyvs; eauto. inv tyvs. all: eaomega.
  - simpl. destruct (i<=?j) eqn:ilj;
    eapply VeqVar; eaomega.
    * apply Nat.eqb_neq in cmp. apply leb_complete in ilj.
      erewrite get_ctx_insert_changed.
      assert (1+(j-1)=j) by omega. rewrite H3. eauto. omega. 
    * apply Nat.eqb_neq in cmp. apply leb_complete_conv in ilj.
      erewrite get_ctx_insert_unchanged; eaomega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  apply VeqUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  apply VeqInt.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply VeqPair; auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqInl; eauto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqInr; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
unfold v_subs. simpl. apply VeqListNil; auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply VeqListCons; auto.
+ assert (wf_vtype A) as wfa by (inv H; inv H3; assumption).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (JL _ _ _ _ (S i) _ _ H1 tyvs') as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqFun.
  rewrite v_shift_comm. apply IH. simpl. f_equal. auto.
  all: simpl; omega.
+ assert (wf_vtype A) as wfa by (inv H; inv H5; inv H8; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (JL _ _ _ _ (S i) _ _ H1 tyvs') as IHc.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqHandler; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. auto.
  all: simpl; omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl.
  rewrite <-v_shift_sub, <-v_shift_negshift_comm; aomega. apply ηFun.
  apply v_sub_makes_no_var. apply v_shift_makes_no_var. 
}{
intros tyvs geq len. apply Ceq.
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H1.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans; eauto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd. auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H4; inv H6; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (JL _ _ _ _ (2+i) _ _ H2 tyvs'') as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqΠMatch. auto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1); aomega.
  apply IHc. simpl. do 2 f_equal. assumption. simpl. omega.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H5; inv H7; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; inv H7; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (JL _ _ _ _ (S i) _ _ H2 tyvsa) as IHc1.
  specialize (JL _ _ _ _ (S i) _ _ H3 tyvsb) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqΣMatch. auto.
  all: rewrite v_shift_comm; omega || apply IHc1 || apply IHc2.
  all: simpl; aomega; f_equal; auto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H4; inv H7; auto).
  assert (wf_vtype (TyList A)) as wfla by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyList A) _ tyvs' wfla) as tyvs''.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IHc1.
  specialize (JL _ _ _ _ (2+i) _ _ H3 tyvs'') as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqListMatch; eauto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IHc2.
  simpl. do 2 f_equal. assumption. simpl. omega. omega.
+ assert (wf_vtype A) as wfa by (inv H1; inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHc1.
  specialize (JL _ _ _ _ (S i) _ _ H2 tyvsa) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqDoBind. eauto.
  rewrite v_shift_comm. apply IHc2. simpl.  f_equal. assumption.
  simpl. omega. omega.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHv1.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp; eauto.
+ specialize (JL _ _ _ _ i _ _ H1 tyvs) as IHv.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle; eauto.
+ assert (wf_vtype A) as wfa by (inv H2; inv H3; inv H2; inv H10; auto).
  assert (wf_vtype (TyFun A C)) as wff by (inv H2; inv H3; inv H2; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' wff) as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs wff) as tyvs'''.
  specialize (JL _ _ _ _ (2+i) _ _ H1 tyvs'') as IHc1.
  specialize (JL _ _ _ _ (1+i) _ _ H2 tyvs''') as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqLetRec.
  all: rewrite v_shift_comm; eaomega.
  - rewrite <-(v_shift_shift 1 1). eapply IHc1. simpl. do 2 f_equal. auto.
    simpl. omega.
  - apply IHc2. simpl. f_equal. auto. simpl. omega.
+ assert (wf_vtype Bop) as wfb by (inv H3; inv H4; inv H3; auto).
  specialize (v_shift_typesafe _ _ Bop _ tyvs wfb) as tyvsb.
  specialize (JL _ _ _ _ i _ _ H2 tyvs) as IHv.
  specialize (JL _ _ _ _ (S i) _ _ H3 tyvsb) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold c_subs. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. auto. simpl. omega. omega.
+ specialize (WF _ _ _ _ i _ _ H2 tyvs) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply OOTB; eauto.
  rewrite <-c_subs_inst. rewrite H3. simpl. auto.
  rewrite <-c_subs_inst. rewrite H4. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ΠMatch (Pair v1 v2) c) i v_s 
    = ΠMatch (Pair (v_subs v1 i v_s) (v_subs v2 i v_s)) 
        (c_subs c (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H1. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inl v) c1 c2) i v_s
    = ΣMatch (Inl (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; aomega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inr v) c1 c2) i v_s
    = ΣMatch (Inr (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; aomega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl.
  assert (c_subs (ListMatch ListNil c1 c2) i v_s 
    = ListMatch ListNil 
        (c_subs c1 i v_s)
        (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βListMatch_Cons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ListMatch (ListCons v vs) c1 c2) i v_s
    = ListMatch (ListCons (v_subs v i v_s) (v_subs vs i v_s))
        (c_subs c1 i v_s)
        (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (App (Fun c) v) i v_s 
    = App (Fun (c_subs c (1+i) (v_shift v_s 1 0))) (v_subs v i v_s)).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (LetRec c1 c2) i v_s
    = LetRec (c_subs c1 (2+i) (v_shift v_s 2 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. simpl. do 2 f_equal; rewrite v_shift_comm; auto || omega. }  
  rewrite H1. clear H1.
  assert ( v_subs (Fun (LetRec (c_shift c1 1 2) c1)) i v_s
    = Fun (LetRec
       (c_shift (c_subs c1 (2+i) (v_shift v_s 2 0)) 1 2)
       (c_subs c1 (2+i) (v_shift v_s 2 0))) ).
  { unfold c_subs. unfold v_subs. simpl. do 2 f_equal.
    rewrite v_shift_comm, <-c_shift_sub, c_shift_negshift_comm.
    do 2 f_equal. rewrite v_shift_comm. all: aomega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    do 3 f_equal. rewrite v_shift_shift, v_shift_comm; aomega. }
  rewrite H1. clear H1. apply rule. omega.  
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (DoBind (Ret v) c) i v_s 
    = DoBind (Ret (v_subs v i v_s)) (c_subs c (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoBind_Op as rule.
  unfold c_subs_out in *. unfold c_subs. simpl. rewrite v_shift_comm. 
  specialize (rule op 
    (v_negshift (v_sub v (i, v_shift v_s 1 i)) 1 i)
    (c_negshift
      (c_sub c1 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i))) 1 (S i))
    (c_negshift
      (c_sub c2 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i))) 1 (S i))).
  rewrite c_shift_negshift_comm, c_shift_sub in rule. simpl.
  assert (v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 0
    = v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 1).
  { rewrite <-v_shift_comm, v_shift_comm. all: aomega. }
  rewrite H1. apply rule. all: aomega. clear rule.
  apply c_sub_makes_no_var. apply v_shift_makes_no_var.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (Handle (Handler c_r h) (Ret v)) i v_s
    = Handle (Handler 
      (c_subs c_r (1+i) (v_shift v_s 1 0)) (h_subs h i v_s)) 
      (Ret (v_subs v i v_s) ) ).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H1. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (Handle (Handler c_r h) (Op op v c_k)) i v_s =
    Handle (Handler (c_subs c_r (1+i) (v_shift v_s 1 0)) (h_subs h i v_s))
    (Op op (v_subs v i v_s) (c_subs c_k (1+i) (v_shift v_s 1 0)))).
  { unfold c_subs. unfold v_subs. simpl. do 5 f_equal;
    apply v_shift_comm; omega. }
  rewrite H2. clear H2.
  assert (v_subs (Fun
    (Handle (Handler (c_shift c_r 1 1) (h_shift h 1 0)) c_k)) i v_s
  = Fun (Handle (v_shift (Handler (c_subs c_r (1+i) (v_shift v_s 1 0)) 
      (h_subs h i v_s)) 1 0) (c_subs c_k (1+i) (v_shift v_s 1 0)))).
  { clear rule. unfold v_subs. unfold c_subs. unfold h_subs. 
    simpl. do 3 f_equal.
    rewrite c_shift_negshift_comm, c_shift_sub. do 3 f_equal.
    rewrite v_shift_comm. f_equal. apply v_shift_comm. all: aomega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite h_shift_negshift_comm, h_shift_sub. all: aomega.
    apply h_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite v_shift_comm; aomega. }
  rewrite H2, v_shift_shift, <-v_shift_subs_alt. clear H2. simpl.
  eapply rule. unfold h_subs. 
  apply negshift_get_case_Some. rewrite <-(v_shift_comm 1 i 0). 
  apply sub_get_case_Some. all:eaomega.
+ assert (wf_vtype (TyΠ A B)) as wfab.
  { inv H2. apply wf_ctx_insert_vtype in H3. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TyΠ A B) n wfab) as tyvsab.
  specialize (CL _ _ c _ (1+i) _ _ H2 tyvsab) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyΠ A B) (n-1) wfab) as tyvsabm.
  specialize (CL _ _ c _ (i) _ _ H2 tyvsabm) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c, c_subs (ΠMatch v c) i v_s 
    = ΠMatch (v_subs v i v_s) (c_subs c (2+i) (v_shift v_s 2 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H3. clear H3.
  destruct (n<=?i) eqn:ni.
  - clear IHc.
    apply leb_complete in ni.
    rewrite c_subs_subs, (c_subs_subs _ (2+n)). simpl.
    specialize ηPair as rule.
    assert (S(S n)=2+n) as samen by omega.
    assert (S(S(S i))=1+(1+(S i))) as samei by omega.
    rewrite samei, samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    assert (v_subs (Pair (Var 1) (Var 0)) (S(S i)) (v_shift v_s 2 0) 
      = (Pair (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H3. clear H3. eapply ηPair. all: aomega.
    apply IHcp. subst. rewrite ctx_insert_comm. all: aomega.
    rewrite ctx_len_insert; omega.
  - clear IHcp.
    apply leb_complete_conv in ni.
    destruct n. omega.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ ). all: aomega. simpl.
    specialize ηPair as rule.
    assert (v_subs (Pair (Var 1) (Var 0)) (S (S i)) (v_shift v_s 2 0)
      = (Pair (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H3. clear H3. 
    assert (S(S n)=2+n) as samen by omega.
    rewrite samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    eapply ηPair. all: aomega.
    subst. rewrite ctx_len_insert in H1. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TyΠ A B)) as triv. omega.
+ assert (wf_vtype (TyΣ A B)) as wfab.
  { inv H2. apply wf_ctx_insert_vtype in H3. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TyΣ A B) n wfab) as tyvsab.
  specialize (CL _ _ c _ (1+i) _ _ H2 tyvsab) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyΣ A B) (n-1) wfab) as tyvsabm.
  specialize (CL _ _ c _ (i) _ _ H2 tyvsabm) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c1 c2, c_subs (ΣMatch v c1 c2) i v_s 
    = ΣMatch (v_subs v i v_s) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H3. clear H3.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite (c_subs_subs _ n), (c_subs_subs _ (1+n)), (c_subs_subs _ (1+n)).
    simpl. all: try omega.
    rewrite <-v_shift_comm, <-c_shift_subs_alt. all: try omega.
    eapply ηSum. omega. apply IHcp. 
    subst. rewrite ctx_insert_comm; aomega.
    rewrite ctx_len_insert; omega.
  - apply leb_complete_conv in ni.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ n).
    destruct n. all: aomega.
    rewrite (c_subs_subs_alt _ n). simpl.
    rewrite <-v_shift_comm, <-c_shift_subs_alt. all: aomega.
    eapply ηSum. subst. rewrite ctx_len_insert in H1. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TyΣ A B)) as triv. omega.
+ assert (wf_vtype (TyList A)) as wfla.
  { inv H2. apply wf_ctx_insert_vtype in H3. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TyList A) n wfla) as tyvsla.
  specialize (CL _ _ c _ (1+i) _ _ H2 tyvsla) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyList A) (n-1) wfla) as tyvslam.
  specialize (CL _ _ c _ (i) _ _ H2 tyvslam) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c1 c2, c_subs (ListMatch v c1 c2) i v_s 
    = ListMatch (v_subs v i v_s) 
        (c_subs c1 i v_s) (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { intros c1' c2'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H3. clear H3.
  destruct (n<=?i) eqn:ni.
  - clear IHc.
    apply leb_complete in ni.
    rewrite c_subs_subs, (c_subs_subs _ n), (c_subs_subs _ (2+n)). simpl.
    specialize ηList as rule.
    assert (S(S n)=2+n) as samen by omega.
    assert (S(S(S i))=1+(1+(S i))) as samei by omega.
    rewrite samei, samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    assert (v_subs (ListCons (Var 1) (Var 0)) (S(S i)) (v_shift v_s 2 0) 
      = (ListCons (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H3. clear H3. eapply ηList. all: aomega.
    apply IHcp. subst. rewrite ctx_insert_comm. all: aomega.
    rewrite ctx_len_insert; omega.
  - clear IHcp.
    apply leb_complete_conv in ni.
    destruct n. omega.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ n), (c_subs_subs_alt _ ).
    all: aomega. simpl.
    specialize ηList as rule.
    assert (v_subs (ListCons (Var 1) (Var 0)) (S (S i)) (v_shift v_s 2 0)
      = (ListCons (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H3. clear H3. 
    assert (S(S n)=2+n) as samen by omega.
    rewrite samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    eapply ηList. all: aomega.
    subst. rewrite ctx_len_insert in H1. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TyList A)) as triv. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl. apply ηDoBind.
}{
intros tyvs geq len.
destruct orig. destruct H4.
+ specialize (HL _ _ h1 _ _ i _ _ H2 tyvs geq) as IHh1.
  specialize (HL _ _ h2 _ _ i _ _ H3 tyvs geq) as IHh2.
  clear VL CL HL RL JL WFHL WFFL WFIL. eapply Heq. 
  2: exact H0. all: eauto. eapply HeqSigØ.
+ assert (wf_vtype A) as wfa by (inv H6; inv H8; inv H6; auto).
  assert (wf_vtype(TyFun B D)) as wff by (inv H6;inv H8;inv H6;inv H14;auto).
  specialize (HL _ _ h1 _ _ i _ _ H2 tyvs geq) as IHh1.
  specialize (HL _ _ h2 _ _ i _ _ H3 tyvs geq) as IHh2.
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs wff) as tyvs'.
  specialize (v_shift_typesafe _ _ A _ tyvs' wfa) as tyvs''.
  specialize (JL _ _ _ _ (2+i) _ _ H6 tyvs'') as IH1.
  specialize (JL _ _ _ _ i _ _ H7 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply Heq. 2: exact H0. all: eauto.
  eapply HeqSigU; eauto.
  - unfold h_subs. eapply negshift_get_case_Some.
    eapply sub_get_case_Some. eauto.
  - unfold h_subs. eapply negshift_get_case_Some.
    eapply sub_get_case_Some. eauto.
  - rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IH1.
    simpl. do 2 f_equal. all: simpl; aomega.
}{
intros tyvs geq len. destruct orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstØ. inv tyvs. auto.
+ specialize (VL _ _ _ _ i _ _ H tyvs geq) as IHv.
  specialize (WF _ _ _ _ i _ _ orig tyvs geq) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  apply WfInstU; eauto.
}
Admitted.

(* ==================== Templates as Terms ==================== *)

Fixpoint tmpl_to_comp_has_ctype Γ Z T A Σ E (orig: wf_t Γ Z T Σ):
  wf_ctype (CTy A Σ E) -> wf_ctx Γ -> wf_tctx Z ->
  has_ctype 
    (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) 
    (tmpl_to_comp (ctx_len Γ) T) 
    (CTy A Σ E).
Proof.
intros wfd wfg wfz.
assert (wf_ctx (tctx_to_ctx Z (CTy A Σ E))).
{ apply wf_tctx_to_ctx; auto. }
assert (wf_ctx (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ)).
{ apply wf_join_ctxs; auto. }
destruct orig; simpl; apply TypeC; eauto.
+ eapply TypeApp.
  - apply TypeV; eauto. apply WfTyFun; inv H1; eauto.
    apply TypeVar. erewrite <-get_join_ctxs_left.
    apply get_tctx_to_ctx. auto.
  - apply v_join_ctxs_typesafe_right; auto.
+ eapply TypeAbsurd. apply v_join_ctxs_typesafe_right; auto.
+ eapply TypeΠMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in orig. auto.
    apply WfCtxU. apply WfCtxU. all: inv H1; inv H3; auto.
+ eapply TypeΣMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig1; eauto.
    simpl in orig1. auto.
    apply WfCtxU. auto. inv H1. inv H3. auto.
  - eapply tmpl_to_comp_has_ctype in orig2; eauto.
    simpl in orig2. auto.
    apply WfCtxU. auto. inv H1. inv H3. auto.
+ eapply TypeListMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig1; eauto.
  - eapply tmpl_to_comp_has_ctype in orig2; eauto.
    simpl in orig2. auto.
    apply WfCtxU. apply WfCtxU. all: inv H1; auto; inv H3; auto.
+ assert (wf_vtype A0) as wfa by (inv H1; inv H3; auto). 
  eapply TypeDoBind; eauto. instantiate (1:=A0).
  - apply c_join_ctxs_typesafe_right; auto. apply TypeC; auto.
    apply WfCTy; inv wfd; auto.
    eapply TypeCSubtype; eauto. apply SubtypeCTy.
    * apply vsubtype_refl. auto.
    * apply SubtypeSigØ.
    * apply SubtypeEqsØ.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in *. auto. apply WfCtxU; auto.
+ eapply TypeOp; eauto.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in orig. auto.
    apply WfCtxU. auto. inv wfd. apply get_op_type_wf in H1.
    destruct H1. auto. auto.
Admitted.


(* ==================== Handling templates ==================== *)

(* Auxilliary lemmas *)
Fixpoint cop_join_ctxs_special Γ' Γ A B D c {struct Γ}:
  wf_ctx Γ -> has_ctype (CtxU (CtxU Γ' (TyFun B D)) A) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs Γ' Γ) (TyFun B D)) A) 
    (c_shift c (ctx_len Γ) 2) D.
Proof.
intros wfg tys.
destruct Γ; simpl.
+ rewrite c_shift_0. auto.
+ assert (CtxU (CtxU (CtxU (join_ctxs Γ' Γ) v) (TyFun B D)) A
    = ctx_insert (CtxU (CtxU (join_ctxs Γ' Γ) (TyFun B D)) A) 2 v).
  { simpl. do 2 f_equal. destruct Γ; simpl. destruct Γ'; simpl. all: auto. }
  assert (S (ctx_len Γ) = ctx_len Γ + 1) by omega.
  rewrite H, H0. rewrite <-(c_shift_shift). apply c_insert_typesafe.
  all: inv wfg; auto.
Admitted.

Fixpoint cop_with_full_ctx_types Γ' Γ Z A B D c:
  wf_ctx Γ -> wf_tctx Z ->
  has_ctype (CtxU (CtxU Γ' (TyFun B D)) A) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) (TyFun B D)) A) 
    (c_shift c (tctx_len Z + ctx_len Γ) 2) D.
Proof.
intros wfg wfz tys.
rewrite <-join_ctxs_assoc. 
erewrite len_tctx_to_ctx, <-len_join_ctxs.
apply cop_join_ctxs_special. apply wf_join_ctxs. apply wf_tctx_to_ctx.
all: auto. inv tys. auto.
Admitted.


Fixpoint handle_t_types Γ Z T Σ Γ' h D (orig: wf_t Γ Z T Σ) {struct orig}:
  wf_ctx Γ -> wf_tctx Z -> has_htype Γ' h  Σ D ->
  has_ctype 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (handle_t (ctx_len Γ) (tctx_len Z) h T) D.
Proof.
intros wfc wfz tys.
assert (wf_ctype D) by (inv tys; inv H0; assumption).
assert (wf_ctx (join_ctxs Γ' (tctx_to_ctx Z D))) as wfct.
{ apply wf_join_ctxs. inv tys. auto. apply wf_tctx_to_ctx; auto. }
assert (wf_ctx (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)) as wfctt.
{ apply wf_join_ctxs; auto. }
destruct orig; simpl.
+ apply TypeC; auto. eapply TypeApp.
  - apply TypeV; auto. instantiate (1:=A).
    apply WfTyFun. inv H0. auto. auto. apply TypeVar.
    erewrite <-get_join_ctxs_left. apply get_join_ctxs_right.
    apply get_tctx_to_ctx. auto.
  - apply v_join_ctxs_typesafe_right; auto.
+ apply TypeC; auto. eapply TypeAbsurd. 
  apply v_join_ctxs_typesafe_right; auto.
+ apply TypeC; auto. eapply TypeΠMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A) B
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU (CtxU Γ A) B)). 
    { simpl.  reflexivity. }
    assert (S (S (ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) B)).
    { simpl. reflexivity. }
    rewrite H1, H2. eapply handle_t_types; eauto.
    apply WfCtxU. apply WfCtxU. auto. all: inv H0; inv H4; auto.
+ apply TypeC; auto. eapply TypeΣMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ A)). 
    { simpl.  reflexivity. }
    assert (S (ctx_len Γ)=ctx_len (CtxU Γ A)).
    { simpl. reflexivity. }
    rewrite H1, H2. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv H0. inv H4. auto.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) B
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ B)). 
    { simpl.  reflexivity. }
    assert (S (ctx_len Γ)=ctx_len (CtxU Γ B)).
    { simpl. reflexivity. }
    rewrite H1, H2. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv H0. inv H4. auto.
+ apply TypeC; auto. eapply TypeListMatch; eauto.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU(CtxU(join_ctxs(join_ctxs Γ' (tctx_to_ctx Z D))Γ)A)(TyList A)
      = join_ctxs(join_ctxs Γ'(tctx_to_ctx Z D))(CtxU(CtxU Γ A)(TyList A))). 
    { simpl.  reflexivity. }
    assert (S (S (ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) (TyList A))).
    { simpl. reflexivity. }
    rewrite H1, H2. eapply handle_t_types; eauto.
    apply WfCtxU. apply WfCtxU. auto. all: inv H0; auto; inv H4; auto.
+ apply TypeC; auto.
  assert (wf_vtype A) as wfa by (inv H0; inv H2; auto). 
  destruct D as [B Σ' E'].  
  eapply TypeDoBind; eauto. instantiate (1:=A).
  - apply c_join_ctxs_typesafe_right; auto. apply TypeC; auto.
    apply WfCTy; inv H; auto.
    eapply TypeCSubtype; eauto. apply SubtypeCTy.
    * apply vsubtype_refl. auto.
    * apply SubtypeSigØ.
    * apply SubtypeEqsØ.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z (CTy B Σ' E'))) Γ) A
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z (CTy B Σ' E'))) (CtxU Γ A)). 
    { simpl. reflexivity. }
    rewrite H1. eapply handle_t_types; eauto. apply WfCtxU; auto.
+ specialize (h_has_case Γ' h Σ D op Aop Bop tys H0) as has.
  destruct has as [cop finds].
  eapply case_has_type in finds as coptys; eauto. rewrite finds.
  unfold c_subs2_out.
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)) (TyFun Bop D)).
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (CtxU(join_ctxs (join_ctxs Γ'(tctx_to_ctx Z D)) Γ) (TyFun Bop D))Aop)).
  - assert (ctx_len Γ + tctx_len Z = tctx_len Z + ctx_len Γ) as same by omega.
    rewrite same. apply cop_with_full_ctx_types; eauto.
  - apply v_shift_typesafe. apply v_join_ctxs_typesafe_right; eauto.
    inv coptys. inv H2. inv H7. auto. 
  - simpl. auto.
  - omega.
  - apply TypeV; eauto. inv coptys. inv H2. inv H7. eauto.
    apply TypeFun.
    assert (S (ctx_len Γ) = ctx_len (CtxU Γ Bop)) as samelen by (simpl; auto).
    assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) Bop
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ Bop)).
    { simpl. reflexivity. }
    rewrite samelen, H2. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv coptys. inv H3. inv H8. inv H10. auto. 
  - assert (forall γ A, CtxU γ A = ctx_insert γ 0 A).
    { intros. induction γ; simpl; auto. }
    rewrite H2. auto.
  - omega.
Admitted.
*)