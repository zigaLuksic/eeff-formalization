(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".

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
assert (S(S(ctx_len Γ)) = ctx_len(CtxU(CtxU Γ A) (TyFun B D))) by auto.
rewrite H4. eauto.
}
Qed.


Fixpoint wf_form_is_under_ctx Γ φ (wf :wf_form Γ φ) {struct wf}:
  form_under_var φ (ctx_len Γ).
Proof.
destruct wf; simpl; auto.
+ apply has_vtype_is_under_ctx in H. apply has_vtype_is_under_ctx in H0. auto.
+ apply has_ctype_is_under_ctx in H. apply has_ctype_is_under_ctx in H0. auto.
+ apply has_htype_is_under_ctx in H2. apply has_htype_is_under_ctx in H3. auto.
+ apply wf_form_is_under_ctx in wf. simpl. auto.
+ apply wf_form_is_under_ctx in wf. simpl. auto.
Qed.


Lemma wf_t_is_under_ctx_tctx Γ Z T Σ:
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
  all: apply IHT in H13; destruct H13; assumption.
Qed.


Lemma handle_t_no_var h i D Γ Z T Σ:
  h_no_var h i -> wf_t Γ Z T Σ ->
  c_no_var 
    (handle_t D (ctx_len Γ) (tctx_len Z) h T)
    (i + tctx_len Z + ctx_len Γ).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ constructor.
  all: apply wf_t_is_under_ctx_tctx in H0; destruct H0; simpl in *.
  omega. eapply v_under_var_no_var; eaomega.
+ apply wf_t_is_under_ctx_tctx in H0. destruct H0.
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
    * apply c_no_var_shift. rewrite slen, (sctx v0). eapply IHT.
      all: aomega.
    * eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
  - simpl. constructor.
    * eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. all: eaomega.
    * rewrite slen, (sctx v0). eauto.
Qed.


Lemma handle_t_under_var h i D Γ Z T Σ:
  h_under_var h i -> wf_t Γ Z T Σ ->
  c_under_var (handle_t D (ctx_len Γ) (tctx_len Z) h T) 
    (i + tctx_len Z + ctx_len Γ).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ constructor.
  all: apply wf_t_is_under_ctx_tctx in H0; destruct H0; simpl in *. 
  omega. eapply v_under_var_weaken; eaomega.
+ apply wf_t_is_under_ctx_tctx in H0. destruct H0.
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
    * apply c_under_var_shift. rewrite slen, (sctx v0). eapply IHT.
      all: aomega.
    * eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
  - simpl. constructor.
    * eapply v_under_var_weaken. eapply has_vtype_is_under_ctx. eauto. omega.
    * rewrite slen, (sctx v0). eauto.
Qed.

(* ==================== Handling and Shifts. ==================== *)

Lemma handle_t_shift Γ' Γ Z h T Σ D i:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t D (ctx_len Γ) (tctx_len Z) (h_shift h 1 i) T
  = c_shift 
      (handle_t D (ctx_len Γ) (tctx_len Z) h T) 
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
    rewrite c_shift_comm. f_equal. omega. omega. f_equal.
    rewrite (sctx v0), IHT, c_shift_comm; aomega.
    f_equal. all: simpl; omega.
  * rewrite v_shift_too_high. auto. 
    apply has_vtype_is_under_ctx in H12. eapply v_under_var_weaken; eaomega.
Qed.


Lemma handle_t_negshift Γ' Γ Z h T Σ D i:
  h_no_var h i -> wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t D (ctx_len Γ) (tctx_len Z) (h_negshift h 1 i) T
  = c_negshift 
      (handle_t D (ctx_len Γ) (tctx_len Z) h T) 
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
  rewrite c_negshift_subs. 2: omega. f_equal.
  * rewrite c_negshift_subs. 2: omega. simpl.
    rewrite cext, c_shift_negshift_comm. do 2 f_equal.
    rewrite (sctx v0), IHT; auto.
    rewrite c_shift_negshift_comm. f_equal. all: simpl; aomega.
    - rewrite (sctx v0). eapply handle_t_no_var; eauto. 
    - rewrite cext. apply c_no_var_shift; aomega.
    - rewrite slen. apply c_no_var_shift. 
      rewrite (sctx v0). eapply handle_t_no_var. all: eaomega.
  * rewrite v_negshift_too_high. auto. 
    apply has_vtype_is_under_ctx in H12. eapply v_under_var_weaken; eaomega.
  * apply c_no_var_subs; simpl. rewrite cext.
    apply c_no_var_shift. all: eaomega.
    rewrite slen. apply c_no_var_shift. 
    rewrite (sctx v0). eapply handle_t_no_var. all: eaomega.
  * apply has_vtype_is_under_ctx in H12. eapply v_under_var_no_var; eaomega.
Qed.


Lemma handle_t_sub Γ' Γ Z h T Σ D i v_s:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D ->
    handle_t D (ctx_len Γ) (tctx_len Z) (h_sub h (i, v_s)) T
  = c_sub 
      (handle_t D (ctx_len Γ) (tctx_len Z) h T)
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
    rewrite (v_shift_comm _ _ 0). f_equal. all: try omega. f_equal.
    rewrite slen, (sctx v0), IHT; auto.
    rewrite c_shift_sub, (v_shift_comm 1 0). do 3 f_equal.
    rewrite v_shift_shift. f_equal. all: simpl; omega.
  * rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H12. eapply v_under_var_weaken; eaomega.
Qed.


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

with wf_hyp_insert_typesafe
  Γ Ψ (orig: wf_hyp Γ Ψ) A_ins i {struct orig} :
  wf_vtype A_ins ->
  wf_hyp (ctx_insert Γ i A_ins) (hyp_shift Ψ 1 i)

with wf_form_insert_typesafe
  Γ φ (orig: wf_form Γ φ) A_ins i {struct orig} :
  wf_vtype A_ins ->
  wf_form (ctx_insert Γ i A_ins) (form_shift φ 1 i)

with wf_inst_insert_typesafe
  Γ Γ' I (orig: wf_inst Γ I Γ') A_ins i {struct orig} : 
  wf_vtype A_ins ->
  wf_inst (ctx_insert Γ i A_ins) (inst_shift I 1 i) Γ'.

Proof.
all: rename v_insert_typesafe into VL; rename c_insert_typesafe into CL.
all: rename h_insert_typesafe into HL; rename respects_insert_typesafe into RL.
all: rename judg_insert_typesafe into JL.
all: rename wf_hyp_insert_typesafe into WFHL.
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
  simpl. apply TypeLeft. auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeRight. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeNil.
+ specialize (VL _ _ _ H1) as IHv1.
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCons; auto.
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
  eapply TypeVSubsume; auto.
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
  simpl. eapply TypeProdMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeSumMatch. auto.
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
  simpl. eapply TypeDo. auto. rewrite ctx_insert_extend. auto.
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
+ specialize (VL _ _ _ H4) as IHv.
  specialize (CL _ _ _ H5) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeOp. 5: rewrite ctx_insert_extend. all: eauto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeCSubsume; auto.
}{
intros wfins. apply TypeH.
{ apply wf_ctx_insert. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear VL CL HL RL JL WFHL WFFL WFIL. apply TypeCasesØ.
+ specialize (HL _ _ _ _ H2) as IHh.
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCasesU. auto.
  do 2 rewrite ctx_insert_extend. auto.
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
{ apply wf_ctx_insert. inv orig. all:assumption. }
{ destruct orig; eauto. }
{ destruct orig; eauto. }
destruct orig. destruct H2.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
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
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqPair; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqLeft; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqRight; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqNil; auto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqCons; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqFun; auto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHc.
  specialize (JL _ _ _ H3) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqHandler; eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in IH. eapply VeqSubsume; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. rewrite <-v_shift_comm. apply ηFun. omega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd; auto.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqProdMatch. eauto.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc1.
  specialize (JL _ _ _ H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqSumMatch. eauto.
  all: rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc1.
  specialize (JL _ _ _ H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqListMatch; eauto.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqDo. eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IHv1.
  specialize (JL _ _ _ H3) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp; eauto.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle; eauto.
+ specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqLetRec; eauto.
  do 2 rewrite ctx_insert_extend. rewrite hyp_shift_comm; eaomega.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H3) as IHv.
  specialize (JL _ _ _ H4) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqOp; eauto.
  rewrite ctx_insert_extend, hyp_shift_comm; eaomega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in IH. eapply CeqSubsume; eauto.
+ specialize (WFIL _ _ _ H3) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply OOTB; eauto.
  rewrite <-c_shift_inst. rewrite H4. simpl. auto.
  rewrite <-c_shift_inst. rewrite H5. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchPair as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchLeft as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchRight as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchNil as rule.
  unfold c_subs_out in *. simpl. 
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchCons as rule.
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
  specialize βDoRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. simpl. rewrite <-c_shift_comm. 
  eapply βDoOp. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleOp as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl in *.
  rewrite c_shift_subs, c_shift_subs. simpl. 
  rewrite <-(c_shift_comm 1 (S(S i))), <-(c_shift_comm 1 (S i)).
  rewrite <-(c_shift_comm 1 (S i)), <-h_shift_comm, <-(h_shift_comm 1 i).
  eapply rule. apply shift_get_case_Some. eauto. all: omega.
+ specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs. simpl.
    eapply ηEmpty. specialize (ctx_len_insert_trivial Γ i A_ins) as triv. omega.
    rewrite <-ctx_insert_comm. all: aomega.
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt.
    eapply ηEmpty. rewrite ctx_len_insert; omega.
    rewrite ctx_insert_comm. all: aomega.
+ specialize (CL _ _ _ H3) as IHc.
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
+ specialize (CL _ _ _ H3) as IHc.
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
+ specialize (CL _ _ _ H3) as IHc.
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
  simpl. apply ηDo.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply DoLoop.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply HandleLoop.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply HeqSym. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigØ. 
+ specialize (JL _ _ _ H4) as IHc.
  specialize (JL _ _ _ H5) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigU.
  - eapply shift_get_case_Some in H2. eauto.
  - eapply shift_get_case_Some in H3. eauto.
  - rewrite ctx_insert_extend, ctx_insert_extend, hyp_shift_comm; eaomega.
  - eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H5 A_ins (2+i)) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply HeqExtend; eauto.
  all: try apply shift_get_case_None; auto.
  rewrite hyp_shift_comm; aomega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply IsHyp. apply has_hypothesis_shift. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TruthIn.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply FalsityEl. simpl in IH. auto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply AndIn; auto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElLeft. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElRight. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrLefteft. auto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrRightight. auto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  specialize (JL _ _ _ H4) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply OrEl; auto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ImpliesIn. auto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ImpliesEl; eauto.
+ specialize (JL _ _ _ H2 A_ins (S i) wfins) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ForallIn. rewrite hyp_shift_comm; aomega.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (VL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_shift_subs.
  eapply ForallEl; eauto. omega.
+ specialize (VL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3 A_ins i wfins) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_shift_subs in IH2.
  eapply ExistsIn; eauto. omega.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3 A_ins (S i)) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ExistsEl. eapply IH1. auto.
  rewrite hyp_shift_comm, form_shift_comm; aomega.
+ specialize (JL _ _ _ H3 A_ins (S i)) as IH1.
  assert (
  forall op Aop Bop,
     get_op_type Σ op = Some (Aop, Bop) ->
     judg (CtxU (CtxU (ctx_insert Γ i A_ins) Aop) (TyFun Bop (CTy A Σ E)))
       (HypU (hyp_shift (hyp_shift Ψ 2 0) 1 (S (S i)))
          (Forall Bop
             (form_shift
                (form_subs (form_shift φ 3 0) 3 (Fun TyUnit (App (Var 2) (Var 1))))
                1 (3+i))))
       (form_shift
          (form_subs (form_shift φ 2 0) 2 
            (Fun TyUnit (Op op Aop Bop (Var 2) (App (Var 2) (Var 0))))) 1 (2+i))
  ) as IH2.
  { intros op Aop Bop gets. specialize (H4 op Aop Bop gets).
    specialize (JL _ _ _ H4 A_ins (2+i) wfins) as IH.
    clear VL CL HL RL JL WFHL WFFL WFIL.
    simpl in *. auto. }
  specialize (JL _ _ _ H5 A_ins i) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply CompInduction; eauto.
  - apply var_admissible_shift; aomega.
  - rewrite form_shift_subs, <-form_shift_comm, <-hyp_shift_comm in IH1.
    simpl in IH1. all: aomega.
  - intros op Aop Bop gets. specialize (IH2 op Aop Bop gets).
    rewrite hyp_shift_comm. rewrite form_shift_subs in IH2.
    rewrite form_shift_comm. simpl in *. rewrite form_shift_subs in IH2.
    rewrite (form_shift_comm 1 (S i)). simpl in *. all: aomega.
  - rewrite form_shift_subs in IH3. simpl in IH3. auto. omega.
}{
intros wfins. inv orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply WfHypØ.
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
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfTruth. apply wf_ctx_insert; auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfFalsity. apply wf_ctx_insert; auto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfAnd; auto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfOr; auto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfImplies; auto.
+ specialize (WFFL _ _ H0 A_ins (S i) wfins) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfForall. auto. simpl in IHf. apply IHf.
+ specialize (WFFL _ _ H0 A_ins (S i) wfins) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfExists. auto. simpl in IHf. apply IHf.
}{
intros wfins. inv orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply WfInstØ.
  apply wf_ctx_insert; auto.
+ specialize (VL _ _ _ H) as IHv.
  specialize (WFIL _ _ _ H0) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstU; auto.
}
Qed.

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

with wf_hyp_shift_typesafe Γ Ψ A0 :
  wf_hyp Γ Ψ -> wf_vtype A0 ->
  wf_hyp (CtxU Γ A0) (hyp_shift Ψ 1 0)

with wf_form_shift_typesafe Γ φ A0 :
  wf_form Γ φ -> wf_vtype A0 ->
  wf_form (CtxU Γ A0) (form_shift φ 1 0)

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
apply wf_hyp_insert_typesafe. assumption.
apply wf_form_insert_typesafe. assumption.
apply wf_inst_insert_typesafe. assumption.
Qed.


Lemma v_join_ctxs_typesafe_left Γ Γ' v A :
  has_vtype Γ v A -> wf_ctx Γ' -> 
  has_vtype (join_ctxs Γ Γ') (v_shift v (ctx_len Γ') 0) A.
Proof.
intros; induction Γ'; simpl.
+ rewrite v_shift_0. assumption.
+ assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H1.
  rewrite <-v_shift_shift. apply v_shift_typesafe; inv H0; auto.
Qed.


Lemma c_join_ctxs_typesafe_left Γ Γ' c C :
  has_ctype Γ c C -> wf_ctx Γ' -> 
  has_ctype (join_ctxs Γ Γ') (c_shift c (ctx_len Γ') 0) C.
Proof.
intros; induction Γ'; simpl.
+ rewrite c_shift_0. assumption.
+ assert (S(ctx_len Γ')=ctx_len Γ'+1) by omega. rewrite H1.
  rewrite <-c_shift_shift. apply c_shift_typesafe; inv H0; auto.
Qed.


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
Qed.


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
Qed.


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
Qed.


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
Qed.

(* ==================== Hypotheses weakening. ==================== *)

Fixpoint hypotheses_weakening Γ Ψ φ (orig: judg Γ Ψ φ) Ψ' {struct orig}:
  wf_hyp Γ Ψ' -> hyp_subset Ψ Ψ' -> judg Γ Ψ' φ.
Proof.
intros wfh subset.
apply WfJudg. destruct orig. auto. destruct orig. auto. auto.
destruct orig. destruct H2.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply VeqVar; eauto.
+ apply VeqUnit.
+ apply VeqInt.
+ apply VeqPair; eauto.
+ eapply VeqLeft; eauto.
+ eapply VeqRight; eauto.
+ apply VeqNil; eauto. 
+ apply VeqCons; eauto.
+ apply VeqFun; auto. eapply hypotheses_weakening. eauto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H2. inv H3. auto.
  - apply hyp_subset_shift. auto.
+ eapply VeqHandler; eauto. eapply hypotheses_weakening. eauto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H2. inv H4. auto.
  - apply hyp_subset_shift. auto.
+ eapply VeqSubsume; eauto.
+ apply ηUnit.
+ apply ηFun.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto.
+ eapply CeqProdMatch; eauto.
  eapply hypotheses_weakening. eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hyp_shift_typesafe; auto.
    apply wf_hyp_shift_typesafe; auto.
    all: inv H3; inv H4. inv H9. auto. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqSumMatch; eauto.
  all: eapply hypotheses_weakening; eauto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H3. inv H5. auto.
  - apply hyp_subset_shift. auto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H4. inv H5. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqListMatch; eauto.
  eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hyp_shift_typesafe; auto.
    apply wf_hyp_shift_typesafe; auto.
    all: inv H4; inv H5. inv H10. auto. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqDo; eauto.
  eapply hypotheses_weakening. eauto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H3. inv H4. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec; eauto. 
  all: eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hyp_shift_typesafe; auto.
    apply wf_hyp_shift_typesafe; auto.
    all: inv H2; inv H4. inv H10. auto. auto.
  - apply hyp_subset_shift. auto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H2. inv H4. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqOp; eauto.
  eapply hypotheses_weakening. eauto.
  - apply wf_hyp_shift_typesafe; auto.
    inv H4. inv H5. auto.
  - apply hyp_subset_shift. auto.
+ eapply CeqSubsume; eauto.
+ eapply OOTB; eauto.
+ eapply βMatchPair.
+ eapply βMatchLeft.
+ eapply βMatchRight.
+ eapply βMatchNil.
+ eapply βMatchCons.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoRet.
+ eapply βDoOp.
+ eapply βHandleRet.
+ eapply βHandleOp. auto.
+ eapply ηEmpty; eauto.
+ eapply ηPair; eauto.
+ eapply ηSum; eauto.
+ eapply ηList; eauto.
+ eapply ηDo; eauto.
+ eapply DoLoop.
+ eapply HandleLoop.
+ eapply HeqSym; eauto.
+ eapply HeqTrans; eauto.
+ eapply HeqSigØ.
+ eapply HeqSigU; eauto.
  eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hyp_shift_typesafe; auto.
    apply wf_hyp_shift_typesafe; auto.
    all: inv H4; inv H6. inv H11. auto. auto.
  - apply hyp_subset_shift. auto.
+ eapply HeqExtend; eauto.  eapply hypotheses_weakening; eauto.
  - rewrite <-(hyp_shift_shift 1).
    apply wf_hyp_shift_typesafe; auto.
    apply wf_hyp_shift_typesafe; auto.
    all: inv H0; inv H10. auto. apply WfTyFun; auto. inv H14. auto. 
  - apply hyp_subset_shift. auto.
+ apply IsHyp. eapply hyp_subset_has_hypothesis; eauto.
+ apply TruthIn.
+ apply FalsityEl. eauto.
+ apply AndIn; eauto.
+ eapply AndElLeft. eauto.
+ eapply AndElRight. eauto.
+ apply OrLefteft. eauto.
+ apply OrRightight. eauto.
+ apply OrEl; eauto.
+ apply ImpliesIn. eapply hypotheses_weakening; eauto. 
  apply WfHypU. auto. inv H0. auto. apply SubsetHypU.
  apply hyp_subset_extend. auto. simpl. left. auto.
+ eapply ImpliesEl. 2: eauto. eauto.
+ apply ForallIn. eapply hypotheses_weakening; eauto.
  apply wf_hyp_shift_typesafe; auto. inv H0. auto.
  apply hyp_subset_shift. auto.
+ eapply ForallEl; eauto.
+ eapply ExistsIn; eauto.
+ eapply ExistsEl. eauto. eapply hypotheses_weakening; eauto.
  - apply WfHypU. apply wf_hyp_shift_typesafe; auto. 
    all: inv H2; inv H5; auto.
  - apply SubsetHypU. apply hyp_subset_extend.
    apply hyp_subset_shift. auto.
    simpl. left. auto.
+ eapply CompInduction; eauto.
  - eapply hypotheses_weakening; eauto.
    apply wf_hyp_shift_typesafe; auto. inv H0. inv H9. inv H8. auto.
    apply hyp_subset_shift. auto.
  - intros op Aop Bop gets. specialize (H4 op Aop Bop gets).
    apply get_op_type_wf in gets. destruct gets.
    eapply hypotheses_weakening; eauto.
    * apply WfHypU. rewrite <-(hyp_shift_shift 1).
      apply wf_hyp_shift_typesafe. apply wf_hyp_shift_typesafe. 
      3: apply WfTyFun. all: auto. inv H0. inv H11. auto.
      inv H4. inv H10. auto.
    * apply SubsetHypU. apply hyp_subset_extend. apply hyp_subset_shift. auto.
      simpl. auto.
    * inv H0. inv H9. inv H8. auto.
Qed.

(* ==================== Better Logic Reflexivity. ==================== *)

(* Defined here because we need it in next proof.*)
Lemma veq_refl Γ Ψ v A : 
  has_vtype Γ v A   -> wf_hyp Γ Ψ -> judg Γ Ψ (Veq A v v)
with ceq_refl Γ Ψ c C : 
  has_ctype Γ c C   -> wf_hyp Γ Ψ -> judg Γ Ψ (Ceq C c c)
with heq_refl Γ Ψ h Σ D : 
  has_htype Γ h Σ D -> wf_hyp Γ Ψ -> judg Γ Ψ (Heq Σ D h h).
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

with wf_hyp_sub_typesafe
  Γ Ψ (orig: wf_hyp Γ Ψ) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_hyp Γ (hyp_sub Ψ (i, v_s))

with wf_form_sub_typesafe
  Γ φ (orig: wf_form Γ φ) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_form Γ (form_sub φ (i, v_s))

with wf_inst_sub_typesafe
  Γ I Γ' (orig: wf_inst Γ I Γ') i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_inst Γ (inst_sub I (i, v_s)) Γ'.

Proof.
all: rename v_sub_typesafe into VL; rename c_sub_typesafe into CL.
all: rename h_sub_typesafe into HL; rename respects_sub_typesafe into RL.
all: rename judg_sub_typesafe into JL.
all: rename wf_hyp_sub_typesafe into WFHL.
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
  apply TypeLeft; eauto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeRight; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeNil; eauto.
+ specialize (VL _ _ _ H1) as IHv1. 
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCons; eauto.
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
  eapply TypeVSubsume; eauto.
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
  simpl. eapply TypeProdMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeSumMatch. eauto.
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
  simpl. eapply TypeDo. eauto.
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
+ specialize (VL _ _ _ H4) as IHv. 
  specialize (CL _ _ _ H5) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H5. inv H6. apply v_shift_typesafe; auto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply TypeCSubsume; eauto.
}{
intros gets tyvs; simpl; apply TypeH; inv orig. auto. auto. auto.
destruct H2.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  apply TypeCasesØ.
+ specialize (HL _ _ _ _ H2) as IHh. 
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TypeCasesU; eauto.
  eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
  apply v_shift_typesafe. apply v_shift_typesafe. assumption.
  all: inv H0. assumption. apply WfTyFun; assumption.
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
{ destruct orig. auto. }
{ destruct orig; eauto. }
{ destruct orig; eauto. }
destruct orig. destruct H2.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqTrans; simpl in IH1; simpl in IH2; eauto.
+ specialize (WFHL _ _ H1) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  subst. simpl.
  destruct (i0 =? i) eqn:cmp.
  - apply (veq_refl _ (hyp_sub Ψ (i, v_s))) in tyvs; auto.
    apply Nat.eqb_eq in cmp. subst. rewrite gets in H2. inv H2.
    inv tyvs. auto. eauto.
  - eapply VeqVar; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqInt.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqPair; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqLeft; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqRight; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply VeqNil; eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
    simpl. apply VeqCons; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqFun; auto. rewrite hyp_shift_sub. eapply IH.
  - simpl. eauto.
  - apply v_shift_typesafe; auto. inv H0. inv H6. inv H3. auto.
  - omega.
+ specialize (JL _ _ _ H2) as IHc.
  specialize (JL _ _ _ H3) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply VeqHandler; eauto. rewrite hyp_shift_sub. eapply IHc.
  - simpl. eauto.
  - apply v_shift_typesafe; auto. inv H0. inv H7. inv H4. inv H8. auto.
  - omega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply VeqSubsume; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. rewrite <-v_shift_sub. apply ηFun. omega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans. eapply IH1; eauto. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd; auto.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqProdMatch. eapply IHv; eauto.
  rewrite hyp_shift_sub. eapply IHc.
  - simpl. eauto.
  - rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe; auto. apply v_shift_typesafe; auto.
    all: inv H3; inv H4. inv H9. auto. auto.
  - omega.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc1.
  specialize (JL _ _ _ H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqSumMatch. eapply IHv; eauto.
  - rewrite hyp_shift_sub. eapply IHc1. simpl. eauto. 
    apply v_shift_typesafe. auto. 
    inv H3. inv H5. auto. omega.
  - rewrite hyp_shift_sub. eapply IHc2. simpl. eauto.
    apply v_shift_typesafe. auto.
    inv H4. inv H5. auto. omega.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc1.
  specialize (JL _ _ _ H4) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqListMatch. eapply IHv; eauto.
  - eapply IHc1; eauto.
  - rewrite hyp_shift_sub. eapply IHc2. simpl. eauto. 
    rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe. apply v_shift_typesafe. auto.
    all: inv H4; inv H5. inv H11. all: aomega.
+ specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqDo. eapply IHc1; eauto.
  rewrite hyp_shift_sub. eapply IHc2.
  - simpl. eauto.
  - apply v_shift_typesafe. auto. 
    inv H3; inv H4. auto.
  - omega.
+ specialize (JL _ _ _ H2) as IHv1.
  specialize (JL _ _ _ H3) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp. eapply IHv1; eauto. eapply IHv2; eauto.
+ specialize (JL _ _ _ H2) as IHv.
  specialize (JL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle. eapply IHv; eauto. eapply IHc; eauto.
+ specialize (JL _ _ _ H2) as IHc1.
  specialize (JL _ _ _ H3) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqLetRec; eauto.
  - rewrite hyp_shift_sub. eapply IHc1. simpl. eauto.
    rewrite <-(v_shift_shift 1 1). apply v_shift_typesafe; auto.
    apply v_shift_typesafe; auto.
    all: inv H3; inv H4. inv H10. all: aomega.
  - rewrite hyp_shift_sub. eapply IHc2. simpl. eauto.
    apply v_shift_typesafe. auto.
    inv H3. inv H4. all: aomega.
+ specialize (JL _ _ _ H3) as IHv.
  specialize (JL _ _ _ H4) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqOp; eauto.
  rewrite hyp_shift_sub. eapply IHc. simpl. eauto.
  apply v_shift_typesafe. assumption.
  apply get_op_type_wf in H2. destruct H2. assumption.
  inv H0. inv H8. inv H5. auto. omega.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply CeqSubsume; eauto.
+ specialize (WFIL _ _ _ H3) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  clear H3. eapply OOTB; eauto.
  rewrite <-c_sub_inst. rewrite H4. simpl. auto.
  rewrite <-c_sub_inst. rewrite H5. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchPair as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchLeft as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchRight as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchNil as rule.
  unfold c_subs_out in *. simpl. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchCons as rule.
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
  specialize βDoRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoOp as rule.
  simpl. rewrite v_shift_comm, <-c_shift_sub. 
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleOp as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl in *.
  rewrite c_sub_subs, c_sub_subs. simpl.
  rewrite v_shift_comm, <-c_shift_sub, <-h_shift_sub, <-h_shift_sub.
  rewrite (v_shift_comm 1 1), <-c_shift_sub.
  rewrite (v_shift_comm 1 0 0 1), <-c_shift_sub. eapply rule.
  rewrite <-v_shift_comm, v_shift_shift. apply sub_get_case_Some.
  eauto. all: omega.
+ specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs; aomega. simpl.
    eapply ηEmpty; auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. apply WfTyEmpty.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt; aomega. simpl.
    eapply ηEmpty; aomega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. apply WfTyEmpty.
+ specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs. simpl.
    assert (S(S n)=2+n) as samen by omega.
    assert (S(S(S i))=2+(S i)) as samei by omega.
    rewrite samei, samen, <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηPair. auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt; aomega.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(S n)=2+n) as samen by omega.
    simpl. rewrite samei, samen, <-v_shift_comm, <-c_shift_sub; aomega.
    eapply ηPair. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
+ specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs, c_sub_subs; aomega. simpl.
    assert (S(S i)=1+(S i)) as samei by omega.
    rewrite samei, <-v_shift_comm, <-c_shift_sub; aomega.
    eapply ηSum. auto. eapply IHc.
    * erewrite <-get_ctx_insert_changed. eauto. omega.
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt, c_sub_subs_alt. simpl.
    rewrite <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηSum. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
+ specialize (CL _ _ _ H3) as IHc.
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
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt, c_sub_subs_alt. simpl.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(S n)=2+n) as samen by omega.
    rewrite samei, samen, <-v_shift_comm, <-c_shift_sub. all: aomega.
    eapply ηList. omega. eapply IHc.
    * erewrite <-get_ctx_insert_unchanged. eauto. omega.
    * apply v_insert_typesafe; auto. inv H3. 
      apply wf_ctx_insert_vtype in H4. auto. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL. 
  simpl. apply ηDo.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply DoLoop.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply HandleLoop.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSym; eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply HeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigØ. 
+ specialize (JL _ _ _ H4) as IHc.
  specialize (JL _ _ _ H5) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigU.
  - eapply sub_get_case_Some in H2. eauto.
  - eapply sub_get_case_Some in H3. eauto.
  - rewrite hyp_shift_sub. eapply IHc. simpl. eauto.
    rewrite <-(v_shift_shift 1 1). 
    apply v_shift_typesafe. apply v_shift_typesafe; auto.
    all: inv H4; inv H6. inv H11. all: aomega.
  - eauto.
+ specialize (JL _ _ _ H2) as IHh.
  specialize (JL _ _ _ H5 (2+i)) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply HeqExtend; eauto.
  - apply sub_get_case_None. auto.
  - apply sub_get_case_None. auto.
  - rewrite hyp_shift_sub; aomega. simpl. eapply IHc. eauto.
    rewrite <-(v_shift_shift 1). 
    apply v_shift_typesafe. apply v_shift_typesafe. auto.
    all: inv H5; inv H6; inv H11; auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply IsHyp. apply has_hypothesis_sub. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TruthIn.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply FalsityEl. simpl in IH. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply AndIn; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElLeft. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElRight. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrLefteft. eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrRightight. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  specialize (JL _ _ _ H4) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply OrEl; eauto.
+ specialize (JL _ _ _ H2) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ImpliesIn. eauto.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ImpliesEl; eauto.
+ specialize (JL _ _ _ H2 (S i)) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ForallIn. rewrite hyp_shift_sub. 
  eapply IH. eauto. apply v_shift_typesafe; auto.
  inv H0. auto. omega.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (VL _ _ _ H3) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_sub_subs.
  eapply ForallEl; eauto. omega.
+ specialize (VL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3 i v_s A_s) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_sub_subs in IH2.
  eapply ExistsIn. eapply IH1; eauto. all: eaomega.
+ specialize (JL _ _ _ H2) as IH1.
  specialize (JL _ _ _ H3 (S i)) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ExistsEl. eapply IH1; eauto.
  rewrite hyp_shift_sub, form_shift_sub; aomega.
  eapply IH2. eauto. apply v_shift_typesafe; auto.
  inv H2. inv H5. auto.
+ specialize (JL _ _ _ H3 (S i) (v_shift v_s 1 0) A_s gets) as IH1.
  assert (
  forall op Aop Bop,
     get_op_type Σ op = Some (Aop, Bop) ->
     judg (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
       (hyp_sub
          (HypU (hyp_shift Ψ 2 0)
             (Forall Bop
                (form_subs (form_shift φ 3 0) 3 (Fun TyUnit (App (Var 2) (Var 1))))))
          (2 + i, v_shift v_s 2 0))
       (form_sub
          (form_subs (form_shift φ 2 0) 2
             (Fun TyUnit (Op op Aop Bop (Var 2) (App (Var 2) (Var 0)))))
          (2 + i, v_shift v_s 2 0))
  ) as IH2.
  { intros op Aop Bop gets'. specialize (H4 op Aop Bop gets').
    specialize (JL _ _ _ H4 (2+i) (v_shift v_s 2 0)) as IH.
    clear VL CL HL RL JL WFHL WFFL WFIL.
    simpl in *. eapply IH; eauto. rewrite <-(v_shift_shift 1).
    apply get_op_type_wf in gets'. destruct gets'.
    apply v_shift_typesafe. apply v_shift_typesafe; auto. 
    apply WfTyFun; auto. inv H0. inv H11. auto. inv H0. inv H9. inv H8. auto. }
  specialize (JL _ _ _ H5 i v_s A_s gets) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  inv H0. inv H9.
  simpl in *. eapply CompInduction; eauto.
  - apply var_admissible_sub; aomega. apply v_shift_makes_no_var.
  - clear IH2. rewrite form_sub_subs in IH1. simpl in IH1.
    rewrite form_shift_sub, v_shift_comm, hyp_shift_sub. 
    simpl in *. all: aomega.
    apply IH1. apply v_shift_typesafe. auto. inv H8. auto.
  - intros op Aop Bop gets'. specialize (IH2 op Aop Bop gets').
    apply get_op_type_wf in gets'. destruct gets'.
    rewrite hyp_shift_sub, form_shift_sub.
    rewrite form_sub_subs, form_sub_subs in IH2.
    simpl in *. rewrite v_shift_shift in IH2. simpl in IH2.
    rewrite form_shift_sub, v_shift_comm, (v_shift_comm 1 0).
    all: aomega. inv H8. auto.
  - rewrite form_sub_subs in IH3. simpl in IH3. auto. omega.
}{
intros gets vtys. inv orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply WfHypØ.
+ specialize (WFHL _ _ H) as IHhy.
  specialize (WFFL _ _ H0) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfHypU; eauto.
}{
intros gets vtys. inv orig.
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
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfTruth. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfFalsity. auto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfAnd; eauto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfOr; eauto.
+ specialize (WFFL _ _ H) as IHf1.
  specialize (WFFL _ _ H0) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfImplies; eauto.
+ specialize (WFFL _ _ H0) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfForall. auto. eapply IHf.
  simpl. eauto. apply v_shift_typesafe; auto.
+ specialize (WFFL _ _ H0) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfExists. auto. eapply IHf.
  simpl. eauto. apply v_shift_typesafe; auto.
}{
intros gets vtys. destruct orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstØ. auto.
+ specialize (VL _ _ _ H) as IHv.
  specialize (WFIL _ _ _ orig) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL. 
  simpl. apply WfInstU; eauto.
}
Qed.


(* ==================== Safety and Subs. ==================== *)


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

with judg_subs_typesafe
  Γ Γ' Ψ φ (orig: judg Γ' Ψ φ) i v_s A_s {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ (hyp_subs Ψ i v_s) (form_subs φ i v_s)

with wf_hyp_subs_typesafe
  Γ Γ' Ψ (orig: wf_hyp Γ' Ψ) i v_s A_s {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  wf_hyp Γ (hyp_subs Ψ i v_s)

with wf_form_subs_typesafe
  Γ Γ' φ (orig: wf_form Γ' φ) i v_s A_s {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  wf_form Γ (form_subs φ i v_s)

with wf_inst_subs_typesafe
  Γ Γ' I Γ0 i v_s A_s (orig: wf_inst Γ' I Γ0) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  wf_inst Γ (inst_subs I i v_s) Γ0.

Proof.
all: rename v_subs_typesafe into VL; rename c_subs_typesafe into CL.
all: rename h_subs_typesafe into HL; rename respects_subs_typesafe into RL.
all: rename judg_subs_typesafe into JL.
all: rename wf_hyp_subs_typesafe into WFHL.
all: rename wf_form_subs_typesafe into WFFL.
all: rename wf_inst_subs_typesafe into WFIL.
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
  apply TypeLeft; auto.  
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeRight; auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeNil; auto.
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH1.
  specialize (VL Γ Γ0 vs _ i _ _ H2 tyvs geq) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeCons; auto.
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
  eapply TypeVSubsume; eauto.
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
  eapply TypeProdMatch. eauto. 
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
  eapply TypeSumMatch. eauto. 
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
  eapply TypeDo. eauto. 
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
  assert (wf_vtype Bop) as wfb. { inv H5. inv H6. auto. }
  specialize (v_shift_typesafe _ _ Bop _ tyvs wfb) as tyvsb.
  specialize (VL _ _ v _ i _ _ H4 tyvs geq) as IHv.
  specialize (CL _ _ c _ (1+i) _ _ H5 tyvsb geqb) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CL Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubsume; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2. 
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeH; auto; unfold h_subs; simpl.
  apply TypeCasesØ.
+ assert (CtxU (CtxU Γ0 A) (TyFun B D) 
    = ctx_insert (CtxU (CtxU Γ A) (TyFun B D)) (2+i) A_s).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; auto).
  assert (wf_vtype (TyFun B D)) as wfb by (inv H0; apply WfTyFun; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs' wfb) as tyvs''.
  specialize (HL _ _ h _ _ i _ _ H2 tyvs geq) as IHh.
  specialize (CL _ _ c _ (2+i) _ _ H3 tyvs'' H4) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply TypeH; auto; unfold h_subs; simpl.
  eapply TypeCasesU; auto.
  rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
  simpl. omega. omega.
}{
intros tysh tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H3. 
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsØ.
+ specialize (RL _ _ _ _ _ _ i v_s _ H3 tysh tyvs geq) as IHr.
  specialize (JL (join_ctxs (join_ctxs Γ (tctx_to_ctx Z D)) Γ0) 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ0) HypØ
    (Ceq D 
      (handle_t D (ctx_len Γ0) (tctx_len Z) h T1) 
      (handle_t D (ctx_len Γ0) (tctx_len Z) h T2) )
    H4 (i + tctx_len Z + ctx_len Γ0) 
    (v_shift v_s (tctx_len Z+ctx_len Γ0) 0) A_s ) as IHc.
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
intros tyvs geq len. apply WfJudg.
{ destruct orig. subst. eapply wf_ctx_insert_rev. eauto. }
{ destruct orig; eauto. }
{ destruct orig; eauto. }
destruct orig. destruct H2.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply VeqSym. apply IH; auto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqTrans; eauto.
+ specialize (WFHL _ _ _ H1 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  subst. simpl. unfold v_subs. simpl.
  rename i0 into j. destruct (j =? i) eqn:cmp. 
  - rewrite v_negshift_shift, v_shift_0.
    eapply (veq_refl _ (hyp_subs Ψ i v_s)) in tyvs.
    apply Nat.eqb_eq in cmp. subst. 
    erewrite get_ctx_insert_new in H2. inv H2. inv tyvs. all: eaomega.
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
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply VeqPair; auto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqLeft; eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. eapply VeqRight; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
unfold v_subs. simpl. apply VeqNil; auto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply VeqCons; auto.
+ assert (wf_vtype A) as wfa. 
  { clear VL CL HL RL JL WFHL WFFL WFIL. inv H0. inv H8. inv H3. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (JL _ _ _ _ H2 (S i) _ _ tyvs') as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold v_subs. simpl. eapply VeqFun; auto.
  rewrite v_shift_comm, hyp_shift_subs_alt.
  apply IH. simpl. f_equal. auto.
  all: simpl; omega.
+ assert (wf_vtype A) as wfa.
  { clear VL CL HL RL JL WFHL WFFL WFIL. inv H0. inv H7. inv H4. inv H8. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (JL _ _ _ _ H2 (S i) _ _ tyvs') as IHc.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IHh.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold v_subs. simpl. eapply VeqHandler; eauto.
  rewrite v_shift_comm, hyp_shift_subs_alt. 
  apply IHc. simpl. f_equal. auto.
  all: simpl; omega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply VeqSubsume; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  unfold v_subs. simpl. apply ηUnit.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold v_subs. simpl.
  rewrite <-v_shift_sub, <-v_shift_negshift_comm; aomega. apply ηFun.
  apply v_sub_makes_no_var. apply v_shift_makes_no_var.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply CeqSym. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqTrans; eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqRet. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply CeqAbsurd; auto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHv.
  assert (wf_vtype A) as wfa.
  { inv H3. inv H4. inv H9. auto. }
  assert (wf_vtype B) as wfb.
  { inv H3. inv H4. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (JL _ _ _ _ H3 (2+i) _ _ tyvs'') as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqProdMatch. eauto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1); aomega.
  rewrite <-(hyp_shift_shift 1), hyp_shift_subs_alt, hyp_shift_subs_alt.
  rewrite hyp_shift_shift.
  apply IHc. simpl. do 2 f_equal. all: simpl; aomega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHv.
  assert (wf_vtype A) as wfa.
  { inv H3. inv H5. auto. }
  assert (wf_vtype B) as wfb.
  { inv H4. inv H5. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (JL _ _ _ _ H3 (S i) _ _ tyvsa) as IHc1.
  specialize (JL _ _ _ _ H4 (S i) _ _ tyvsb) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqSumMatch. eauto.
  all: rewrite v_shift_comm, hyp_shift_subs_alt.
  all: apply IHc1 || apply IHc2 || aomega.
  all: simpl; aomega; f_equal; auto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHv.
  assert (wf_vtype A) as wfa.
  { inv H4. inv H5. inv H11. auto. }
  assert (wf_vtype (TyList A)) as wfla.
  { inv H4. inv H5. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyList A) _ tyvs' wfla) as tyvs''.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IHc1.
  specialize (JL _ _ _ _ H4 (2+i) _ _ tyvs'') as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqListMatch; eauto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1); aomega.
  rewrite <-(hyp_shift_shift 1), hyp_shift_subs_alt, hyp_shift_subs_alt.
  rewrite hyp_shift_shift.
  apply IHc2. simpl. do 2 f_equal. all: simpl; aomega.
+ assert (wf_vtype A) as wfa.
  { inv H3. inv H4. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHc1.
  specialize (JL _ _ _ _ H3 (S i) _ _ tyvsa) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqDo. eauto.
  rewrite v_shift_comm, hyp_shift_subs_alt. 
  apply IHc2. simpl. f_equal. all: simpl; aomega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHv1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqApp; eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IHv.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. eapply CeqHandle; eauto.
+ assert (wf_vtype A) as wfa.
  { inv H3. inv H4. inv H10. auto. }
  assert (wf_vtype (TyFun A C)) as wff.
  { inv H3. inv H4. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' wff) as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs wff) as tyvs'''.
  specialize (JL _ _ _ _ H2 (2+i) _ _ tyvs'') as IHc1.
  specialize (JL _ _ _ _ H3 (1+i) _ _ tyvs''') as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqLetRec.
  all: rewrite v_shift_comm; eaomega.
  - rewrite <-(v_shift_shift 1 1), <-(hyp_shift_shift 1).
    rewrite hyp_shift_subs_alt, hyp_shift_subs_alt, hyp_shift_shift.
    eapply IHc1. simpl. do 2 f_equal. all: simpl; aomega.
  - rewrite hyp_shift_subs_alt. apply IHc2.
    simpl. f_equal. all: simpl; aomega.
+ assert (wf_vtype Bop) as wfb.
  { inv H4. inv H5. auto. }
  specialize (v_shift_typesafe _ _ Bop _ tyvs wfb) as tyvsb.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IHv.
  specialize (JL _ _ _ _ H4 (S i) _ _ tyvsb) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. unfold c_subs. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm, hyp_shift_subs_alt.
  apply IHc. simpl. f_equal. all: simpl; aomega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply CeqSubsume; eauto.
+ specialize (WFIL _ _ _ _ i _ _ H3 tyvs) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply OOTB; eauto.
  rewrite <-c_subs_inst. rewrite H4. simpl. auto.
  rewrite <-c_subs_inst. rewrite H5. simpl. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchPair as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ProdMatch (Pair v1 v2) c) i v_s 
    = ProdMatch (Pair (v_subs v1 i v_s) (v_subs v2 i v_s)) 
        (c_subs c (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H2. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchLeft as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (SumMatch (Left A B v) c1 c2) i v_s
    = SumMatch (Left A B (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; aomega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchRight as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (SumMatch (Right A B v) c1 c2) i v_s
    = SumMatch (Right A B (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; aomega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchNil as rule.
  unfold c_subs_out in *. simpl.
  assert (c_subs (ListMatch (Nil A) c1 c2) i v_s 
    = ListMatch (Nil A) 
        (c_subs c1 i v_s)
        (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βMatchCons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ListMatch (Cons v vs) c1 c2) i v_s
    = ListMatch (Cons (v_subs v i v_s) (v_subs vs i v_s))
        (c_subs c1 i v_s)
        (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H2. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (App (Fun A c) v) i v_s 
    = App (Fun A (c_subs c (1+i) (v_shift v_s 1 0))) (v_subs v i v_s)).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (LetRec A C c1 c2) i v_s
    = LetRec A C (c_subs c1 (2+i) (v_shift v_s 2 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. simpl. do 2 f_equal; rewrite v_shift_comm; auto || omega. }  
  rewrite H2. clear H1.
  assert ( v_subs (Fun A (LetRec A C (c_shift c1 1 2) c1)) i v_s
    = Fun A (LetRec A C
       (c_shift (c_subs c1 (2+i) (v_shift v_s 2 0)) 1 2)
       (c_subs c1 (2+i) (v_shift v_s 2 0))) ).
  { unfold c_subs. unfold v_subs. simpl. do 2 f_equal.
    rewrite v_shift_comm, <-c_shift_sub, c_shift_negshift_comm.
    do 2 f_equal. rewrite v_shift_comm. all: aomega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    do 3 f_equal. rewrite v_shift_shift, v_shift_comm; aomega. }
  rewrite H1. clear H1. apply rule. omega.  
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (Do (Ret v) c) i v_s 
    = Do (Ret (v_subs v i v_s)) (c_subs c (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βDoOp as rule.
  simpl. unfold c_subs_out in *. unfold c_subs. simpl. rewrite v_shift_comm. 
  specialize (rule op A B
    (v_negshift (v_sub v (i, v_shift v_s 1 i)) 1 i)
    (c_negshift
      (c_sub c1 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i))) 1 (S i))
    (c_negshift
      (c_sub c2 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i))) 1 (S i))).
  rewrite c_shift_negshift_comm, c_shift_sub in rule. simpl.
  assert (v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 0
    = v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 1).
  { rewrite <-v_shift_comm, v_shift_comm. all: aomega. }
  rewrite H2. apply rule. all: aomega. clear rule.
  apply c_sub_makes_no_var. apply v_shift_makes_no_var.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleRet as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (Handle (Handler A c_r h) (Ret v)) i v_s
    = Handle (Handler A
      (c_subs c_r (1+i) (v_shift v_s 1 0)) (h_subs h i v_s)) 
      (Ret (v_subs v i v_s) ) ).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; aomega. }  
  rewrite H2. apply rule. all: omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  specialize βHandleOp as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (Handle (Handler A c_r h) (Op op Aop Bop v c_k)) i v_s =
    Handle (Handler A (c_subs c_r (1+i) (v_shift v_s 1 0)) (h_subs h i v_s))
    (Op op Aop Bop (v_subs v i v_s) (c_subs c_k (1+i) (v_shift v_s 1 0)))).
  { unfold c_subs. unfold v_subs. simpl. do 5 f_equal;
    apply v_shift_comm; omega. }
  rewrite H3. clear H3.
  assert (v_subs (Fun Bop
    (Handle (Handler A (c_shift (c_shift c_r 1 1) 1 2) 
    (h_shift (h_shift h 1 0) 1 1)) (c_shift c_k 1 1))) (S i) (v_shift v_s 1 0)
  = Fun Bop (Handle (v_shift (Handler A (c_subs (c_shift c_r 1 1) (2+i) 
      (v_shift v_s 2 0)) (h_subs (h_shift h 1 0) (S i) (v_shift v_s 1 0))) 1 0)
      (c_subs (c_shift c_k 1 1) (2+i) (v_shift v_s 2 0)))).
  { clear rule. unfold v_subs. unfold c_subs. unfold h_subs. 
    simpl. do 3 f_equal.
    rewrite c_shift_negshift_comm, c_shift_sub. do 2 f_equal.
    rewrite <-c_shift_comm. all: aomega. f_equal.
    rewrite v_shift_comm. f_equal. rewrite v_shift_comm, v_shift_shift.
    all: aomega. apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite h_shift_negshift_comm, h_shift_sub, <-h_shift_comm. all: aomega.
    apply h_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite v_shift_comm, v_shift_shift; aomega. }
  rewrite H3, v_shift_shift. clear H3. simpl in *.
  rewrite <-(v_shift_shift 1 1), v_shift_comm, <-(c_shift_subs_alt _ _ 1).
  rewrite <-c_shift_subs_alt, <-h_shift_subs_alt.
  rewrite h_shift_comm, c_shift_comm.
  eapply rule. 
  apply negshift_get_case_Some. rewrite <-(v_shift_comm 1 0 0 1), v_shift_shift.
  simpl. rewrite <-(v_shift_comm 1 i).
  apply sub_get_case_Some. all:eaomega.
+ specialize (v_insert_typesafe _ _ _ tyvs (TyEmpty) n WfTyEmpty) as tyv.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyv) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyEmpty) (n-1) WfTyEmpty) as tyvm.
  specialize (CL _ _ c _ (i) _ _ H3 tyvm) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (c_subs (Absurd C v) i v_s = Absurd C (v_subs v i v_s) ).
  { unfold c_subs. simpl. auto. }
  rewrite H4. clear H4.
  destruct (n<=?i) eqn:ni.
  - clear IHc.
    apply leb_complete in ni.
    rewrite c_subs_subs. simpl. apply ηEmpty; auto. omega.
    apply IHcp. subst. rewrite ctx_insert_comm. all: aomega.
    rewrite ctx_len_insert; omega.
  - clear IHcp.
    apply leb_complete_conv in ni.
    destruct n. omega.
    rewrite (c_subs_subs_alt _ n). all: aomega. simpl.
    apply ηEmpty; auto.
    subst. rewrite ctx_len_insert in H2. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n TyEmpty) as triv. omega.
+ assert (wf_vtype (TyProd A B)) as wfab.
  { inv H3. apply wf_ctx_insert_vtype in H4. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TyProd A B) n wfab) as tyvsab.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyvsab) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyProd A B) (n-1) wfab) as tyvsabm.
  specialize (CL _ _ c _ (i) _ _ H3 tyvsabm) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c, c_subs (ProdMatch v c) i v_s 
    = ProdMatch (v_subs v i v_s) (c_subs c (2+i) (v_shift v_s 2 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H4. clear H4.
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
    rewrite H4. clear H4. eapply ηPair. all: aomega.
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
    rewrite H4. clear H4. 
    assert (S(S n)=2+n) as samen by omega.
    rewrite samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    eapply ηPair. all: aomega.
    subst. rewrite ctx_len_insert in H2. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TyProd A B)) as triv. omega.
+ assert (wf_vtype (TySum A B)) as wfab.
  { inv H3. apply wf_ctx_insert_vtype in H4. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TySum A B) n wfab) as tyvsab.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyvsab) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TySum A B) (n-1) wfab) as tyvsabm.
  specialize (CL _ _ c _ (i) _ _ H3 tyvsabm) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c1 c2, c_subs (SumMatch v c1 c2) i v_s 
    = SumMatch (v_subs v i v_s) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H4. clear H4.
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
    eapply ηSum. subst. rewrite ctx_len_insert in H2. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TySum A B)) as triv. omega.
+ assert (wf_vtype (TyList A)) as wfla.
  { inv H3. apply wf_ctx_insert_vtype in H4. auto. auto. }
  specialize (v_insert_typesafe _ _ _ tyvs (TyList A) n wfla) as tyvsla.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyvsla) as IHcp.
  specialize (v_insert_typesafe _ _ _ tyvs (TyList A) (n-1) wfla) as tyvslam.
  specialize (CL _ _ c _ (i) _ _ H3 tyvslam) as IHc.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  assert (forall c1 c2, c_subs (ListMatch v c1 c2) i v_s 
    = ListMatch (v_subs v i v_s) 
        (c_subs c1 i v_s) (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { intros c1' c2'. unfold c_subs. simpl. rewrite v_shift_comm; aomega. }
  rewrite H4. clear H4.
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
    assert (v_subs (Cons (Var 1) (Var 0)) (S(S i)) (v_shift v_s 2 0) 
      = (Cons (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H4. clear H4. eapply ηList. all: aomega.
    apply IHcp. subst. rewrite ctx_insert_comm. all: aomega.
    rewrite ctx_len_insert; omega.
  - clear IHcp.
    apply leb_complete_conv in ni.
    destruct n. omega.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ n), (c_subs_subs_alt _ ).
    all: aomega. simpl.
    specialize ηList as rule.
    assert (v_subs (Cons (Var 1) (Var 0)) (S (S i)) (v_shift v_s 2 0)
      = (Cons (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H4. clear H4. 
    assert (S(S n)=2+n) as samen by omega.
    rewrite samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    eapply ηList. all: aomega.
    subst. rewrite ctx_len_insert in H2. omega. omega.
    assert (S n - 1 = n) as n0 by omega. rewrite n0 in *.
    apply IHc. subst. rewrite ctx_insert_comm; aomega.
    specialize (ctx_len_insert_trivial Γ n (TyList A)) as triv. omega.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply ηDo.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply DoLoop.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply HandleLoop.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply HeqSym. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL. apply HeqSigØ.
+ assert (wf_vtype A) as wfa.
  { inv H4. inv H6. inv H11. auto. }
  assert (wf_vtype (TyFun B D)) as wff.
  { inv H4. inv H6. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs' wff) as tyvs''.
  specialize (JL _ _ _ _ H4 (2+i) _ _ tyvs'') as IH1.
  specialize (JL _ _ _ _ H5 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply HeqSigU; eauto.
  - unfold h_subs. eapply negshift_get_case_Some.
    eapply sub_get_case_Some. eauto.
  - unfold h_subs. eapply negshift_get_case_Some.
    eapply sub_get_case_Some. eauto.
  - rewrite v_shift_comm, <-(v_shift_shift 1 1), <-(hyp_shift_shift 1).
    rewrite hyp_shift_subs_alt, hyp_shift_subs_alt, hyp_shift_shift.
    apply IH1. simpl. do 2 f_equal. all: simpl; aomega.
+ assert (wf_vtype A) as wfa.
  { inv H5. inv H6. inv H11. auto. }
  assert (wf_vtype (TyFun B D)) as wff.
  { inv H5. inv H6. auto. }
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs' wff) as tyvs''.
  specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H5 (2+i) _ _ tyvs'') as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. unfold h_subs. simpl. apply HeqExtend; eauto.
  - apply negshift_get_case_None. apply sub_get_case_None. auto.
  - apply negshift_get_case_None. apply sub_get_case_None. auto.
  - rewrite <-(hyp_shift_shift 1), hyp_shift_subs_alt, hyp_shift_subs_alt.
    rewrite hyp_shift_shift, (v_shift_comm 1 i), <-(v_shift_shift 1 1).
    unfold c_subs in *. apply IH2. all: aomega.
    do 2 f_equal. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply IsHyp. apply has_hypothesis_subs. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply TruthIn.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply FalsityEl. simpl in IH. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply AndIn; eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElLeft. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply AndElRight. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrLefteft. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply OrRightight. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  specialize (JL _ _ _ _ H4 i _ _ tyvs) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply OrEl; eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ImpliesIn. eauto.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ImpliesEl; eauto.
+ specialize (JL (CtxU Γ A) _ _ _ H2 (S i) (v_shift v_s 1 0)) as IH.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. apply ForallIn. rewrite hyp_shift_subs_alt. 
  eapply IH. eauto. apply v_shift_typesafe; eauto.
  inv H0. auto. f_equal. auto. all: omega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (VL _ _ _ _ i _ _ H3 tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_subs_subs.
  eapply ForallEl; eauto. omega.
+ specialize (VL _ _ _ _ i _ _ H2 tyvs) as IH1.
  specialize (JL _ _ _ _ H3 i _ _ tyvs) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. rewrite form_subs_subs in IH2.
  eapply ExistsIn. eapply IH1; eauto. all: eaomega.
+ specialize (JL _ _ _ _ H2 i _ _ tyvs) as IH1.
  specialize (JL (CtxU Γ A) _ _ _ H3 (S i) (v_shift v_s 1 0)) as IH2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl in *. eapply ExistsEl. eapply IH1; eauto.
  rewrite hyp_shift_subs_alt, form_shift_subs_alt; aomega.
  eapply IH2. eauto. apply v_shift_typesafe; eauto.
  inv H2. inv H5. auto. f_equal. auto. omega.
+ specialize (JL (CtxU Γ A) _ _ _ H3 (S i) ) as IH1.
  assert (
  forall op Aop Bop,
     get_op_type Σ op = Some (Aop, Bop) ->
     judg (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
       (hyp_subs
          (HypU (hyp_shift Ψ 2 0)
             (Forall Bop
                (form_subs (form_shift φ 3 0) 3 (Fun TyUnit (App (Var 2) (Var 1))))))
          (2 + i) (v_shift v_s 2 0))
       (form_subs
          (form_subs (form_shift φ 2 0) 2
             (Fun TyUnit
              (Op op Aop Bop (Var 2) (App (Var 2) (Var 0))))) (2 + i) (v_shift v_s 2 0))
  ) as IH2.
  { intros op Aop Bop gets'. specialize (H4 op Aop Bop gets').
    specialize 
      (JL (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E))) _ _ _ H4 (2+i)) as IH.
    all: clear VL CL HL RL JL WFHL WFFL WFIL.
    simpl in *. eapply IH; eauto. clear IH1 IH. 
    rewrite <-(v_shift_shift 1).
    apply get_op_type_wf in gets'. destruct gets'.
    apply v_shift_typesafe. apply v_shift_typesafe; eauto. 
    apply WfTyFun; auto. inv H0. inv H11. auto. inv H0. inv H9. inv H8. auto.
    do 2 f_equal. auto. omega. }
  specialize (JL Γ _ _ _ H5 i ) as IH3.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  inv H0. inv H9.
  simpl in *. eapply CompInduction; eauto.
  - apply var_admissible_subs; aomega. apply v_shift_makes_no_var.
  - clear IH2. specialize (IH1 (v_shift v_s 1 0) A_s).
    rewrite form_subs_subs in IH1. simpl in IH1. unfold v_subs in IH1.
    rewrite form_shift_subs_alt, v_shift_comm, hyp_shift_subs_alt. 
    simpl in *. all: aomega.
    apply IH1. apply v_shift_typesafe. auto. inv H8. all: aomega.
  - intros op Aop Bop gets'. specialize (IH2 op Aop Bop gets').
    apply get_op_type_wf in gets'. destruct gets'.
    rewrite <-(hyp_shift_shift 1).
    rewrite <-(form_shift_shift 1), <-(form_shift_shift 1).
    rewrite hyp_shift_subs_alt, hyp_shift_subs_alt, hyp_shift_shift.
    rewrite form_shift_subs_alt, form_shift_subs_alt, form_shift_subs_alt.
    rewrite <-(form_shift_shift 1 1), form_shift_subs_alt, form_shift_subs_alt.
    rewrite form_shift_shift, form_shift_shift, v_shift_shift, v_shift_shift.
    rewrite form_shift_shift, v_shift_shift, v_shift_shift. simpl.
    rewrite form_subs_subs, v_shift_shift in IH2. simpl in IH2.
    rewrite (form_subs_subs (form_shift φ 2 0)) in IH2.
    rewrite <-(v_shift_comm 1 0 0 3), v_shift_shift in IH2.
    rewrite <-(v_shift_comm 1 0 0 2), v_shift_shift in IH2.
    unfold v_subs in IH2. simpl in *. all: aomega. inv H8. auto.
  - clear IH1 IH2. specialize (IH3 v_s A_s tyvs). 
    rewrite form_subs_subs in IH3. unfold v_subs in IH3. simpl in IH3.
    apply IH3. all: aomega.
}{
intros tyvs geq len. destruct orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfHypØ.
+ specialize (WFFL _ _ _ H i _ _ tyvs geq) as IHv.
  specialize (WFHL _ _ _ orig i _ _ tyvs geq) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  apply WfHypU; eauto.
}{
intros tyvs geq len. destruct orig.
+ specialize (VL _ _ _ _ i _ _ H tyvs geq) as IHv1.
  specialize (VL _ _ _ _ i _ _ H0 tyvs geq) as IHv2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfVeq; eauto.
+ specialize (CL _ _ _ _ i _ _ H tyvs geq) as IHc1.
  specialize (CL _ _ _ _ i _ _ H0 tyvs geq) as IHc2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfCeq; eauto.
+ specialize (HL _ _ _ _ _ i _ _ H2 tyvs geq) as IHh1.
  specialize (HL _ _ _ _ _ i _ _ H3 tyvs geq) as IHh2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  eapply WfHeq. 2: exact H0. all: eauto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfTruth. inv tyvs. auto.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  apply WfFalsity. inv tyvs. auto.
+ specialize (WFFL _ _ _ orig1 i _ _ tyvs geq) as IHf1.
  specialize (WFFL _ _ _ orig2 i _ _ tyvs geq) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfAnd; eauto.
+ specialize (WFFL _ _ _ orig1 i _ _ tyvs geq) as IHf1.
  specialize (WFFL _ _ _ orig2 i _ _ tyvs geq) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfOr; eauto.
+ specialize (WFFL _ _ _ orig1 i _ _ tyvs geq) as IHf1.
  specialize (WFFL _ _ _ orig2 i _ _ tyvs geq) as IHf2.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfImplies; eauto.
+ specialize (WFFL (CtxU Γ A) _ _ orig (S i)) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfForall. auto. eapply IHf.
  apply v_shift_typesafe; eauto. simpl. f_equal. auto. simpl. omega.
+ specialize (WFFL (CtxU Γ A) _ _ orig (S i)) as IHf.
  clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfExists. auto. eapply IHf.
  apply v_shift_typesafe; eauto. simpl. f_equal. auto. simpl. omega.
}{
intros tyvs geq len. destruct orig.
+ clear VL CL HL RL JL WFHL WFFL WFIL.
  simpl. apply WfInstØ. inv tyvs. auto.
+ specialize (VL _ _ _ _ i _ _ H tyvs geq) as IHv.
  specialize (WFIL _ _ _ _ i _ _ orig tyvs geq) as IHwf.
  clear VL CL HL RL JL WFHL WFFL WFIL. simpl.
  apply WfInstU; eauto.
}
Qed.


(* ==================== Templates as Terms ==================== *)

Fixpoint tmpl_to_comp_has_ctype Γ Z T A Σ E (orig: wf_t Γ Z T Σ):
  wf_ctype (CTy A Σ E) -> wf_ctx Γ -> wf_tctx Z ->
  has_ctype 
    (join_ctxs (tctx_to_ctx Z (CTy A Σ E)) Γ) 
    (tmpl_to_comp (CTy A Σ E) (ctx_len Γ) T) 
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
+ eapply TypeProdMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in orig. auto.
    apply WfCtxU. apply WfCtxU. all: inv H1; inv H3; auto.
+ eapply TypeSumMatch.
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
  eapply TypeDo; eauto. instantiate (1:=A0).
  - apply c_join_ctxs_typesafe_right; auto. apply TypeC; auto.
    apply WfCTy; inv wfd; auto.
    eapply TypeCSubsume; eauto. apply STyCTy.
    * apply vsubtype_refl. auto.
    * apply STySigØ.
    * apply STyEqsØ.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in *. auto. apply WfCtxU; auto.
+ eapply TypeOp; eauto.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eapply tmpl_to_comp_has_ctype in orig; eauto.
    simpl in orig. auto.
    apply WfCtxU. auto. inv wfd. apply get_op_type_wf in H1.
    destruct H1. auto. auto.
Qed.


(* ==================== Handling templates ==================== *)

(* Auxilliary lemmas *)
Fixpoint cop_join_ctxs_special Γ' Γ A B D c {struct Γ}:
  wf_ctx Γ -> has_ctype (CtxU (CtxU Γ' A) (TyFun B D)) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs Γ' Γ) A) (TyFun B D)) 
    (c_shift c (ctx_len Γ) 2) D.
Proof.
intros wfg tys.
destruct Γ; simpl.
+ rewrite c_shift_0. auto.
+ assert (CtxU (CtxU (CtxU (join_ctxs Γ' Γ) v) A) (TyFun B D)
    = ctx_insert (CtxU (CtxU (join_ctxs Γ' Γ) A) (TyFun B D)) 2 v).
  { simpl. do 2 f_equal. destruct Γ; simpl. destruct Γ'; simpl. all: auto. }
  assert (S (ctx_len Γ) = ctx_len Γ + 1) by omega.
  rewrite H, H0. rewrite <-(c_shift_shift). apply c_insert_typesafe.
  all: inv wfg; auto.
Qed.

Fixpoint cop_with_full_ctx_types Γ' Γ Z A B D c:
  wf_ctx Γ -> wf_tctx Z ->
  has_ctype (CtxU (CtxU Γ' A) (TyFun B D)) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A) (TyFun B D)) 
    (c_shift c (tctx_len Z + ctx_len Γ) 2) D.
Proof.
intros wfg wfz tys.
rewrite <-join_ctxs_assoc. 
erewrite len_tctx_to_ctx, <-len_join_ctxs.
apply cop_join_ctxs_special. apply wf_join_ctxs. apply wf_tctx_to_ctx.
all: auto. inv tys. auto.
Qed.


Fixpoint handle_t_types Γ Z T Σ Γ' h D (orig: wf_t Γ Z T Σ) {struct orig}:
  wf_ctx Γ -> wf_tctx Z -> has_htype Γ' h  Σ D ->
  has_ctype 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (handle_t D (ctx_len Γ) (tctx_len Z) h T) D.
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
+ apply TypeC; auto. eapply TypeProdMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A) B
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU (CtxU Γ A) B)). 
    { simpl.  reflexivity. }
    assert (S (S (ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) B)).
    { simpl. reflexivity. }
    rewrite H1, H2. eapply handle_t_types; eauto.
    apply WfCtxU. apply WfCtxU. auto. all: inv H0; inv H4; auto.
+ apply TypeC; auto. eapply TypeSumMatch.
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
  eapply TypeDo; eauto. instantiate (1:=A).
  - apply c_join_ctxs_typesafe_right; auto. apply TypeC; auto.
    apply WfCTy; inv H; auto.
    eapply TypeCSubsume; eauto. apply STyCTy.
    * apply vsubtype_refl. auto.
    * apply STySigØ.
    * apply STyEqsØ.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z (CTy B Σ' E'))) Γ) A
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z (CTy B Σ' E'))) (CtxU Γ A)). 
    { simpl. reflexivity. }
    rewrite H1. eapply handle_t_types; eauto. apply WfCtxU; auto.
+ specialize (h_has_case Γ' h Σ D op A B tys H0) as has.
  destruct has as [cop finds].
  eapply case_has_type in finds as coptys; eauto. rewrite finds.
  unfold c_subs2_out.
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)) Aop).
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (CtxU(join_ctxs (join_ctxs Γ'(tctx_to_ctx Z D)) Γ) Aop) (TyFun Bop D))).
  - assert (ctx_len Γ + tctx_len Z = tctx_len Z + ctx_len Γ) as same by omega.
    rewrite same. apply cop_with_full_ctx_types; eauto.
    eapply ctx_subtype_ctype; eauto.
    * do 2 try apply WfCtxU || apply WfTyFun; auto. inv tys. auto.
    * do 2 try apply STyCtxU || apply STyFun; auto. 
      all: inv tys; apply ctx_subtype_refl || apply csubtype_refl; auto.
  - apply v_shift_typesafe.
    apply TypeV. auto. 3: auto. apply WfTyFun; eauto. 
    apply TypeFun.
    assert (S (ctx_len Γ) = ctx_len (CtxU Γ Bop)) as samelen by (simpl; auto).
    assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) Bop
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ Bop)).
    { simpl. reflexivity. }
    rewrite samelen, H6. eapply handle_t_types; eauto.
    apply WfCtxU; auto.
  - simpl. auto.
  - omega.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (forall γ A, CtxU γ A = ctx_insert γ 0 A).
    { intros. induction γ; simpl; auto. }
    rewrite H6. auto.
  - omega.
Qed.
