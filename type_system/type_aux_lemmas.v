Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic". *)

Require Export syntax_lemmas substitution_lemmas subtyping_lemmas
  logic_aux_lemmas.
Open Scope string_scope.

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
Admitted.


Lemma wf_is_under_ctx_tctx Γ Z T Σ:
  wf_t Γ Z T Σ -> 
  t_under_var T (ctx_len Γ) /\ t_under_tvar T (tctx_len Z).
Proof.
revert Γ. induction T; intros Γ wf.
+ inv wf. simpl. constructor.
  - eapply has_vtype_is_under_ctx. eauto.
  - apply tctx_len_gets in H5. omega.
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
  eapply has_vtype_is_under_ctx. eauto.
  all: apply IHT in H7; destruct H7; assumption.
Admitted.


Lemma handle_t_no_var h i Γ Z T Σ:
  h_no_var h i -> wf_t Γ Z T Σ ->
  c_no_var (handle_t (ctx_len Γ) (tctx_len Z) h T) 
    (i + tctx_len Z + ctx_len Γ).
Proof.
revert h Γ i. induction T; intros; simpl.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ constructor.
  all: apply wf_is_under_ctx_tctx in H0; destruct H0; simpl in *. 
  omega. eapply v_under_var_no_var. eauto. omega.
+ apply wf_is_under_ctx_tctx in H0. destruct H0.
  eapply v_under_var_no_var. eauto. omega.
+ constructor; inv H0.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. eauto. omega.
  - rewrite slen, slen, (sctx A), (sctx B). eauto.
+ inv H0. constructor. 2: constructor.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. eauto. omega.
  - rewrite slen, (sctx A). auto. 
  - rewrite slen, (sctx B). auto. 
+ inv H0. constructor. 2: constructor.
  - eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. eauto. omega.
  - auto. 
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto. 
+ destruct (find_case h o) eqn:finds; inv H0.
  - apply c_no_var_subs. apply c_no_var_subs. all: omega || simpl.
    * eapply find_case_no_var in finds; eauto.
      assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+(2+i)) by omega.
      rewrite H0. apply c_no_var_shift. eauto. omega.
    * apply v_no_var_shift. eapply v_under_var_no_var.
      eapply has_vtype_is_under_ctx. eauto. all: omega.
    * rewrite slen, (sctx B_op). eauto.
  - simpl. constructor.
    * eapply v_under_var_no_var. eapply has_vtype_is_under_ctx. eauto. omega.
    * rewrite slen, (sctx B_op). eauto.
Admitted.

(* ==================== Handling and Shifts. ==================== *)

Lemma handle_t_shift Γ' Γ Z h T Σ D i:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (h_shift h 1 i) T
  = c_shift (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + tctx_len Z + ctx_len Γ).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ simpl. apply tctx_len_gets in H5 as zlen. 
  destruct ((i + tctx_len Z + ctx_len Γ) <=? ctx_len Γ + v) eqn:cmp.
  { apply leb_complete in cmp. omega. }
  f_equal. rewrite v_shift_too_high. auto.
  eapply has_vtype_is_under_ctx in H3.  
  eapply v_under_var_weaken. eauto. omega.
+ f_equal. rewrite v_shift_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken. eauto. omega.
+ f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken. eauto. omega.
  - rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - rewrite slen, (sctx A). auto.
  - rewrite slen, (sctx B). auto.
  + f_equal.
  - rewrite v_shift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - auto.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  erewrite shift_find_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_shift_subs. 2: omega. f_equal; simpl. 
  * rewrite c_shift_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+tctx_len Z+ctx_len Γ))=(tctx_len Z+ctx_len Γ)+S(S i))
    as cext by omega. rewrite cext.
    rewrite c_shift_comm. f_equal. omega. omega.
    rewrite (v_shift_too_high (v_shift v 1 0)). auto.
    apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_weaken. eauto. omega. omega. 
  * f_equal. rewrite slen, (sctx B_op). auto. 
Admitted.


Lemma handle_t_negshift Γ' Γ Z h T Σ D i:
  h_no_var h i -> wf_t Γ Z T Σ -> has_htype Γ' h Σ D -> 
    handle_t (ctx_len Γ) (tctx_len Z) (h_negshift h 1 i) T
  = c_negshift (handle_t (ctx_len Γ) (tctx_len Z) h T) 
      1 (i + tctx_len Z + ctx_len Γ).
Proof.
revert Γ h i. induction T; intros Γ h i novar wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ apply tctx_len_gets in H5 as zlen. simpl.
  destruct ((i + tctx_len Z + ctx_len Γ) <=? ctx_len Γ + v) eqn:cmp.
  - apply leb_complete in cmp. omega.
  - f_equal. rewrite v_negshift_too_high. auto.
    eapply has_vtype_is_under_ctx in H3.  
    eapply v_under_var_weaken. eauto. omega.
+ f_equal. rewrite v_negshift_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken. eauto. omega.
+ f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken. eauto. omega.
  - rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - rewrite slen, (sctx A). auto.
  - rewrite slen, (sctx B). auto.
  + f_equal.
  - rewrite v_negshift_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - auto.
  - rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+S(S i))
  as cext by omega.
  eapply find_case_no_var in find as cop_novar; eauto.
  erewrite negshift_find_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_negshift_subs. 2: omega. f_equal; simpl. 
  * rewrite c_negshift_subs. 2: omega. f_equal; simpl.
    rewrite cext, c_shift_negshift_comm. f_equal. auto. omega.
    rewrite v_negshift_too_high. auto.
    - apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
      eapply v_under_var_weaken. eauto. omega. omega. 
    - simpl. rewrite cext. apply c_no_var_shift. eauto. omega.
    - apply v_no_var_shift. apply has_vtype_is_under_ctx in H6.
      eapply v_under_var_no_var. eauto. omega. omega. 
  * f_equal. rewrite slen, (sctx B_op). auto.
  * apply c_no_var_subs. simpl. rewrite cext.
    apply c_no_var_shift. eauto. omega. 
    apply v_no_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_no_var. eauto. all: omega.
  * simpl. rewrite slen, (sctx B_op). eapply handle_t_no_var; eauto.
Admitted.


Lemma handle_t_sub Γ' Γ Z h T Σ D i v_s:
  wf_t Γ Z T Σ -> has_htype Γ' h Σ D ->
    handle_t (ctx_len Γ) (tctx_len Z) (h_sub h (i, v_s)) T
  = c_sub (handle_t (ctx_len Γ) (tctx_len Z) h T)
      (i+tctx_len Z+ctx_len Γ, v_shift v_s (tctx_len Z+ctx_len Γ) 0).
Proof.
revert Γ h i. induction T; intros Γ h i wf types; simpl; inv wf.
all: assert (forall A Γ, S(ctx_len Γ)=ctx_len (CtxU Γ A)) as sctx by
 (intros; simpl; omega).
all: assert (forall x, S(i+tctx_len Z+x) = i+tctx_len Z+S x) as slen by
  (intros; omega).
+ apply tctx_len_gets in H5 as zlen. simpl.
  destruct (ctx_len Γ + v =? i + tctx_len Z + ctx_len Γ) eqn:cmp.
  - apply Nat.eqb_eq in cmp. omega.
  - f_equal. rewrite v_sub_too_high. auto.
    eapply has_vtype_is_under_ctx in H3. 
    eapply v_under_var_weaken. eauto. omega.
+ f_equal. rewrite v_sub_too_high. auto.
  apply has_vtype_is_under_ctx in H2.
  eapply v_under_var_weaken. eauto. omega.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H3.
    eapply v_under_var_weaken. eauto. omega.
  - assert (tctx_len Z + ctx_len Γ + 2 = tctx_len Z + S(S(ctx_len Γ))) as same.
    omega. rewrite v_shift_shift, same.
    rewrite slen, slen, (sctx A), (sctx B). auto.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. rewrite v_shift_shift, same, slen, (sctx A). auto.
  - assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. rewrite v_shift_shift, same, slen, (sctx B). auto.
+ f_equal.
  - rewrite v_sub_too_high. auto.
    apply has_vtype_is_under_ctx in H4.
    eapply v_under_var_weaken. eauto. omega.
  - auto.
  - assert (tctx_len Z + ctx_len Γ + 2 = tctx_len Z + S(S(ctx_len Γ))) as same.
    omega. rewrite v_shift_shift, same.
    rewrite slen, slen, (sctx A), (sctx (TyList A)). auto.
+ eapply h_has_case in H4 as find. 2: exact types.
  destruct find as [cop find].
  erewrite sub_find_Some, find; eauto.
  unfold c_subs2_out. unfold c_subs_out.
  rewrite c_sub_subs. 2: omega. f_equal; simpl. 
  * rewrite c_sub_subs. 2: omega. f_equal; simpl.
    assert (S(S(i+tctx_len Z+ctx_len Γ))=(ctx_len Γ+tctx_len Z)+S(S i))
    as cext by omega. rewrite cext.
    rewrite c_shift_sub, v_shift_shift. do 2 f_equal. simpl.
    rewrite (v_shift_comm _ _ 0). f_equal. all: try omega.
    rewrite v_sub_too_high. auto.
    apply v_under_var_shift. apply has_vtype_is_under_ctx in H6.
    eapply v_under_var_weaken. eauto. omega. omega. 
  * assert (tctx_len Z + ctx_len Γ + 1 = tctx_len Z + S(ctx_len Γ)) as same.
    omega. f_equal. rewrite v_shift_shift, same, slen, (sctx B_op). auto.
Admitted.


(* ==================== Safety and Shifts. ==================== *)

Fixpoint v_insert_typesafe 
  Γ v A (orig : has_vtype Γ v A) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_vtype (ctx_insert Γ A_ins i) (v_shift v 1 i) A

with c_insert_typesafe 
  Γ c C (orig : has_ctype Γ c C) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_ctype (ctx_insert Γ A_ins i) (c_shift c 1 i) C

with h_insert_typesafe 
  Γ h Σ D (orig : has_htype Γ h Σ D) A_ins i {struct orig} :
  wf_vtype A_ins ->
  has_htype (ctx_insert Γ A_ins i) (h_shift h 1 i) Σ D

with respects_insert_typesafe
  Γ h Σ D E (orig: respects Γ h Σ D E) A_ins i {struct orig} :
  has_htype Γ h Σ D -> wf_vtype A_ins ->
  respects (ctx_insert Γ A_ins i) (h_shift h 1 i) Σ D E

with veq_insert_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  veq A (ctx_insert Γ A_ins i) (v_shift v1 1 i) (v_shift v2 1 i)

with ceq_insert_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  ceq C (ctx_insert Γ A_ins i) (c_shift c1 1 i) (c_shift c2 1 i)
  
with heq_insert_typesafe
  Γ Σ D h1 h2 (orig: heq Σ D Γ h1 h2) A_ins i {struct orig} :
  wf_vtype A_ins ->
  heq Σ D (ctx_insert Γ A_ins i) (h_shift h1 1 i) (h_shift h2 1 i)

with wf_inst_insert_typesafe
  Γ Γ' I (orig: wf_inst Γ I Γ') A_ins i {struct orig} : 
  wf_vtype A_ins ->
  wf_inst (ctx_insert Γ A_ins i) (inst_shift I 1 i) Γ'.

Proof.
all: rename v_insert_typesafe into V; rename c_insert_typesafe into CI.
all: rename h_insert_typesafe into HC; rename respects_insert_typesafe into R.
all: rename veq_insert_typesafe into VE; rename ceq_insert_typesafe into CE.
all: rename heq_insert_typesafe into HE; rename wf_inst_insert_typesafe into WF.
{
intros wfins. apply TypeV.
{ apply wf_ctx_insert. inv orig. assumption. assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ clear V CI HC R VE CE HE WF. simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE WF. simpl. apply TypeInt.
+ clear V CI HC R VE CE HE WF.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    assumption. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    assumption. apply leb_iff_conv in cmp. assumption.
+ specialize (V _ _ _ H1) as IHv1. specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. apply TypePair; auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. simpl. apply TypeInl. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. simpl. apply TypeInr. auto.
+ clear V CI HC R VE CE HE WF. simpl. apply TypeListNil.
+ specialize (V _ _ _ H1) as IHv1. specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. apply TypeListCons; auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE WF.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (HC _ _ _ _ H2) as IHh. specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHres.
  clear V CI HC R VE CE HE WF.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. eapply TypeVSubtype; auto.
}{
intros wfins. apply TypeC.
{ apply wf_ctx_insert. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. simpl. apply TypeRet. auto.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. simpl. apply TypeAbsurd. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeΠMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF.
  simpl. eapply TypeΣMatch. auto. all: rewrite ctx_insert_extend; auto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeListMatch; auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (CI _ _ _ H1) as IHc1. specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF.
  simpl. eapply TypeDoBind. auto. rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H1) as IHv. specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeApp; auto.
+ specialize (V _ _ _ H1) as IHv. specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeHandle; auto.
+ specialize (CI _ _ _ H1) as IHc1.
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (V _ _ _ H2) as IHv. specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE WF.
  simpl. eapply TypeOp. 3: rewrite ctx_insert_extend. all: eauto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE WF. eapply TypeCSubtype; auto.
}{
intros wfins. apply TypeH.
{ apply wf_ctx_insert. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear V CI HC R VE CE HE WF. apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE WF.
  simpl. apply TypeCasesU. 2: auto.
  - apply shift_find_None. assumption.
  - do 2 rewrite ctx_insert_extend. auto.
}{
intros types wfins. apply Respects.
{ clear V CI HC R VE CE HE WF. apply wf_ctx_insert. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H3.
+ clear V CI HC R VE CE HE WF. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ H3) as IHres. specialize (CE _ _ _ _ H4) as IHeq.
  clear V CI HC R VE CE HE WF. apply RespectEqsU. auto.
  rewrite join_ctxs_insert, join_ctxs_insert.
  erewrite handle_t_shift. erewrite handle_t_shift.
  rewrite <-len_tctx_to_ctx.
  assert (ctx_len Γ+(tctx_len Z+i) = i+tctx_len Z+ctx_len Γ) by omega.
  rewrite H5. apply IHeq.
  all: inv H2. all: try eassumption.
}{
intros wfins. apply Veq.
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H1.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. apply VeqSym. auto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE WF. subst. simpl. rename i0 into j.
  destruct (i <=? j) eqn:cmp; eapply VeqVar; eauto.
  - erewrite <-get_ctx_insert_changed. auto. apply leb_complete in cmp. auto.
  - erewrite <-get_ctx_insert_unchanged. assumption. 
    apply leb_complete_conv in cmp. assumption.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqInt.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. simpl. apply VeqPair; auto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqInr; eauto.
+ clear V CI HC R VE CE HE WF. simpl. eapply VeqListNil.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqListCons; eauto.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqFun.
  rewrite ctx_insert_extend. auto.
+ specialize (CE _ _ _ _ H1) as IHc.
  specialize (HE _ _ _ _ _ H2) as IHh.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqHandler; eauto.
  rewrite ctx_insert_extend. auto.
+ clear V CI HC R VE CE HE WF. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE WF. simpl. rewrite <-v_shift_comm. apply ηFun. omega.
}{
intros wfins. apply Ceq.
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H1.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. apply CeqSym. auto.
+ specialize (CE _ _ _ _ H1) as IH1.
  specialize (CE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqRet. auto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqAbsurd. auto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqΠMatch. auto.
  do 2 rewrite ctx_insert_extend. auto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc1.
  specialize (CE _ _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqΣMatch. auto.
  all: rewrite ctx_insert_extend; auto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc1.
  specialize (CE _ _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqListMatch; eauto.
  do 2 rewrite ctx_insert_extend. auto.
+ specialize (CE _ _ _ _ H1) as IHc1.
  specialize (CE _ _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqDoBind. eauto.
  rewrite ctx_insert_extend; auto.
+ specialize (VE _ _ _ _ H1) as IHv1.
  specialize (VE _ _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqHandle; eauto.
+ specialize (CE _ _ _ _ H1) as IHc1.
  specialize (CE _ _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqLetRec.
  do 2 rewrite ctx_insert_extend; auto.
  rewrite ctx_insert_extend; auto.
+ specialize (VE _ _ _ _ H2) as IHv.
  specialize (CE _ _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqOp; eauto.
  rewrite ctx_insert_extend; auto.
+ specialize (WF _ _ _ H2) as IHwf.
  clear V CI HC R VE CE HE WF. eapply OOTB; eauto.
  rewrite <-c_shift_inst. rewrite H3. simpl. auto.
  rewrite <-c_shift_inst. rewrite H4. simpl. auto.
+ clear V CI HC R VE CE HE WF. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl. 
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Cons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  simpl. rewrite <-c_shift_comm. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. simpl. rewrite <-c_shift_comm. 
  eapply βDoBind_Op. omega.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_shift_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_shift_subs, c_shift_subs, <-v_shift_comm.
  simpl. rewrite <-c_shift_comm, <-h_shift_comm.
  eapply rule. apply shift_find_Some. eauto. all: omega.
+ clear V CI HC R VE CE HE WF. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs. rewrite c_shift_subs. simpl.
    assert (S(S(S i))=2+(S i)) as same by omega.
    rewrite same, <-c_shift_comm. all: try omega.
    apply ηPair. rewrite ctx_len_insert. omega.
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt, c_shift_subs_alt.
    assert (S(S i)=2+i) as samei by omega.
    assert (1+S(S n)=2+(S n)) as samen by omega.
    rewrite samei, samen, <-c_shift_comm. all: try omega.
    apply ηPair. omega.
+ clear V CI HC R VE CE HE WF. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_shift_subs, c_shift_subs, c_shift_subs. simpl.
    assert (S(S i)=1+(S i)) as same by omega.
    rewrite same, <-c_shift_comm. all: try omega.
    apply ηSum.
  - apply leb_complete_conv in ni.
    rewrite c_shift_subs_alt, c_shift_subs_alt, c_shift_subs_alt. simpl.
    rewrite <-c_shift_comm. all: try omega.
    apply ηSum.
+ clear V CI HC R VE CE HE WF. simpl. apply ηDoBind.
}{
intros wfins. inv orig. destruct H4. 
+ specialize (HC _ _ _ _ H2) as IH1.
  specialize (HC _ _ _ _ H3) as IH2.
  clear V CI HC R VE CE HE WF. eapply Heq. 
  2: exact H0. all: eauto. apply HeqSigØ. 
+ specialize (HC _ _ _ _ H2) as IH1.
  specialize (HC _ _ _ _ H3) as IH2.
  specialize (CE _ _ _ _ H6) as IHc.
  specialize (HE _ _ _ _ _ H7) as IHh.
  clear V CI HC R VE CE HE WF. eapply Heq.
  2: exact H0. all: eauto. eapply HeqSigU.
  - eapply shift_find_Some in H4. eauto.
  - eapply shift_find_Some in H5. eauto.
  - rewrite ctx_insert_extend, ctx_insert_extend. eauto.
  - eauto.
}{
intros wfins. inv orig.
+ clear V CI HC R VE CE HE WF. apply WfInstØ.
  apply wf_ctx_insert; auto.
+ specialize (V _ _ _ H) as IHv.
  specialize (WF _ _ _ H0) as IHwf.
  clear V CI HC R VE CE HE WF. simpl.
  apply WfInstU; auto.
}
Admitted.


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

with veq_shift_typesafe Γ A v1 v2 A0 :
  veq A Γ v1 v2 -> wf_vtype A0 ->
  veq A (CtxU Γ A0) (v_shift v1 1 0) (v_shift v2 1 0)

with ceq_shift_typesafe Γ C c1 c2 A0 :
  ceq C Γ c1 c2 -> wf_vtype A0 ->
  ceq C (CtxU Γ A0) (c_shift c1 1 0) (c_shift c2 1 0)

with heq_shift_typesafe Γ Σ D h1 h2 A0 :
  heq Σ D Γ h1 h2 -> wf_vtype A0 ->
  heq Σ D (CtxU Γ A0) (h_shift h1 1 0) (h_shift h2 1 0)

with wf_inst_shift_typesafe Γ Γ' I A0 : 
  wf_inst Γ I Γ' -> wf_vtype A0 ->
  wf_inst (CtxU Γ A0) (inst_shift I 1 0) Γ'.

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
+ rewrite join_ctxs_left_unit. assumption.
+ rewrite join_ctxs_left_step.
  apply v_join_ctxs_typesafe_right. 
  rewrite <-(v_shift_too_high _ 1 (ctx_len Γ)).
  apply v_insert_typesafe. auto. inv H0. auto.
  eapply has_vtype_is_under_ctx. eauto. inv H0. auto.
Admitted.


Lemma v_join_all_ctxs_typesafe Γ Γ' Z D v A :
  has_vtype Γ' v A -> wf_ctx Γ -> wf_tctx Z -> wf_ctype D ->
  has_vtype (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
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
  has_ctype (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (c_shift c (tctx_len Z+ctx_len Γ) 0) C.
Proof.
intros. 
rewrite <-c_shift_shift.
apply c_join_ctxs_typesafe_left; auto.
erewrite len_tctx_to_ctx. apply c_join_ctxs_typesafe_left. auto.
apply wf_tctx_to_ctx; auto.
Admitted.


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

with veq_sub_typesafe
  Γ A v1 v2 (orig: veq A Γ v1 v2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  veq A Γ (v_sub v1 (i, v_s)) (v_sub v2 (i, v_s))

with ceq_sub_typesafe
  Γ C c1 c2 (orig: ceq C Γ c1 c2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  ceq C Γ (c_sub c1 (i, v_s)) (c_sub c2 (i, v_s))

with heq_sub_typesafe
  Γ Σ D h1 h2 (orig: heq Σ D Γ h1 h2) i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  heq Σ D Γ (h_sub h1 (i, v_s)) (h_sub h2 (i, v_s))

with wf_inst_sub_typesafe
  Γ I Γ' (orig: wf_inst Γ I Γ') i v_s A_s {struct orig} :
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  wf_inst Γ (inst_sub I (i, v_s)) Γ'.

Proof.
all: rename v_sub_typesafe into V; rename c_sub_typesafe into CI.
all: rename h_sub_typesafe into HC; rename respects_sub_typesafe into R.
all: rename veq_sub_typesafe into VE; rename ceq_sub_typesafe into CE.
all: rename heq_sub_typesafe into HE; rename wf_inst_sub_typesafe into WF.
{
intros gets tyvs. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear V CI HC R VE CE HE WF. 
  simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE WF. 
  simpl. apply TypeInt.
+ clear V CI HC R VE CE HE WF.
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv tyvs. assumption.
  - apply TypeVar. assumption.
+ specialize (V _ _ _ H1) as IHv1. 
  specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. apply TypePair; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE HE WF. apply TypeInl; eauto.
+ specialize (V _ _ _ H1) as IHv. clear V CI HC R VE CE HE WF. apply TypeInr; eauto.
+ clear V CI HC R VE CE HE WF. apply TypeListNil; eauto.
+ specialize (V _ _ _ H1) as IHv1. 
  specialize (V _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. apply TypeListCons; eauto.
+ specialize (CI _ _ _ H1) as IHc. 
  specialize (V _ _ _ tyvs) as IHvs.
  clear V CI HC R VE CE HE WF. simpl.
  apply TypeFun. eapply IHc. eauto. inv H0. apply v_shift_typesafe; auto.
+ specialize (HC _ _ _ _ H2) as IHh. 
  specialize (CI _ _ _ H1) as IHc.
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE HE WF. simpl. apply TypeHandler; eauto. eapply IHc. 
  exact gets. inv H0. inv H6. apply v_shift_typesafe; assumption.
+ specialize (V _ _ _ H1) as IHv.
  clear V CI HC R VE CE HE WF. eapply TypeVSubtype; eauto.
}{
intros gets tyvs. apply TypeC; inv orig.
assumption. assumption. destruct H1.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE HE WF. apply TypeRet; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  clear V CI HC R VE CE HE WF. apply TypeAbsurd; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeΠMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeΣMatch. eauto.
  - eapply IHc1. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
  - eapply IHc2. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc1.
  specialize (CI _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeListMatch. eauto.
  - eapply IHc1. exact gets. auto.
  - eapply IHc2. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1. inv H5. all:auto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeDoBind. eauto.
  eapply IHc2. exact gets. inv H1. inv H4. apply v_shift_typesafe; auto. 
+ specialize (V _ _ _ H1) as IHv. 
  specialize (V _ _ _ H2) as IHv0.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeApp; eauto.
+ specialize (V _ _ _ H1) as IHv. 
  specialize (CI _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeHandle; eauto.
+ specialize (CI _ _ _ H1) as IHc1. 
  specialize (CI _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeLetRec.
  - eapply IHc1. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. exact gets. inv H1. inv H3. apply v_shift_typesafe; auto.
+ specialize (V _ _ _ H2) as IHv. 
  specialize (CI _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H3. inv H4. apply v_shift_typesafe; auto.
+ specialize (CI _ _ _ H1) as IHc.
  clear V CI HC R VE CE HE WF. eapply TypeCSubtype; eauto.
}{
intros gets tyvs; simpl; apply TypeH; inv orig.
all: try assumption.
destruct H2.
+ clear V CI HC R VE CE HE WF. 
  apply TypeCasesØ.
+ specialize (HC _ _ _ _ H3) as IHh. 
  specialize (CI _ _ _ H4) as IHc.
  clear V CI HC R VE CE HE WF. simpl. apply TypeCasesU; eauto.
  - rewrite sub_find_None; auto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H0. 2: assumption. apply WfTyFun; assumption.
}{
intros htys gets tyvs; simpl. apply Respects; inv orig.
all: try assumption.
destruct H3.
+ clear V CI HC R VE CE HE WF. 
  apply RespectEqsØ.
+ specialize (CE _ _ _ _ H4) as IHc. 
  specialize (R _ _ _ _ _ H3) as IHr.
  clear V CI HC R VE CE HE WF.
  apply RespectEqsU. eauto. erewrite handle_t_sub. erewrite handle_t_sub.
  eapply IHc. all: inv H2; eauto. clear IHc IHr.
  * assert (i+tctx_len Z+ctx_len Γ=ctx_len Γ+(tctx_len Z+i)) as same by omega.
    erewrite same, <-get_join_ctxs_left, len_tctx_to_ctx, <-get_join_ctxs_left. 
    eauto.
  * eapply v_join_all_ctxs_typesafe; auto.
}{
intros gets tyvs. apply Veq.
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H1.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. apply VeqSym. eauto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE WF. subst. simpl.
  destruct (i0 =? i) eqn:cmp.
  - apply veq_refl in tyvs.
    inv H0. apply Nat.eqb_eq in cmp. subst. rewrite gets in H1.
    inv H1. eapply veq_subtype in tyvs; eauto. inv tyvs. assumption.
  - eapply VeqVar; eauto.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqInt.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. simpl. apply VeqPair; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqInr; eauto.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqListNil; eauto.
+ specialize (VE _ _ _ _ H1) as IH1.
  specialize (VE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. simpl. apply VeqListCons; eauto.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqFun. eapply IH.
  - simpl. eauto.
  - inv H. inv H3. apply v_shift_typesafe; auto.
+ specialize (CE _ _ _ _ H1) as IHc.
  specialize (HE _ _ _ _ _ H2) as IHh.
  clear V CI HC R VE CE HE WF. simpl. eapply VeqHandler; eauto. eapply IHc.
  - simpl. eauto.
  - inv H. inv H5. inv H8. apply v_shift_typesafe; auto.
+ clear V CI HC R VE CE HE WF. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE WF. simpl. rewrite <-v_shift_sub. apply ηFun. omega.
}{
intros gets vtys. apply Ceq.
{ inv orig; eauto. }
{ inv orig; eauto. }
inv orig. destruct H1.
+ specialize (CE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. apply CeqSym. eauto.
+ specialize (CE _ _ _ _ H1) as IH1.
  specialize (CE _ _ _ _ H2) as IH2.
  clear V CI HC R VE CE HE WF. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqRet. eauto.
+ specialize (VE _ _ _ _ H1) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqAbsurd. eauto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqΠMatch. eauto. eapply IHc.
  - simpl. eauto.
  - inv H1. inv H3. inv H6. rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe; auto. apply v_shift_typesafe; auto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc1.
  specialize (CE _ _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqΣMatch. eauto. all: inv H1; inv H4.
  - eapply IHc1. simpl. eauto. inv H7. apply v_shift_typesafe; assumption.
  - eapply IHc2. simpl. eauto. inv H7. apply v_shift_typesafe; assumption.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc1.
  specialize (CE _ _ _ _ H3) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqListMatch. eauto.
  - eapply IHc1; eauto.
  - eapply IHc2. simpl. eauto. rewrite <-(v_shift_shift 1 1).
    apply v_shift_typesafe. apply v_shift_typesafe. auto.
    all: inv H1; inv H4. inv H7. auto. auto.
+ specialize (CE _ _ _ _ H1) as IHc1.
  specialize (CE _ _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqDoBind. eauto. eapply IHc2.
  - simpl. eauto.
  - inv H1. inv H3. inv H6. apply v_shift_typesafe; assumption.
+ specialize (VE _ _ _ _ H1) as IHv1.
  specialize (VE _ _ _ _ H2) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ H1) as IHv.
  specialize (CE _ _ _ _ H2) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqHandle; eauto.
+ specialize (CE _ _ _ _ H1) as IHc1.
  specialize (CE _ _ _ _ H2) as IHc2.
  clear V CI HC R VE CE HE WF. simpl. inv H2. inv H4. eapply CeqLetRec.
  - eapply IHc1. simpl. eauto. rewrite <-(v_shift_shift 1 1).
    inv H2. apply v_shift_typesafe; auto. inv H10. apply v_shift_typesafe; auto.
  - eapply IHc2. simpl. eauto. inv H2. apply v_shift_typesafe; assumption.
+ specialize (VE _ _ _ _ H2) as IHv.
  specialize (CE _ _ _ _ H3) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqOp; eauto.
  eapply IHc. simpl. eauto. apply v_shift_typesafe. assumption.
  apply get_op_type_wf in H1. destruct H1. assumption. inv H. inv H5. auto.
+ specialize (WF _ _ _ H2) as IHwf.
  clear V CI HC R VE CE HE WF. clear H2. eapply OOTB; eauto.
  rewrite <-c_sub_inst. rewrite H3. simpl. auto.
  rewrite <-c_sub_inst. rewrite H4. simpl. auto.
+ clear V CI HC R VE CE HE WF. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Cons as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βLetRec as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  simpl. rewrite v_shift_comm, <-c_shift_sub, v_shift_shift. 
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βDoBind_Op as rule.
  simpl. rewrite v_shift_comm, <-c_shift_sub. 
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_sub_subs.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Op as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_sub_subs, c_sub_subs, <-v_shift_sub, v_shift_shift.
  simpl. rewrite v_shift_comm, <-c_shift_sub, <-h_shift_sub.
  simpl in rule. eapply rule. apply sub_find_Some. eauto. all: omega.
+ clear V CI HC R VE CE HE WF. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs. simpl.
    assert (S(S n)=2+n) as samen by omega.
    assert (S(S(S i))=2+(S i)) as samei by omega.
    rewrite samei, samen, <-v_shift_comm.
    rewrite <-c_shift_sub. all: try omega.
    apply ηPair. omega.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt.
    assert (S(S i)=2+i) as samei by omega.
    assert (S(S n)=2+n) as samen by omega.
    simpl. rewrite samei, samen, <-v_shift_comm. 
    rewrite <-c_shift_sub. all : try omega.
    apply ηPair. omega.
+ clear V CI HC R VE CE HE WF. simpl.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite c_sub_subs, c_sub_subs, c_sub_subs. simpl.
    assert (S(S i)=1+(S i)) as samei by omega.
    rewrite samei, <-v_shift_comm.
    rewrite <-c_shift_sub. all: try omega.
    apply ηSum.
  - apply leb_complete_conv in ni.
    rewrite c_sub_subs_alt, c_sub_subs_alt, c_sub_subs_alt. simpl.
    rewrite <-v_shift_comm, <-c_shift_sub. all: try omega.
    apply ηSum.
+ clear V CI HC R VE CE HE WF. simpl. apply ηDoBind.
}{
intros gets vtys.
inv orig. destruct H4.
+ specialize (HC _ _ _ _ H2) as IH1.
  specialize (HC _ _ _ _ H3) as IH2.
  clear V CI HC R VE CE HE WF. eapply Heq. 
  2: exact H0. all: eauto. apply HeqSigØ. 
+ specialize (HC _ _ _ _ H2) as IH1.
  specialize (HC _ _ _ _ H3) as IH2.
  specialize (CE _ _ _ _ H6) as IHc.
  specialize (HE _ _ _ _ _ H7) as IHh.
  clear V CI HC R VE CE HE WF. eapply Heq.
  2: exact H0. all: eauto. eapply HeqSigU.
  - eapply sub_find_Some in H4. eauto.
  - eapply sub_find_Some in H5. eauto.
  - eapply IHc. simpl. eauto. rewrite <-(v_shift_shift 1 1). 
    apply v_shift_typesafe. apply v_shift_typesafe; auto.
    all: inv H6; inv H8; inv H6. inv H14. assumption. assumption.
  - eauto.
}{
intros gets vtys. destruct orig.
+ clear V CI HC R VE CE HE WF. simpl. apply WfInstØ. auto.
+ specialize (V _ _ _ H) as IHv.
  specialize (WF _ _ _ orig) as IHwf.
  clear V CI HC R VE CE HE WF. simpl.
  apply WfInstU; eauto.
}
Admitted.


Fixpoint v_subs_typesafe 
  Γ Γ' v A i v_s A_s (orig: has_vtype Γ' v A) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_vtype Γ (v_subs v i v_s) A

with c_subs_typesafe
  Γ Γ' c C i v_s A_s (orig: has_ctype Γ' c C) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_ctype Γ (c_subs c i v_s) C

with h_subs_typesafe
  Γ Γ' h Σ D i v_s A_s (orig: has_htype Γ' h Σ D) {struct orig}:
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  has_htype Γ (h_subs h i v_s) Σ D

with respects_subs_typesafe
  Γ Γ' h Σ D E i v_s A_s (orig: respects Γ' h Σ D E) {struct orig} :
  has_htype Γ' h Σ D -> has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i ->
  ctx_len Γ >= i ->
  respects Γ (h_subs h i v_s) Σ D E

with veq_subs_typesafe
  Γ Γ' A v1 v2 i v_s A_s (orig: veq A Γ' v1 v2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  veq A Γ (v_subs v1 i v_s) (v_subs v2 i v_s)

with ceq_subs_typesafe
  Γ Γ' C c1 c2 i v_s A_s (orig: ceq C Γ' c1 c2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c1 i v_s) (c_subs c2 i v_s)

with heq_subs_typesafe
  Γ Γ' Σ D h1 h2 i v_s A_s (orig: heq Σ D Γ' h1 h2) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h1 i v_s) (h_subs h2 i v_s)

with wf_inst_subs_typesafe
  Γ Γ' I Γ0 i v_s A_s (orig: wf_inst Γ' I Γ0) {struct orig} :
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  wf_inst Γ (inst_subs I i v_s) Γ0.

Proof.
all: rename v_subs_typesafe into V; rename c_subs_typesafe into CI.
all: rename h_subs_typesafe into HC; rename respects_subs_typesafe into R.
all: rename veq_subs_typesafe into VE; rename ceq_subs_typesafe into CE.
all: rename heq_subs_typesafe into HE; rename wf_inst_subs_typesafe into WF.
{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear V CI HC R VE CE HE WF. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeUnit.
+ clear V CI HC R VE CE HE WF. 
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInt.
+ clear V CI HC R VE CE HE WF. 
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
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypePair; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInl; auto.  
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeInr; auto.
+ clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeListNil; auto.
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH1.
  specialize (V Γ Γ0 vs _ i _ _ H2 tyvs geq) as IH2.
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeListCons; auto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  inv H0. specialize (v_shift_typesafe _ Γ A _ tyvs H5) as tyvs'.
  specialize (CI _ _ c _ (1+i) _ _ H1 tyvs') as IH. 
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply WfTyFun; auto. apply TypeFun. 
  rewrite v_shift_comm. apply IH. simpl. f_equal. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; inv H7; assumption).
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (CI _ _ c_ret _ (1+i) _ _ H1 tyvs' H4) as IHc. 
  specialize (HC _ _ h _ _ i _ _ H2 tyvs geq) as IHh. 
  specialize (R _ _ h _ _ _ i _ _ H3 H2 tyvs) as IHr.
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. apply TypeHandler. 
  rewrite v_shift_comm. apply IHc. simpl. omega. omega. auto. auto.
+ specialize (V Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeV; auto; unfold v_subs; simpl. 
  eapply TypeVSubtype; eauto.
}{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1. 
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeRet. auto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. apply TypeAbsurd. auto.
+ assert (CtxU (CtxU Γ0 A) B = ctx_insert (CtxU (CtxU Γ A) B) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H5; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; auto).
  specialize (V _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CI _ _ c _ (2+i) _ _ H2 tyvs'' H3) as IHc.
  clear V CI HC R VE CE HE WF.
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
  specialize (CI _ _ c1 _ (1+i) _ _ H2 tyvsa geqa) as IHc1.
  specialize (CI _ _ c2 _ (1+i) _ _ H3 tyvsb geqb) as IHc2.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeΣMatch. eauto. 
  - rewrite v_shift_comm. apply IHc1. simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU (CtxU Γ0 A) (TyList A) 
    = ctx_insert (CtxU (CtxU Γ A) (TyList A)) A_s (2+i)).
  { simpl. f_equal. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H6; auto).
  assert (wf_vtype (TyList A)) as wfla by (inv H1; auto).
  specialize (V _ _ v _ i _ _ H1 tyvs geq) as IHv.
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyList A) _ tyvs' wfla) as tyvs''.
  specialize (CI _ _ c1 _ i _ _ H2 tyvs geq) as IHc1.
  specialize (CI _ _ c2 _ (2+i) _ _ H3 tyvs'' H4) as IHc2.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeListMatch; eauto. 
  rewrite v_shift_shift in IHc2. rewrite v_shift_comm. apply IHc2.
  simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) A_s (1+i)) as geqa.
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (CI _ _ c1 _ i _ _ H1 tyvs geq) as IHc1.
  specialize (CI _ _ c2 _ (1+i) _ _ H2 tyvsa geqa) as IHc2.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeDoBind. eauto. 
  rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ specialize (V _ _ v1 _ i _ _ H1 tyvs) as IH1.
  specialize (V _ _ v2 _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeApp. eauto. eauto.
+ specialize (V _ _ v _ i _ _ H1 tyvs) as IHv.
  specialize (CI _ _ c _ i _ _ H2 tyvs) as IHc.
  clear V CI HC R VE CE HE WF.
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
  clear V CI HC R VE CE HE WF.
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
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CI Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear V CI HC R VE CE HE WF.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubtype; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2. 
+ clear V CI HC R VE CE HE WF.
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
  clear V CI HC R VE CE HE WF.
  apply TypeH; auto; unfold h_subs; simpl. eapply TypeCasesU.
  - apply negshift_find_None. apply sub_find_None. assumption.
  - auto. 
  - rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
    simpl. omega. omega.
}{
intros tysh tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H3. 
+ clear V CI HC R VE CE HE WF.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsØ.
+ specialize (R _ _ _ _ _ _ i v_s _ H3 tysh tyvs geq) as IHr.
  specialize (CE 
    (join_ctxs (join_ctxs Γ (tctx_to_ctx Z D)) Γ0) 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ0) 
    D (handle_t (ctx_len Γ0) (tctx_len Z) h T1) 
    (handle_t (ctx_len Γ0) (tctx_len Z) h T2) 
    (i + tctx_len Z + ctx_len Γ0) 
    (v_shift v_s (tctx_len Z+ctx_len Γ0) 0) A_s H4) as IHc.
  all: clear V CI HC R VE CE HE WF.
  apply Respects; auto; unfold h_subs; simpl. apply RespectEqsU. auto.
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
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. apply VeqSym. apply IH; auto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (VE _ _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE WF. eapply VeqTrans; eauto.
+ clear V CI HC R VE CE HE WF. subst. unfold v_subs. simpl.
  rename i0 into j. destruct (j =? i) eqn:cmp. 
  - rewrite v_negshift_shift, v_shift_0. 
    apply veq_refl in tyvs. inv H0. apply Nat.eqb_eq in cmp. subst. 
    erewrite get_ctx_insert_new in H1. inv H1.
    eapply veq_subtype in tyvs; eauto. inv tyvs. all: omega || auto.
  - simpl. destruct (i<=?j) eqn:ilj; eapply VeqVar; omega || eauto.
    * apply Nat.eqb_neq in cmp. apply leb_complete in ilj.
      erewrite get_ctx_insert_changed.
      assert (1+(j-1)=j) by omega. rewrite H3. eauto. omega. 
    * apply Nat.eqb_neq in cmp. apply leb_complete_conv in ilj.
      erewrite get_ctx_insert_unchanged. eauto. omega.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqUnit.
+ clear V CI HC R VE CE HE WF. simpl. apply VeqInt.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (VE _ _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. apply VeqPair; auto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. eapply VeqInl; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. eapply VeqInr; eauto.
+ clear V CI HC R VE CE HE WF. unfold v_subs. simpl. apply VeqListNil; auto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (VE _ _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. apply VeqListCons; auto.
+ assert (wf_vtype A) as wfa by (inv H; inv H3; assumption).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (CE _ _ _ _ _ (S i) _ _ H1 tyvs') as IH.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. eapply VeqFun.
  rewrite v_shift_comm. apply IH. simpl. f_equal. assumption.
  all: simpl; omega.
+ assert (wf_vtype A) as wfa by (inv H; inv H5; inv H8; assumption).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (CE _ _ _ _ _ (S i) _ _ H1 tyvs') as IHc.
  specialize (HE _ _ _ _ _ _ i _ _ H2 tyvs) as IHh.
  clear V CI HC R VE CE HE WF. unfold v_subs. simpl. eapply VeqHandler; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. assumption.
  all: simpl; omega.
+ clear V CI HC R VE CE HE WF. unfold v_subs. simpl. apply ηUnit.
+ clear V CI HC R VE CE HE WF. unfold v_subs. simpl.
  rewrite <-v_shift_sub, <-v_shift_negshift_comm. apply ηFun.
  apply v_sub_makes_no_var. apply v_shift_makes_no_var. omega. omega. 
}{
intros tyvs geq len. apply Ceq.
{ inv orig; eauto. }
{ inv orig; eauto. }
destruct orig. destruct H1.
+ specialize (CE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. apply CeqSym. eauto.
+ specialize (CE _ _ _ _ _ i _ _ H1 tyvs) as IH1.
  specialize (CE _ _ _ _ _ i _ _ H2 tyvs) as IH2.
  clear V CI HC R VE CE HE WF. eapply CeqTrans; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqRet. auto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IH.
  clear V CI HC R VE CE HE WF. simpl. apply CeqAbsurd. auto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H4; inv H6; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ B _ tyvs' wfb) as tyvs''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H2 tyvs'') as IHc.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqΠMatch. auto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IHc.
  simpl. do 2 f_equal. assumption.
  simpl. omega. omega.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H5; inv H7; auto).
  assert (wf_vtype B) as wfb by (inv H1; inv H5; inv H7; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvsa.
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CE _ _ _ _ _ (S i) _ _ H2 tyvsa) as IHc1.
  specialize (CE _ _ _ _ _ (S i) _ _ H3 tyvsb) as IHc2.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqΣMatch. auto.
  all: rewrite v_shift_comm; omega || apply IHc1 || apply IHc2.
  all: simpl; try omega; f_equal; assumption.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IHv.
  assert (wf_vtype A) as wfa by (inv H1; inv H4; inv H7; auto).
  assert (wf_vtype (TyList A)) as wfla by (inv H1; inv H4; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyList A) _ tyvs' wfla) as tyvs''.
  specialize (CE _ _ _ _ _ i _ _ H2 tyvs) as IHc1.
  specialize (CE _ _ _ _ _ (2+i) _ _ H3 tyvs'') as IHc2.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqListMatch; eauto.
  rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IHc2.
  simpl. do 2 f_equal. assumption. simpl. omega. omega.
+ assert (wf_vtype B) as wfb by (inv H1; inv H4; inv H6; auto).
  specialize (v_shift_typesafe _ _ B _ tyvs wfb) as tyvsb.
  specialize (CE _ _ _ _ _ i _ _ H1 tyvs) as IHc1.
  specialize (CE _ _ _ _ _ (S i) _ _ H2 tyvsb) as IHc2.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqDoBind. eauto.
  rewrite v_shift_comm. apply IHc2. simpl.  f_equal. assumption.
  simpl. omega. omega.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IHv1.
  specialize (VE _ _ _ _ _ i _ _ H2 tyvs) as IHv2.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqApp; eauto.
+ specialize (VE _ _ _ _ _ i _ _ H1 tyvs) as IHv.
  specialize (CE _ _ _ _ _ i _ _ H2 tyvs) as IHc.
  clear V CI HC R VE CE HE WF. simpl. eapply CeqHandle; eauto.
+ assert (wf_vtype A) as wfa by (inv H2; inv H3; inv H2; inv H10; auto).
  assert (wf_vtype (TyFun A C)) as wff by (inv H2; inv H3; inv H2; auto).
  specialize (v_shift_typesafe _ _ A _ tyvs wfa) as tyvs'.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs' wff) as tyvs''.
  specialize (v_shift_typesafe _ _ (TyFun A C) _ tyvs wff) as tyvs'''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H1 tyvs'') as IHc1.
  specialize (CE _ _ _ _ _ (1+i) _ _ H2 tyvs''') as IHc2.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqLetRec.
  all: rewrite v_shift_comm; omega || auto.
  - rewrite <-(v_shift_shift 1 1). eapply IHc1. simpl. do 2 f_equal. auto.
    simpl. omega.
  - apply IHc2. simpl. f_equal. auto. simpl. omega.
+ assert (wf_vtype B_op) as wfb by (inv H3; inv H4; inv H3; auto).
  specialize (v_shift_typesafe _ _ B_op _ tyvs wfb) as tyvsb.
  specialize (VE _ _ _ _ _ i _ _ H2 tyvs) as IHv.
  specialize (CE _ _ _ _ _ (S i) _ _ H3 tyvsb) as IHc.
  clear V CI HC R VE CE HE WF. unfold c_subs. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. f_equal. auto. simpl. omega. omega.
+ specialize (WF _ _ _ _ i _ _ H2 tyvs) as IHwf.
  clear V CI HC R VE CE HE WF. eapply OOTB; eauto.
  rewrite <-c_subs_inst. rewrite H3. simpl. auto.
  rewrite <-c_subs_inst. rewrite H4. simpl. auto.
+ clear V CI HC R VE CE HE WF. specialize βΠMatch as rule.
  unfold c_subs2_out in *. unfold c_subs_out in *. simpl.
  rewrite c_subs_subs, (c_subs_subs _ 0). simpl.
  assert (c_subs (ΠMatch (Pair v1 v2) c) i v_s 
    = ΠMatch (Pair (v_subs v1 i v_s) (v_subs v2 i v_s)) 
        (c_subs c (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm. reflexivity. omega. }  
  rewrite H1. rewrite v_shift_shift, <-v_shift_subs_alt.
  apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inl as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inl v) c1 c2) i v_s
    = ΣMatch (Inl (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βΣMatch_Inr as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (ΣMatch (Inr v) c1 c2) i v_s
    = ΣMatch (Inr (v_subs v i v_s)) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Nil as rule.
  unfold c_subs_out in *. simpl.
  assert (c_subs (ListMatch ListNil c1 c2) i v_s 
    = ListMatch ListNil 
        (c_subs c1 i v_s)
        (c_subs c2 (2+i) (v_shift v_s 2 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal; f_equal; 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βListMatch_Cons as rule.
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
+ clear V CI HC R VE CE HE WF. specialize βApp as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (App (Fun c) v) i v_s 
    = App (Fun (c_subs c (1+i) (v_shift v_s 1 0))) (v_subs v i v_s)).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βLetRec as rule.
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
    do 2 f_equal. rewrite v_shift_comm. auto. omega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var. all: try omega.
    do 3 f_equal. rewrite v_shift_shift, v_shift_comm; auto || omega. }
  rewrite H1. clear H1. apply rule. omega.  
+ clear V CI HC R VE CE HE WF. specialize βDoBind_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (DoBind (Ret v) c) i v_s 
    = DoBind (Ret (v_subs v i v_s)) (c_subs c (1+i) (v_shift v_s 1 0))).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βDoBind_Op as rule.
  unfold c_subs_out in *. unfold c_subs. simpl. rewrite v_shift_comm. 
  specialize (rule op 
    (v_negshift (v_sub v (i, v_shift v_s 1 i)) 1 i)
    (c_negshift
      (c_sub c1 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i)))
      1 (S i))
    (c_negshift
      (c_sub c2 (S i, v_shift (v_shift v_s 1 0) 1 (1 + i))) 1
      (S i))).
  rewrite c_shift_negshift_comm, c_shift_sub in rule. simpl.
  assert (v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 0
    = v_shift (v_shift (v_shift v_s 1 0) 1 (S i)) 1 1).
  { rewrite <-v_shift_comm, v_shift_comm. all: omega || auto. }
  rewrite H1. apply rule. all: try omega. clear rule.
  apply c_sub_makes_no_var. apply v_shift_makes_no_var.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Ret as rule.
  unfold c_subs_out in *. simpl. rewrite c_subs_subs. simpl.
  assert (c_subs (Handle (Handler c_r h) (Ret v)) i v_s
    = Handle (Handler 
      (c_subs c_r (1+i) (v_shift v_s 1 0)) (h_subs h i v_s)) 
      (Ret (v_subs v i v_s) ) ).
  { unfold c_subs. unfold v_subs. simpl. f_equal. f_equal. 
    rewrite v_shift_comm; reflexivity || omega. }  
  rewrite H1. apply rule. all: omega.
+ clear V CI HC R VE CE HE WF. specialize βHandle_Op as rule.
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
    rewrite v_shift_comm. f_equal. apply v_shift_comm. all: try omega.
    apply c_sub_makes_no_var. apply v_shift_makes_no_var.
    rewrite h_shift_negshift_comm, h_shift_sub. f_equal. omega.
    apply h_sub_makes_no_var. apply v_shift_makes_no_var. omega.
    rewrite v_shift_comm. reflexivity. omega. }
  rewrite H2, v_shift_shift, <-v_shift_subs_alt. clear H2. simpl.
  eapply rule. unfold h_subs. 
  apply negshift_find_Some. rewrite <-(v_shift_comm 1 i 0). 
  apply sub_find_Some. eauto. all: omega.
+ clear V CI HC R VE CE HE WF. simpl.
  assert (forall c, c_subs (ΠMatch v c) i v_s 
    = ΠMatch (v_subs v i v_s) (c_subs c (2+i) (v_shift v_s 2 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm. reflexivity. omega. }
  rewrite H1. clear H1.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
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
    rewrite H1. clear H1. apply ηPair. all: omega.
  - apply leb_complete_conv in ni.
    destruct n. omega.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ ). all: try omega. simpl.
    specialize ηPair as rule.
    assert (v_subs (Pair (Var 1) (Var 0)) (S (S i)) (v_shift v_s 2 0)
      = (Pair (Var 1) (Var 0))).
    { unfold v_subs. simpl. reflexivity. }
    rewrite H1. clear H1. 
    assert (S(S n)=2+n) as samen by omega.
    rewrite samen, <-v_shift_comm.
    rewrite <-(v_shift_shift 1 1), <-(c_shift_shift 1 1).
    rewrite <-c_shift_subs_alt, <-c_shift_subs_alt, c_shift_shift.
    apply ηPair. all: omega.
+ clear V CI HC R VE CE HE WF. simpl.
  assert (forall c1 c2, c_subs (ΣMatch v c1 c2) i v_s 
    = ΣMatch (v_subs v i v_s) 
        (c_subs c1 (1+i) (v_shift v_s 1 0))
        (c_subs c2 (1+i) (v_shift v_s 1 0))).
  { intro c'. unfold c_subs. simpl. rewrite v_shift_comm. reflexivity. omega. }
  rewrite H1. clear H1.
  destruct (n<=?i) eqn:ni.
  - apply leb_complete in ni.
    rewrite (c_subs_subs _ n), (c_subs_subs _ (1+n)), (c_subs_subs _ (1+n)).
    simpl. all: try omega.
    assert (S(S i)=1+(S i)) as samei by omega.
    rewrite samei. rewrite <-v_shift_comm.
    rewrite <-c_shift_subs_alt. all: try omega.
    apply ηSum.
  - apply leb_complete_conv in ni.
    rewrite (c_subs_subs_alt _ n), (c_subs_subs_alt _ n).
    destruct n. all: try omega.
    rewrite (c_subs_subs_alt _ n). simpl.
    rewrite <-v_shift_comm, <-c_shift_subs_alt. all: try omega.
    apply ηSum.
+ clear V CI HC R VE CE HE WF. simpl. apply ηDoBind.
}{
intros tyvs geq len.
destruct orig. destruct H4.
+ specialize (HC _ _ h1 _ _ i _ _ H2 tyvs geq) as IHh1.
  specialize (HC _ _ h2 _ _ i _ _ H3 tyvs geq) as IHh2.
  clear V CI HC R VE CE HE WF. eapply Heq. 
  2: exact H0. all: eauto. eapply HeqSigØ.
+ assert (wf_vtype A) as wfa by (inv H6; inv H8; inv H6; auto).
  assert (wf_vtype(TyFun B D)) as wff by (inv H6;inv H8;inv H6;inv H14;auto).
  specialize (HC _ _ h1 _ _ i _ _ H2 tyvs geq) as IHh1.
  specialize (HC _ _ h2 _ _ i _ _ H3 tyvs geq) as IHh2.
  specialize (v_shift_typesafe _ _ (TyFun B D) _ tyvs wff) as tyvs'.
  specialize (v_shift_typesafe _ _ A _ tyvs' wfa) as tyvs''.
  specialize (CE _ _ _ _ _ (2+i) _ _ H6 tyvs'') as IH1.
  specialize (HE _ _ _ _ _ _ i _ _ H7 tyvs) as IH2.
  clear V CI HC R VE CE HE WF. eapply Heq.
  2: exact H0. all: eauto. eapply HeqSigU.
  - unfold h_subs. eapply negshift_find_Some. eapply sub_find_Some. eauto.
  - unfold h_subs. eapply negshift_find_Some. eapply sub_find_Some. eauto.
  - rewrite v_shift_comm, <-(v_shift_shift 1 1). apply IH1.
    simpl. do 2 f_equal. assumption. simpl. omega. omega.
  - eauto.
}{
intros tyvs geq len. destruct orig.
+ clear V CI HC R VE CE HE WF. simpl. apply WfInstØ. inv tyvs. auto.
+ specialize (V _ _ _ _ i _ _ H tyvs geq) as IHv.
  specialize (WF _ _ _ _ i _ _ orig tyvs geq) as IHwf.
  clear V CI HC R VE CE HE WF. simpl.
  apply WfInstU; eauto.
}
Admitted.

(* ==================== Handling templates ==================== *)

Fixpoint cop_insert_ctx Γ' Γ A B D c {struct Γ}:
  wf_ctx Γ -> has_ctype (CtxU (CtxU Γ' (TyFun B D)) A) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs Γ' Γ) (TyFun B D)) A) 
    (c_shift c (ctx_len Γ) 2) D.
Proof.
intros wfg tys.
destruct Γ; simpl.
+ rewrite c_shift_0. auto.
+ assert (CtxU (CtxU (CtxU (join_ctxs Γ' Γ) v) (TyFun B D)) A
    = ctx_insert (CtxU (CtxU (join_ctxs Γ' Γ) (TyFun B D)) A) v 2).
  { simpl. do 2 f_equal. destruct Γ; simpl. destruct Γ'; simpl. all: auto. }
  assert (S (ctx_len Γ) = ctx_len Γ + 1) by omega.
  rewrite H, H0. rewrite <-(c_shift_shift). apply c_insert_typesafe.
  all: inv wfg; auto.
Admitted.


Fixpoint handle_t_cop_types Γ' Γ Z A B D c:
  wf_ctx Γ -> wf_tctx Z ->
  has_ctype (CtxU (CtxU Γ' (TyFun B D)) A) c D ->
  has_ctype 
    (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) (TyFun B D)) A) 
    (c_shift c (tctx_len Z + ctx_len Γ) 2) D.
Proof.
intros wfg wfz tys.
rewrite <-join_ctxs_assoc. 
erewrite len_tctx_to_ctx, <-len_join_ctxs.
apply cop_insert_ctx. apply wf_join_ctxs. apply wf_tctx_to_ctx. all: auto.
inv tys. auto.
Admitted.


Fixpoint handle_t_types Γ Z T Σ Γ' h D {struct T}:
  wf_ctx Γ -> wf_tctx Z -> wf_t Γ Z T Σ -> has_htype Γ' h  Σ D ->
  has_ctype 
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (handle_t (ctx_len Γ) (tctx_len Z) h T) D.
Proof.
intros wfc wfz wft tys.
assert (wf_ctype D) by (inv tys; inv H0; assumption).
assert (wf_ctx (join_ctxs Γ' (tctx_to_ctx Z D))) as wfct.
{ apply wf_join_ctxs. inv tys. auto. apply wf_tctx_to_ctx; auto. }
assert (wf_ctx (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)) as wfctt.
{ apply wf_join_ctxs; auto. }
destruct T; simpl.
+ apply TypeC; auto. inv wft. eapply TypeApp.
  - apply TypeV; auto. instantiate (1:=A).
    apply WfTyFun. inv H4. auto. auto. apply TypeVar.
    erewrite <-get_join_ctxs_left. apply get_join_ctxs_right.
    apply get_tctx_to_ctx. auto.
  - apply v_join_ctxs_typesafe_right; auto.
+ apply TypeC; auto. inv wft. eapply TypeAbsurd. 
  apply v_join_ctxs_typesafe_right; auto.
+ apply TypeC; auto. inv wft. eapply TypeΠMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A) B
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU (CtxU Γ A) B)). 
    { simpl.  reflexivity. }
    assert (S (S (ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) B)).
    { simpl. reflexivity. }
    rewrite H0. rewrite H1. eapply handle_t_types; eauto.
    apply WfCtxU. apply WfCtxU. auto. all: inv H4; inv H3; auto.
+ apply TypeC; auto. inv wft. eapply TypeΣMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) A
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ A)). 
    { simpl.  reflexivity. }
    assert (S (ctx_len Γ)=ctx_len (CtxU Γ A)).
    { simpl. reflexivity. }
    rewrite H0. rewrite H1. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv H5. inv H3. auto.
  - assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) B
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ B)). 
    { simpl.  reflexivity. }
    assert (S (ctx_len Γ)=ctx_len (CtxU Γ B)).
    { simpl. reflexivity. }
    rewrite H0. rewrite H1. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv H5. inv H3. auto.
+ apply TypeC; auto. inv wft. eapply TypeListMatch.
  - apply v_join_ctxs_typesafe_right; eauto.
  - eauto.
  - assert (CtxU(CtxU(join_ctxs(join_ctxs Γ' (tctx_to_ctx Z D))Γ)A)(TyList A)
      = join_ctxs(join_ctxs Γ'(tctx_to_ctx Z D))(CtxU(CtxU Γ A)(TyList A))). 
    { simpl.  reflexivity. }
    assert (S (S (ctx_len Γ))=ctx_len (CtxU (CtxU Γ A) (TyList A))).
    { simpl. reflexivity. }
    rewrite H0. rewrite H1. eapply handle_t_types; eauto.
    apply WfCtxU. apply WfCtxU. auto. all: inv H5; auto; inv H3; auto.
+ inv wft.
  specialize (h_has_case Γ' h Σ D o A_op B_op tys H5) as has.
  destruct has as [c_op finds].
  eapply case_has_type in finds as coptys; eauto. rewrite finds.
  unfold c_subs2_out.
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)) (TyFun B_op D)).
  eapply c_subs_typesafe. instantiate (1:= 
  (CtxU (CtxU(join_ctxs (join_ctxs Γ'(tctx_to_ctx Z D)) Γ) (TyFun B_op D))A_op)).
  - assert (ctx_len Γ + tctx_len Z = tctx_len Z + ctx_len Γ) as same by omega.
    rewrite same. apply handle_t_cop_types; eauto.
  - apply v_shift_typesafe. apply v_join_ctxs_typesafe_right; eauto.
    inv coptys. inv H0. inv H6. auto. 
  - simpl. auto.
  - omega.
  - apply TypeV; eauto. inv coptys. inv H0. inv H6. eauto.
    apply TypeFun.
    assert (S (ctx_len Γ) = ctx_len (CtxU Γ B_op)) as samelen by (simpl; auto).
    assert (CtxU (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ) B_op
      = join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) (CtxU Γ B_op)).
    { simpl. reflexivity. }
    rewrite samelen, H0. eapply handle_t_types; eauto.
    apply WfCtxU. auto. inv coptys. inv H1. inv H9. inv H11. auto. 
  - assert (forall γ A, CtxU γ A = ctx_insert γ A 0).
    { intros. induction γ; simpl; auto. }
    rewrite H0. auto.
  - omega.
Admitted.

(* ==================== Instantiation ==================== *)

Lemma wf_inst_len_same Γ' I Γ:
  wf_inst Γ' I Γ -> inst_len I = ctx_len Γ.
Proof.
intros orig. induction orig; simpl; auto.
Qed.


Lemma inst_len_insert I i v:
  i <= inst_len I -> 
  inst_len (inst_insert I i v) = 1+inst_len I.
Proof.
revert i v. induction I; intros; simpl.
+ destruct i. simpl. auto. simpl in H. omega.
+ destruct i. auto.
  assert (S i=?0=false) by (apply Nat.eqb_neq; omega). 
  rewrite H0. simpl. rewrite IHI. omega. simpl in H. omega.
Qed.

Lemma find_inst_None I h op:
  find_case h op = None -> find_case (h_inst h I) op = None.
Proof.
revert I op. induction h; intros I op orig.
+ simpl. auto.
+ simpl in *. destruct (op==o). discriminate. auto.
Qed.

Fixpoint find_inst_Some I I' h op c_op:
  find_case h op = Some c_op -> 
  I' = InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0) ->
  find_case (h_inst h I) op = Some (c_inst c_op I').
Proof.
intros finds same. destruct h; subst; simpl in *.
+ discriminate.
+ destruct (op==o). inv finds. auto. apply find_inst_Some; auto.
Qed.


Lemma wf_inst_get_Some Γ I Γ' n A:
  wf_inst Γ I Γ' -> get_vtype Γ' n = Some A ->
  exists v, get_inst_val I n = Some v /\ has_vtype Γ v A.
Proof.
intros wf. revert n A. induction wf; intros n A' gets.
+ simpl in gets. discriminate.
+ simpl in gets. destruct n.
  - inv gets. exists v. eauto.
  - apply IHwf. auto.
Admitted.


Lemma wf_inst_extend A Γ I Γ':
  wf_vtype A -> wf_inst Γ I Γ' ->
  wf_inst (CtxU Γ A) (InstU (inst_shift I 1 0) (Var 0)) (CtxU Γ' A).
Proof.
intros wfa wfi. apply WfInstU.
+ apply TypeV; auto.
  - apply WfCtxU. inv wfi. 2: inv H. all: auto.
  - apply TypeVar. auto.
+ apply wf_inst_shift_typesafe; auto.
Qed.


Lemma instU_is_insert I v:
  InstU I v = inst_insert I 0 v.
Proof.
destruct I; simpl; auto.
Qed.

Lemma instU_insert_extend I n vs v:
  InstU (inst_insert I n vs) v = inst_insert (InstU I v) (S n) vs.
Proof.
simpl. do 2 f_equal. omega.
Qed.


Fixpoint v_inst_subs k v vs n I {struct v}:
  n <= inst_len I -> 
  v_under_var v (1+inst_len I) -> v_under_var vs (inst_len I) ->
  v_inst (v_subs v n vs) I =
  v_subs (v_inst v (inst_insert (inst_shift I 1 k) n (Var k)))
    k (v_inst vs I)
with c_inst_subs k c vs n I {struct c}:
  n <= inst_len I -> 
  c_under_var c (1+inst_len I) -> v_under_var vs (inst_len I) ->
  c_inst (c_subs c n vs) I =
  c_subs (c_inst c (inst_insert (inst_shift I 1 k) n (Var k)))
    k (v_inst vs I)
with h_inst_subs k h vs n I {struct h}:
  n <= inst_len I -> 
  h_under_var h (1+inst_len I) -> v_under_var vs (inst_len I) ->
  h_inst (h_subs h n vs) I =
  h_subs (h_inst h (inst_insert (inst_shift I 1 k) n (Var k)))
    k (v_inst vs I).
Proof.
{
intros safe undv undvs. 
destruct v; unfold v_subs in *; unfold c_subs in *; simpl; auto.
{ rename v into dbi.
  destruct (dbi=?n) eqn:dbin; simpl.
  2: destruct (n<=?dbi) eqn:cmp.
  - apply Nat.eqb_eq in dbin. subst. 
    rewrite inst_insert_same. simpl.
    assert (k=?k=true) as same by (apply Nat.eqb_eq; auto). rewrite same.
    rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    all: omega || auto. rewrite inst_len_shift. omega.
  - apply Nat.eqb_neq in dbin. apply leb_complete in cmp.
    destruct dbi. omega.
    rewrite inst_insert_above. simpl.
    assert (dbi-0=dbi) as same by omega. rewrite same, get_inst_val_shift. 
    destruct (get_inst_val I dbi) eqn:gets; simpl.
    rewrite v_sub_no_var, v_negshift_shift, v_shift_0.
    all: omega || auto.
    apply v_shift_makes_no_var. rewrite inst_len_shift. auto.
  - apply Nat.eqb_neq in dbin. apply leb_complete_conv in cmp.
    rewrite inst_insert_under. simpl.
    rewrite get_inst_val_shift.
    destruct (get_inst_val I dbi) eqn:gets; simpl.
    rewrite v_sub_no_var, v_negshift_shift, v_shift_0.
    all: omega || auto.
    apply v_shift_makes_no_var. rewrite inst_len_shift. auto. }
all: f_equal; simpl in *; try destruct undv; eauto.
all: rewrite inst_shift_insert, inst_shift_comm, v_shift_comm; try omega; simpl.
all: erewrite (c_inst_subs (S k)); simpl.
all: try rewrite inst_len_shift; omega || auto.
+ do 3 f_equal. do 2 f_equal. omega. rewrite v_shift_inst, v_shift_comm.
  simpl. rewrite instU_is_insert, v_inst_no_var_same.
  rewrite v_negshift_shift, v_shift_0, v_shift_inst, v_shift_inst. 
  all: omega || auto. apply v_shift_makes_no_var.
  apply v_under_var_shift; try omega.
  rewrite inst_len_shift, inst_len_shift. auto.
+ apply v_under_var_shift; try omega. auto.
+ do 3 f_equal. do 2 f_equal. omega. rewrite v_shift_inst, v_shift_comm.
  simpl. rewrite instU_is_insert, v_inst_no_var_same.
  rewrite v_negshift_shift, v_shift_0, v_shift_inst, v_shift_inst. 
  all: omega || auto. apply v_shift_makes_no_var.
  apply v_under_var_shift; try omega.
  rewrite inst_len_shift, inst_len_shift. auto.
+ apply v_under_var_shift; try omega. auto.
}{
intros safe undv undvs. 
destruct c; unfold v_subs in *; unfold c_subs in *; simpl; auto; f_equal.

all: rewrite v_shift_comm || rewrite c_shift_comm || auto; try omega.
all: try erewrite (v_inst_subs k); auto.
all: clear v_inst_subs h_inst_subs.
all: simpl in *; try destruct undv; try destruct H0; omega || eauto.

all: assert (forall n, S(S n)=2+n) as ssn by (intros; omega).
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; omega || auto.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; omega || auto.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; omega || auto.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: omega || auto.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; omega || auto.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; omega || auto.
  - apply v_under_var_shift; omega || auto.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: omega || auto.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; omega || auto.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; omega || auto.
  - apply v_under_var_shift; omega || auto.
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; omega || auto.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; omega || auto.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; omega || auto.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: omega || auto.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; omega || auto.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; omega || auto.
  - apply v_under_var_shift; omega || auto.
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; omega || auto.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; omega || auto.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; omega || auto.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: omega || auto.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; omega || auto.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; omega || auto.
  - apply v_under_var_shift; omega || auto.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); omega || auto.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: omega || auto.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; omega || auto.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; omega || auto.
  - apply v_under_var_shift; omega || auto.
}{
intros safe undv undvs. 
destruct h; unfold h_subs in *; unfold c_subs in *; simpl; auto; f_equal.
all: simpl in *; destruct undv; try rewrite v_shift_comm; simpl.
all: erewrite (c_inst_subs (S(S k))) || erewrite (h_inst_subs k) || auto.
all: simpl; try rewrite inst_len_shift; omega || eauto.
all: clear c_inst_subs h_inst_subs.
+ do 3 f_equal.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite instU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; omega || auto.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; omega || auto.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; omega || auto.
+ assert (S(S(inst_len I)) = 2+(inst_len I)) as same by omega.
  rewrite same. apply v_under_var_shift. auto. omega.
}
Qed.


Lemma c_inst_subs_out c vs I :
  c_under_var c (1+inst_len I) -> v_under_var vs (inst_len I) ->
  c_inst (c_subs_out c vs) I =
  c_subs 
    (c_inst c (InstU (inst_shift I 1 0) (Var 0)))
    0 (v_inst vs I).
Proof.
intros. unfold c_subs_out. unfold c_subs_out.
rewrite (c_inst_subs 0). do 2 f_equal.
rewrite instU_is_insert.
all: simpl; omega || auto.
Qed.


Lemma c_inst_subs2_out c vs1 vs2 I :
  c_under_var c (2+inst_len I) ->
  v_under_var vs1 (inst_len I) -> v_under_var vs2 (inst_len I) ->
  c_inst (c_subs2_out c vs1 vs2) I =
  c_subs (c_subs 
    (c_inst c (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    0 (v_inst vs2 (inst_shift I 1 0))) 0 (v_inst vs1 I).
Proof.
intros. unfold c_subs2_out.
rewrite c_inst_subs_out, c_inst_subs_out. simpl.
rewrite inst_shift_shift. f_equal. f_equal.
rewrite instU_is_insert, v_inst_no_var_same, v_negshift_shift, v_shift_0.
all: simpl; omega || auto.
+ apply v_shift_makes_no_var.
+ apply v_under_var_shift. rewrite inst_len_shift. auto. omega.
+ rewrite inst_len_shift. auto.
+ apply v_under_var_shift. rewrite inst_len_shift. auto. omega.
+ unfold c_subs_out. apply c_under_var_subs. auto.
  - apply v_under_var_shift. auto. omega.
  - omega.
Qed.


Fixpoint v_wf_inst_typesafe Γ I Γ' v A (orig:has_vtype Γ' v A) :
  wf_inst Γ I Γ' ->
  has_vtype Γ (v_inst v I) A
with c_wf_inst_typesafe Γ I Γ' c C (orig:has_ctype Γ' c C) :
  wf_inst Γ I Γ' ->
  has_ctype Γ (c_inst c I) C
with h_wf_inst_typesafe Γ I Γ' h Σ D (orig:has_htype Γ' h Σ D) :
  wf_inst Γ I Γ' ->
  has_htype Γ (h_inst h I) Σ D
with respect_wf_inst_typesafe Γ I Γ' h Σ D E (orig:respects Γ' h Σ D E):
  wf_inst Γ I Γ' -> has_htype Γ (h_inst h I) Σ D ->
  respects Γ (h_inst h I) Σ D E
with veq_wf_inst_typesafe Γ I Γ' v1 v2 A (orig: veq A Γ' v1 v2):
  wf_inst Γ I Γ' ->
    veq A Γ (v_inst v1 I) (v_inst v2 I)
with ceq_wf_inst_typesafe Γ I Γ' c1 c2 C (orig: ceq C Γ' c1 c2):
  wf_inst Γ I Γ' ->
    ceq C Γ (c_inst c1 I) (c_inst c2 I)
with heq_wf_inst_typesafe Γ I Γ' h1 h2 Σ D (orig: heq Σ D Γ' h1 h2):
  wf_inst Γ I Γ' ->
    heq Σ D Γ (h_inst h1 I) (h_inst h2 I).
Proof.
all: rename v_wf_inst_typesafe into VL.
all: rename c_wf_inst_typesafe into CL.
all: rename h_wf_inst_typesafe into HL.
all: rename respect_wf_inst_typesafe into RL.
all: rename veq_wf_inst_typesafe into VEL.
all: rename ceq_wf_inst_typesafe into CEL.
all: rename heq_wf_inst_typesafe into HEL.
all: intro wfinst; assert (wf_ctx Γ) by (inv wfinst; auto; inv H; auto).
{
destruct orig. destruct H2; simpl.
+ clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeUnit.
+ clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeInt.
+ clear VL CL HL RL VEL CEL HEL.
  eapply wf_inst_get_Some in H2 as gets; eauto. 
  destruct gets as [v''[gets tys]]. rewrite gets. auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypePair; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeInl; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeInr; auto.
+ clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeListNil; auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeListCons; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply CL in H2; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeFun; eauto.
  inv H1. auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply HL in H3; eauto.
  eapply RL in H4; eauto.
  eapply CL in H2; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. apply TypeHandler; auto.
  inv H1. inv H7. auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeV; auto. eapply TypeVSubtype; eauto.
}{
destruct orig. destruct H2; simpl.
+ eapply VL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. apply TypeRet; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. apply TypeAbsurd; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  simpl in H3. rewrite inst_shift_shift in H3.
  apply TypeC; auto. eapply TypeΠMatch; eauto.
  all: inv H2; inv H5; auto.
+ eapply wf_inst_extend in wfinst as wfinsc1.
  eapply wf_inst_extend in wfinst as wfinsc2.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeΣMatch; eauto.
  all: inv H2; inv H6; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  simpl in H4. rewrite inst_shift_shift in H4.
  apply TypeC; auto. eapply TypeListMatch; eauto.
  all: inv H2; auto; inv H6; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply CL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeDoBind; eauto.
  inv H2. inv H5. auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeApp; eauto.
+ eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeHandle; eauto.
+ eapply wf_inst_extend in wfinst as wfinsc1.
  eapply wf_inst_extend in wfinsc1 as wfinsc1.
  eapply wf_inst_extend in wfinst as wfinsc2.
  eapply CL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  simpl in H2. rewrite inst_shift_shift in H2.
  apply TypeC; auto. eapply TypeLetRec; eauto.
  all: inv H2; inv H4; auto; inv H9; auto.
+ eapply wf_inst_extend in wfinst as wfinsc1.
  eapply VL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeOp; eauto.
  all: inv H4; inv H5; auto.
+ eapply CL in H2; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply TypeC; auto. eapply TypeCSubtype; eauto.
}{
destruct orig. destruct H3; simpl.
+ clear VL CL HL RL VEL CEL HEL.
  apply TypeH; auto. apply TypeCasesØ; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply HL in H4; eauto.
  eapply CL in H5; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  simpl in H5. rewrite inst_shift_shift in H5.
  apply TypeH; auto. eapply TypeCasesU; eauto.
  apply find_inst_None. auto.
  all: inv H5; inv H6; auto. inv H10. auto.
}{
intros tys. destruct orig. destruct H4; simpl.
+ clear VL CL HL RL VEL CEL HEL. apply Respects; auto. apply RespectEqsØ.
+ eapply RL in H4; eauto.
  eapply CEL in H5 as ce; eauto.
  apply Respects; auto. apply RespectEqsU; eauto.
  admit. admit.
}{
destruct orig. destruct H2; simpl.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqSym. auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply VEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. eapply VeqTrans; eauto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  clear VL CL HL RL VEL CEL HEL.
  eapply wf_inst_get_Some in H2; eauto.
  destruct H2 as [v'[gets tys]].
  rewrite gets. apply veq_refl. 
  apply TypeV; auto. inv H0. auto. eapply TypeVSubtype; eauto.
+ eapply VL in H0; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqUnit.
+ eapply VL in H0; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqInt; auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply VEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqPair; auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqInl; auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqInr; auto.
+ eapply VL in H0; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqListNil; auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply VEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqListCons; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply CEL in H2; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply VeqFun; auto.
  inv H0. inv H4. auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  eapply CEL in H2; eauto.
  eapply HEL in H3; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. eapply VeqHandler; eauto.
  inv H0. inv H6. inv H9. auto.
+ eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. apply ηUnit.
+ eapply VL in H0 as IH1; eauto.
  eapply VL in H1 as IH2; eauto.
  all: clear VL CL HL RL VEL CEL HEL.
  apply Veq; auto. rewrite instU_is_insert.
  rewrite v_inst_no_var_same, v_negshift_shift, v_shift_0. 
  rewrite <-v_shift_inst. apply ηFun.
  all: omega || auto.
  apply v_shift_makes_no_var.
  apply v_under_var_shift. erewrite inst_len_shift, wf_inst_len_same.
  eapply has_vtype_is_under_ctx. all: omega || eauto.
}{
destruct orig. destruct H2; simpl.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply CEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. apply CeqSym. auto.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply CEL in H2; eauto.
  eapply CEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqTrans; eauto.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. apply CeqRet; auto.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. apply CeqAbsurd; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply CEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqΠMatch; eauto.
  simpl in H3. rewrite inst_shift_shift in H3. auto.
  all: inv H2; inv H4; inv H7; auto.
+ eapply wf_inst_extend in wfinst as wfinsc1.
  eapply wf_inst_extend in wfinst as wfinsc2.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply CEL in H3; eauto.
  eapply CEL in H4; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqΣMatch; eauto.
  all: inv H2; inv H5; inv H8; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply CEL in H3; eauto.
  eapply CEL in H4; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqListMatch; eauto.
  simpl in H4. rewrite inst_shift_shift in H4. auto.
  all: inv H2; inv H5; auto; inv H8; auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply CEL in H2; eauto.
  eapply CEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqDoBind; eauto.
  inv H3. inv H4. inv H3. auto.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply VEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqApp; eauto.
+ eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H2; eauto.
  eapply CEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqHandle; eauto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply wf_inst_extend in wfinsc as wfinsc.
  eapply wf_inst_extend in wfinst as wfinscf.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply CEL in H2; eauto.
  eapply CEL in H3; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqLetRec; eauto.
  simpl in H2. rewrite inst_shift_shift in H2. auto.
  all: inv H2; inv H4; inv H2; auto. inv H10. auto.
+ eapply wf_inst_extend in wfinst as wfinsc.
  eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  eapply VEL in H3; eauto.
  eapply CEL in H4; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply Ceq; auto. eapply CeqOp; eauto.
  inv H4. inv H5. inv H4. auto.
+ (* OOTB *) admit.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_prodmatch in H0 as parts. 
  destruct parts as [A[B[tyv tyc]]].
  apply Ceq; auto. 
  specialize (βΠMatch (v_inst v1 I) (v_inst v2 I)
    (c_inst c (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    ) as rule.
  unfold c_subs2_out in rule. unfold c_subs_out in rule. 
  rewrite c_inst_subs2_out. rewrite v_shift_inst in rule.
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. simpl in tyc. auto.
  - apply shape_pair in tyv. destruct tyv as [tyv1 tyv2].
    eapply has_vtype_is_under_ctx. eauto.
  - apply shape_pair in tyv. destruct tyv as [tyv1 tyv2].
    eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_summatch in H0 as parts. 
  destruct parts as [A[B[tyv[tyc1 tyc2]]]].
  simpl in *. apply Ceq; auto. 
  specialize (βΣMatch_Inl (v_inst v I)
    (c_inst c1 (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out.
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc1. auto.
  - apply shape_sum_inl in tyv. eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_summatch in H0 as parts. 
  destruct parts as [A[B[tyv[tyc1 tyc2]]]].
  simpl in *. apply Ceq; auto. 
  specialize (βΣMatch_Inr (v_inst v I)
    (c_inst c1 (InstU (inst_shift I 1 0) (Var 0)))
    (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out.
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc2. auto.
  - apply shape_sum_inr in tyv. eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_listmatch in H0 as parts. 
  destruct parts as [A[tyv[tyc1 tyc2]]].
  simpl in *. apply Ceq; auto. 
  specialize (βListMatch_Nil (c_inst c1 I) ) as rule.
  apply rule.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_listmatch in H0 as parts. 
  destruct parts as [A[tyv[tyc1 tyc2]]].
  simpl in *. apply Ceq; auto. 
  specialize (βListMatch_Cons (v_inst v I) (v_inst vs I)
    (c_inst c1 I)
    (c_inst c2 (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    ) as rule.
  unfold c_subs2_out in rule. unfold c_subs_out in rule.
  rewrite c_inst_subs2_out. rewrite v_shift_inst in rule. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc2. auto.
  - apply shape_list_cons in tyv. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
  - apply shape_list_cons in tyv. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_app in H0 as parts.
  destruct parts as [A[tyc tyv]].
  simpl in *. apply Ceq; auto. 
  specialize (βApp 
    (c_inst c (InstU (inst_shift I 1 0) (Var 0))) (v_inst v I)
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. auto.
  - eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_letrec in H0 as parts.
  destruct parts as [A[C'[tyc1 tyc2]]].
  simpl in *. apply Ceq; auto. 
  specialize (βLetRec
  (c_inst c1 (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
  (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out.
  rewrite c_shift_inst in rule. simpl in *.
  rewrite inst_shift_comm, inst_shift_shift. simpl.
  assert ( (InstU (InstU (InstU (inst_shift (inst_shift I 2 0) 1 2) 
      (Var 2)) (Var 1)) (Var 0))
    = inst_insert (InstU (InstU (inst_shift (inst_shift I 2 0) 1 2) 
      (Var 1)) (Var 0)) 2 (Var 2)) as same.
  {simpl. destruct I; auto. }
  rewrite same, c_inst_no_var_same, c_negshift_shift, c_shift_0. apply rule.
  all: simpl; omega || auto.
  all: clear rule; try clear same.
  - apply c_shift_makes_no_var.
  - rewrite inst_len_shift, inst_len_shift, same_len. apply c_under_var_shift.
    eapply has_ctype_is_under_ctx in tyc1. auto. omega.
  - eapply has_ctype_is_under_ctx in tyc2. rewrite same_len. auto.
  - rewrite same_len. eapply has_ctype_is_under_ctx in tyc1. aconstructor.
    eapply c_under_var_shift. auto. omega.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  destruct C as [A Σ E].
  apply shape_dobind in H0 as parts.
  destruct parts as [A'[tyret tyc]].
  simpl in *. apply Ceq; auto. 
  specialize (βDoBind_Ret (v_inst v I)
    (c_inst c (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. auto.
  - eapply has_vtype_is_under_ctx. apply shape_ret in tyret. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  destruct C as [A Σ E].
  apply shape_dobind in H0 as parts.
  destruct parts as [A'[tyc1 tyc2]].
  simpl in *. apply Ceq; auto. 
  specialize (βDoBind_Op op (v_inst v I)
    (c_inst c1 (InstU (inst_shift I 1 0) (Var 0)))
    (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  rewrite c_shift_inst in rule. simpl in rule.
  rewrite <-inst_shift_comm in rule.
  assert ( (InstU (InstU (inst_shift (inst_shift I 1 0) 1 0) 
     (Var 1)) (Var 0))
    = inst_insert (InstU (inst_shift (inst_shift I 1 0) 1 0) (Var 0))
     1 (Var 1)) as same.
  { simpl. destruct I; auto. }
  rewrite same, c_inst_no_var_same, c_negshift_shift, c_shift_0. apply rule.
  all: simpl; omega || auto.
  - apply c_shift_makes_no_var.
  - rewrite inst_len_shift, inst_len_shift, same_len.
    apply c_under_var_shift. apply has_ctype_is_under_ctx in tyc2.
    auto. omega.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_handle in H0 as parts.
  destruct parts as [C'[tyh tyc]].
  simpl in *. apply Ceq; auto. 
  specialize (βHandle_Ret (c_inst c_r (InstU (inst_shift I 1 0) (Var 0)))
  (h_inst h I) (v_inst v I)
  ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len; destruct C'.
  - apply shape_handler in tyh. destruct tyh as [Σ[D[tycr _]]].
    apply has_ctype_is_under_ctx in tycr. auto.
  - eapply has_vtype_is_under_ctx. apply shape_ret in tyc. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  eapply find_inst_Some in H2 as finds. 2: reflexivity.
  apply shape_handle in H0 as parts.
  destruct parts as [C'[tyh tyc]].
  simpl in *. apply Ceq; auto. 
  specialize (βHandle_Op
    (c_inst c_r (InstU (inst_shift I 1 0) (Var 0)))
    (h_inst h I) op (v_inst v I)
    (c_inst c_k (InstU (inst_shift I 1 0) (Var 0)))
    (c_inst c_op (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    C Γ finds
    ) as rule.
  simpl in *.
  unfold c_subs2_out in rule. unfold c_subs_out in rule.
  rewrite c_inst_subs2_out. rewrite c_shift_inst in rule. simpl in *.
  assert (
    InstU (InstU (inst_shift (inst_shift I 1 0) 1 0) (Var 1)) (Var 0) =
    inst_insert (InstU (inst_shift (inst_shift I 1 0) 1 0) (Var 0)) 1 (Var 1)).
  { simpl. destruct I; auto. }
  assert (
    (InstU (inst_shift I 1 0) (Var 0)) =
    inst_insert (inst_shift I 1 0) 0 (Var 0)).
  { simpl. destruct I; auto. }
  rewrite H3, c_inst_no_var_same.
  rewrite H4, h_inst_no_var_same, <-H4.
  rewrite c_negshift_shift, c_shift_0, h_negshift_shift, h_shift_0. simpl.
  rewrite inst_shift_comm. rewrite v_shift_inst, h_shift_inst in rule.
  apply rule. 
  all: simpl; omega || auto; try clear rule; clear tys1 tys2.
  all: try rewrite inst_len_shift; try rewrite inst_len_shift.
  all: try rewrite same_len.
  all: destruct C' as [A Σ E]; apply shape_handler in tyh;
       destruct tyh as [Σ'[D'[tycr[tyh[res[sty csty]]]]]].
  all: eapply shape_op in tyc; destruct tyc as [Aop[Bop[gets[tyv tyck]]]].
  6: constructor. 6: constructor.
  - apply h_shift_makes_no_var.
  - apply h_under_var_shift. eapply has_htype_is_under_ctx. eauto. omega.
  - apply c_shift_makes_no_var.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in tycr. auto. omega.
  - eapply sig_subtype_get_Some in sty; eauto. destruct sty as [A'[B'[g _]]].
    eapply case_has_type in H2; eauto.
    eapply has_ctype_is_under_ctx in H2. auto.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in tycr. auto. omega.
  - apply h_under_var_shift. eapply has_htype_is_under_ctx. eauto. omega.
  - apply has_ctype_is_under_ctx in tyck. auto.
  - eapply has_vtype_is_under_ctx. eauto.
+ eapply CL in H0 as tys1; eauto.
  eapply CL in H1 as tys2; eauto.
  clear VL CL HL RL VEL CEL HEL.
  apply wf_inst_len_same in wfinst as same_len.
  apply shape_prodmatch in H1 as parts.
  destruct parts as [A[B[tyv tyc]]].
  simpl in *. apply Ceq; auto.
  erewrite (c_inst_subs 0), (c_inst_subs 2).
  specialize (ηPair Γ (v_inst v I) 0
    (c_inst c (inst_insert (inst_shift I 1 0) n (Var 0))) C
  ) as rule.
  rewrite c_shift_inst, inst_shift_insert in rule. simpl in *.
  assert (c_inst (c_shift c 2 0)
    (InstU (InstU (inst_insert (inst_shift (inst_shift I 2 0) 1 2) (n - 0)
      (Var 2)) (Var 1)) (Var 0))
    = c_inst c (inst_insert (inst_shift (inst_shift I 1 0) 2 0) n (Var 2))).
  { rewrite <-(c_shift_shift 1), instU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0, instU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0. do 2 f_equal.
    rewrite (inst_shift_comm 1). all: omega || auto.
    + apply c_shift_makes_no_var.
    + apply c_under_var_shift; omega || simpl.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.


  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. auto.
  - eapply has_vtype_is_under_ctx. apply shape_ret in tyret. eauto.



