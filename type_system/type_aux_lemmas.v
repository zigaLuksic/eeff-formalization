Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".

Require Export subtyping_lemmas substitution_lemmas.

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
  wf_vtype A_ins ->
  respects (ctx_insert Γ i A_ins) (h_shift h 1 i) Σ D E.

Proof.
all: rename v_insert_typesafe into VL; rename c_insert_typesafe into CL.
all: rename h_insert_typesafe into HL; rename respects_insert_typesafe into RL.
{
intros wfins. apply TypeV.
{ apply wf_ctx_insert. inv orig. all: auto. }
{ inv orig. auto. }
inv orig. destruct H1.
+ clear VL CL HL RL.
  simpl. apply TypeUnit.
+ clear VL CL HL RL.
  simpl. apply TypeInt.
+ clear VL CL HL RL.
  simpl. destruct (i <=? n) eqn:cmp.
  - apply TypeVar. rewrite <-get_ctx_insert_changed.
    auto. apply leb_complete in cmp. omega.
  - apply TypeVar. rewrite <-get_ctx_insert_unchanged.
    auto. apply leb_iff_conv in cmp. auto.
+ specialize (VL _ _ _ H1) as IHv1.
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL.
  simpl. apply TypePair; auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  simpl. apply TypeLeft. auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  simpl. apply TypeRight. auto.
+ clear VL CL HL RL.
  simpl. apply TypeNil.
+ specialize (VL _ _ _ H1) as IHv1.
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL.
  simpl. apply TypeCons; auto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL.
  simpl. apply TypeFun. rewrite ctx_insert_extend. auto.
+ specialize (HL _ _ _ _ H2) as IHh.
  specialize (CL _ _ _ H1) as IHc.
  specialize (RL _ _ _ _ _ H3) as IHres.
  clear VL CL HL RL.
  simpl. apply TypeHandler. rewrite ctx_insert_extend. all: auto. 
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  eapply TypeVSubsume; auto.
}{
intros wfins. apply TypeC.
{ apply wf_ctx_insert. inv orig. all: assumption. }
{ inv orig. assumption. }
inv orig. destruct H1.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  simpl. apply TypeRet. auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  simpl. apply TypeAbsurd. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeProdMatch. auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeSumMatch. auto.
  all: rewrite ctx_insert_extend; auto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeListMatch; auto.
  rewrite ctx_insert_extend. rewrite ctx_insert_extend. auto.
+ specialize (CL _ _ _ H1) as IHc1.
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeDo. auto. rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (VL _ _ _ H2) as IHv0.
  clear VL CL HL RL.
  simpl. eapply TypeApp; auto.
+ specialize (VL _ _ _ H1) as IHv.
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeHandle; auto.
+ specialize (CL _ _ _ H1) as IHc1.
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeLetRec.
  - do 2 rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ specialize (VL _ _ _ H2) as IHv.
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeOp; eauto. 
  rewrite ctx_insert_extend. all: eauto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL.
  eapply TypeCSubsume; auto.
}{
intros wfins. apply TypeH.
{ apply wf_ctx_insert. inv orig. all: assumption. }
all: try (inv orig; assumption).
inv orig. destruct H2.
+ simpl. clear VL CL HL RL. apply TypeCasesØ.
+ specialize (HL _ _ _ _ H2) as IHh.
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL.
  simpl. apply TypeCasesU. auto.
  do 2 rewrite ctx_insert_extend. auto.
}{
intros wfins. apply Respects.
{ clear VL CL HL RL. apply wf_ctx_insert. inv orig. all: auto. }
all: inv orig; auto.
destruct H4. apply RespectAlways.
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
  respects Γ h Σ D E -> wf_vtype A0 ->
  respects (CtxU Γ A0) (h_shift h 1 0) Σ D E.

Proof.
all: intros orig;
assert (ctx_insert Γ 0 A0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H.
apply v_insert_typesafe. assumption.
apply c_insert_typesafe. assumption.
apply h_insert_typesafe. assumption.
apply respects_insert_typesafe. assumption.
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
  get_vtype Γ i = Some A_s -> has_vtype Γ v_s A_s ->
  respects Γ (h_sub h (i, v_s)) Σ D E.

Proof.
all: rename v_sub_typesafe into VL; rename c_sub_typesafe into CL.
all: rename h_sub_typesafe into HL; rename respects_sub_typesafe into RL.
{
intros gets tyvs. apply TypeV; inv orig.
assumption. assumption. destruct H1.
+ clear VL CL HL RL. 
  simpl. apply TypeUnit.
+ clear VL CL HL RL. 
  simpl. apply TypeInt.
+ clear VL CL HL RL.
  simpl. destruct (n =? i) eqn:cmp.
  - apply Nat.eqb_eq in cmp. rewrite cmp in *. rewrite H1 in gets.
    injection gets. intro. subst. inv tyvs. assumption.
  - apply TypeVar. assumption.
+ specialize (VL _ _ _ H1) as IHv1. 
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL.
  simpl. apply TypePair; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL.
  apply TypeLeft; eauto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  apply TypeRight; eauto.
+ clear VL CL HL RL.
  apply TypeNil; eauto.
+ specialize (VL _ _ _ H1) as IHv1. 
  specialize (VL _ _ _ H2) as IHv2.
  clear VL CL HL RL.
  simpl. apply TypeCons; eauto.
+ specialize (CL _ _ _ H1) as IHc. 
  specialize (VL _ _ _ tyvs) as IHvs.
  clear VL CL HL RL.
  simpl. apply TypeFun. eapply IHc. eauto.
  inv H0. apply v_shift_typesafe; auto.
+ specialize (HL _ _ _ _ H2) as IHh. 
  specialize (CL _ _ _ H1) as IHc.
  specialize (RL _ _ _ _ _ H3) as IHr.
  clear VL CL HL RL.
  simpl. apply TypeHandler; eauto. eapply IHc. 
  exact gets. inv H0. inv H6. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H1) as IHv.
  clear VL CL HL RL.
  eapply TypeVSubsume; eauto.
}{
intros gets tyvs. apply TypeC; inv orig. auto. auto. destruct H1.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL.
  apply TypeRet; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  clear VL CL HL RL.
  apply TypeAbsurd; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeProdMatch; eauto.
  - eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H4; assumption.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeSumMatch. eauto.
  - eapply IHc1. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto. 
  - eapply IHc2. exact gets. inv H1. inv H5. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc1.
  specialize (CL _ _ _ H3) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeListMatch. eauto.
  - eapply IHc1. exact gets. auto.
  - eapply IHc2. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1. inv H5. all:auto.
+ specialize (CL _ _ _ H1) as IHc1. 
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeDo. eauto.
  eapply IHc2. exact gets. inv H1. inv H4. apply v_shift_typesafe; auto. 
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (VL _ _ _ H2) as IHv0.
  clear VL CL HL RL.
  simpl. eapply TypeApp; eauto.
+ specialize (VL _ _ _ H1) as IHv. 
  specialize (CL _ _ _ H2) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeHandle; eauto.
+ specialize (CL _ _ _ H1) as IHc1. 
  specialize (CL _ _ _ H2) as IHc2.
  clear VL CL HL RL.
  simpl. eapply TypeLetRec.
  - eapply IHc1. exact gets. rewrite <-(v_shift_shift 1 1 0).
    apply v_shift_typesafe. apply v_shift_typesafe. assumption.
    all: inv H1; inv H3. 2: assumption. inv H7. assumption. 
  - eapply IHc2. exact gets. inv H1. inv H3. apply v_shift_typesafe; auto.
+ specialize (VL _ _ _ H2) as IHv. 
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL.
  simpl. eapply TypeOp; eauto.
  eapply IHc. exact gets. inv H3. inv H4. apply v_shift_typesafe; auto.
+ specialize (CL _ _ _ H1) as IHc.
  clear VL CL HL RL.
  eapply TypeCSubsume; eauto.
}{
intros gets tyvs; simpl; apply TypeH; inv orig. auto. auto. auto.
destruct H2.
+ clear VL CL HL RL. 
  apply TypeCasesØ.
+ specialize (HL _ _ _ _ H2) as IHh. 
  specialize (CL _ _ _ H3) as IHc.
  clear VL CL HL RL.
  simpl. apply TypeCasesU; eauto.
  eapply IHc. exact gets. rewrite <-(v_shift_shift 1 1 0).
  apply v_shift_typesafe. apply v_shift_typesafe. assumption.
  all: inv H0. auto. apply WfTyFun; assumption.
}{
intros gets tyvs; simpl. apply Respects; destruct orig; auto.
{ eapply HL. clear VL CL HL RL. all: eauto. }
destruct H4. apply RespectAlways.
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
  has_vtype Γ v_s A_s -> Γ' = ctx_insert Γ i A_s ->
  ctx_len Γ >= i ->
  respects Γ (h_subs h i v_s) Σ D E.


Proof.
all: rename v_subs_typesafe into VL; rename c_subs_typesafe into CL.
all: rename h_subs_typesafe into HL; rename respects_subs_typesafe into RL.
{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1.
+ clear VL CL HL RL. 
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeUnit.
+ clear VL CL HL RL. 
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeInt.
+ clear VL CL HL RL. 
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
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypePair; auto.  
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeLeft; auto.  
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeRight; auto.
+ clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeNil; auto.
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH1.
  specialize (VL Γ Γ0 vs _ i _ _ H2 tyvs geq) as IH2.
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeCons; auto.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s).
  { simpl. f_equal. auto. }
  inv H0. specialize (v_shift_typesafe _ Γ A _ tyvs H5) as tyvs'.
  specialize (CL _ _ c _ (1+i) _ _ H1 tyvs') as IH. 
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl. apply WfTyFun; auto.
  apply TypeFun. rewrite v_shift_comm. apply IH.
  simpl. f_equal. simpl. omega. omega.
+ assert (CtxU Γ0 A = ctx_insert (CtxU Γ A) (1+i) A_s).
  { simpl. f_equal. auto. }
  assert (wf_vtype A) as wfa by (inv H0; inv H7; assumption).
  specialize (v_shift_typesafe _ Γ A _ tyvs wfa) as tyvs'.
  specialize (CL _ _ cr _ (1+i) _ _ H1 tyvs' H4) as IHc. 
  specialize (HL _ _ h _ _ i _ _ H2 tyvs geq) as IHh. 
  specialize (RL _ _ h _ _ _ i _ _ H3 tyvs) as IHr.
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl.
  apply TypeHandler. rewrite v_shift_comm. apply IHc. simpl. all: aomega.
+ specialize (VL Γ Γ0 v _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL.
  apply TypeV; auto; unfold v_subs; simpl. 
  eapply TypeVSubsume; eauto.
}{
intros tyvs geq len. 
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H1. 
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl.
  apply TypeRet. auto.
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IH.
  clear VL CL HL RL.
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
  clear VL CL HL RL.
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
  clear VL CL HL RL.
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
  clear VL CL HL RL.
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
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeDo. eauto. 
  rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ specialize (VL _ _ v1 _ i _ _ H1 tyvs) as IH1.
  specialize (VL _ _ v2 _ i _ _ H2 tyvs) as IH2.
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeApp. eauto. eauto.
+ specialize (VL _ _ v _ i _ _ H1 tyvs) as IHv.
  specialize (CL _ _ c _ i _ _ H2 tyvs) as IHc.
  clear VL CL HL RL.
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
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeLetRec. 
  - rewrite v_shift_shift in IHc1. rewrite v_shift_comm. apply IHc1. 
    simpl. omega. omega.
  - rewrite v_shift_comm. apply IHc2. simpl. omega. omega.
+ assert (CtxU Γ0 Bop = ctx_insert (CtxU Γ Bop) (1+i) A_s) as geqb.
  { simpl. f_equal. auto. }
  assert (wf_vtype Bop) as wfb. { inv H3. inv H4. auto. }
  specialize (v_shift_typesafe _ _ Bop _ tyvs wfb) as tyvsb.
  specialize (VL _ _ v _ i _ _ H2 tyvs geq) as IHv.
  specialize (CL _ _ c _ (1+i) _ _ H3 tyvsb geqb) as IHc.
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl.
  eapply TypeOp; eauto.
  rewrite v_shift_comm. apply IHc. simpl. omega. omega.
+ specialize (CL Γ Γ0 c _ i _ _ H1 tyvs geq) as IH.
  clear VL CL HL RL.
  apply TypeC; auto; unfold c_subs; simpl. 
  eapply TypeCSubsume; eauto.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H2.
+ clear VL CL HL RL.
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
  clear VL CL HL RL.
  apply TypeH; auto; unfold h_subs; simpl.
  eapply TypeCasesU; auto.
  rewrite v_shift_shift in IHc. rewrite v_shift_comm. apply IHc. 
  simpl. omega. omega.
}{
intros tyvs geq len.
assert (wf_ctx Γ) as wfg by (inv tyvs; assumption).
destruct orig. destruct H4.
specialize (HL _ _ _ _ _ i v_s _ H3 tyvs geq) as IHh.
clear VL CL HL RL.
apply Respects; auto. apply RespectAlways.
}
Qed.
