(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".

Require Export syntax_lemmas substitution_lemmas 
  type_lemmas instantiation_lemmas.


Lemma operational_in_logic Γ c c' C:
  has_ctype Γ c C -> step c c'-> ceq C Γ c c'. 
Proof.
intros tys steps.
assert (has_ctype Γ c' C) as tys' by (eapply preservation; eauto).
revert C tys tys'. induction steps; intros C tys tys'; apply Ceq.
all: assumption || (inv tys; assumption) || auto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βListMatch_Nil.
+ eapply βListMatch_Cons.
+ eapply βApp.
+ eapply βLetRec.
+ destruct C as [A Σ E]. eapply shape_dobind_full in tys.
  3: reflexivity. 2: reflexivity. destruct tys as [A' [ty1 ty2]].
  eapply CeqDoBind.
  - eapply IHsteps. eauto. eapply preservation; eauto.
  - apply ceq_refl. auto.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op. 
+ eapply shape_handle in tys. destruct tys as [C' [tyh tyc]].
  eapply CeqHandle. 
  - apply veq_refl. eauto.
  - apply IHsteps. assumption. eapply preservation; eauto.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
Qed.

(* ==================== Substitution is Safe in Logic ==================== *)

Fixpoint veq_subs_logicsafe_weak
  Γ Γ' A v i v_s v_s' A_s (orig: has_vtype Γ' v A) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  veq A Γ (v_subs v i v_s) (v_subs v i v_s')

with ceq_subs_logicsafe_weak
  Γ Γ' C c i v_s v_s' A_s (orig: has_ctype Γ' c C) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c i v_s) (c_subs c i v_s')

with heq_subs_logicsafe_weak
  Γ Γ' Σ D h i v_s v_s' A_s (orig: has_htype Γ' h Σ D) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h i v_s) (h_subs h i v_s').

Proof.
all: rename veq_subs_logicsafe_weak into VEQ.
all: rename ceq_subs_logicsafe_weak into CEQ.
all: rename heq_subs_logicsafe_weak into HEQ.
{
intros vseq ctxs clen. apply Veq; try (inv orig; eassumption).
eapply v_subs_typesafe; inv vseq; eauto. 
eapply v_subs_typesafe; inv vseq; eauto.
destruct orig. destruct H1.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqInt.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. 
  destruct (n=?i) eqn: ni; simpl.
  - rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    apply Nat.eqb_eq in ni. subst. rewrite get_ctx_insert_new in H1. inv H1. 
    inv vseq. assumption. all: omega || assumption.
  - assert (veq A Γ 
      (if i <=? n then Var (n-1) else Var n)
      (if i <=? n then Var (n-1) else Var n)).
    apply veq_refl. apply TypeV; auto.
    { inv vseq. inv H2. assumption. }
    destruct (i<=?n) eqn: cmp.
    * apply TypeVar. subst. erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * apply TypeVar. subst. erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. assumption.
    * inv H2. assumption.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqPair; eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqInl. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqInr. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqListNil.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqListCons; eapply VEQ; eauto.
+ clear VEQ HEQ. unfold v_subs. unfold c_subs in CEQ. simpl. 
  apply VeqFun. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). 
  eapply CEQ; eauto. apply veq_shift_typesafe; eauto.
  inv H0. auto. subst. apply ctx_insert_extend. simpl. all: omega.
+ clear VEQ. unfold v_subs. unfold c_subs in CEQ. unfold h_subs in HEQ. simpl.
  eapply VeqHandler. 3: apply csubtype_refl; inv H0; assumption.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply veq_shift_typesafe; eauto. inv H0. inv H6. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
  - eapply HEQ; eauto.
+ assert (veq A' Γ (v_subs v i v_s) (v_subs v i v_s')).
  eapply veq_subtype; eauto. inv H3. assumption.
}{
intros vseq ctxs clen. apply Ceq; try (inv orig; eassumption).
eapply c_subs_typesafe; inv vseq; eauto. 
eapply c_subs_typesafe; inv vseq; eauto.
destruct orig. destruct H1.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqRet. eauto.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqAbsurd.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqΠMatch. eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  rewrite <-(v_shift_shift 1 1), <-(v_shift_shift 1 1).
  apply veq_shift_typesafe. apply veq_shift_typesafe. eauto.
  inv H1. inv H4. assumption. inv H1. inv H4. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqΣMatch. eauto.
  all: rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply veq_shift_typesafe; eauto.
  inv H1. inv H5. assumption. subst. apply ctx_insert_extend. simpl.
  all: try omega. eapply CEQ; eauto. apply veq_shift_typesafe; eauto.
  inv H1. inv H5. assumption. subst. apply ctx_insert_extend. simpl. omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqListMatch; eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  rewrite <-(v_shift_shift 1 1), <-(v_shift_shift 1 1).
  apply veq_shift_typesafe. apply veq_shift_typesafe. eauto.
  inv H1. inv H5. assumption. inv H1. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ VEQ. unfold c_subs in *. simpl.
  eapply CeqDoBind. eauto. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply veq_shift_typesafe; eauto.
  inv H1. inv H4. assumption. subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs. unfold v_subs in *. simpl. eapply CeqApp; eauto.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl.
  eapply CeqHandle; eauto.
+ clear VEQ HEQ. unfold c_subs in *. simpl. eapply CeqLetRec.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    rewrite <-(v_shift_shift 1 1), <-(v_shift_shift 1 1 _ v_s'). 
    apply veq_shift_typesafe. apply veq_shift_typesafe. eauto.
    inv H1. inv H3. inv H8. eauto. inv H1. inv H3. eauto.
    subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
    simpl. all: omega.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply veq_shift_typesafe. eauto. inv H2. inv H3. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply veq_shift_typesafe. eauto. inv H3. inv H4. assumption.
  subst. apply ctx_insert_extend. simpl. all: omega.
+ assert (ceq C' Γ (c_subs c i v_s) (c_subs c i v_s')).
  eapply ceq_subtype; eauto. inv H3. assumption.
}{
intros vseq ctxs clen. destruct orig. destruct H2.
+ clear VEQ CEQ HEQ. 
  assert (has_htype Γ CasesØ SigØ D).
  {apply TypeH. inv vseq. inv H2. 2:apply WfSigØ. all:auto. apply TypeCasesØ. }
  eapply Heq; eauto; try (apply sig_subtype_refl; assumption). 
  all: unfold h_subs; simpl. apply HeqSigØ.
+ unfold h_subs in *. unfold c_subs in *. simpl.
  eapply HEQ in H2 as IHh; eauto. eapply CEQ in H3 as IHc.
  all: clear VEQ CEQ HEQ.
  4: instantiate (2:=CtxU (CtxU Γ (TyFun Bop D)) Aop).
  Focus 3. 
    erewrite <-ctx_insert_extend. f_equal. erewrite <-ctx_insert_extend.
    f_equal. eauto.
  Focus 2.
    eapply veq_shift_typesafe. eapply veq_shift_typesafe. eauto.
    apply WfTyFun. all: inv H0; auto.
  eapply heq_case_extend_structural; eauto.
  all: try rewrite v_shift_shift, v_shift_shift in IHc; simpl in *.
  - apply negshift_get_case_None. apply sub_get_case_None.
    inv H0. eapply wf_sig_unique_cases; eauto.
  - apply negshift_get_case_None. apply sub_get_case_None.
    inv H0. eapply wf_sig_unique_cases; eauto.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). assumption. all: omega.
  - omega.
}
Qed.


Fixpoint veq_subs_logicsafe
  Γ Γ' A v1 v2 i v_s v_s' A_s (orig: veq A Γ' v1 v2) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  veq A Γ (v_subs v1 i v_s) (v_subs v2 i v_s')

with ceq_subs_logicsafe
  Γ Γ' C c1 c2 i v_s v_s' A_s (orig: ceq C Γ' c1 c2) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c1 i v_s) (c_subs c2 i v_s')

with heq_subs_logicsafe
  Γ Γ' Σ D h1 h2 i v_s v_s' A_s (orig: heq Σ D Γ' h1 h2) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h1 i v_s) (h_subs h2 i v_s').
Proof.
all: intros vseq ctxs clen.
{
assert (veq A Γ (v_subs v1 i v_s) (v_subs v1 i v_s')).
eapply veq_subs_logicsafe_weak; eauto. inv orig. eauto.
eapply veq_trans; eauto. eapply veq_subs_typesafe; eauto. inv vseq. auto.
}{
assert (ceq C Γ (c_subs c1 i v_s) (c_subs c1 i v_s')).
eapply ceq_subs_logicsafe_weak; eauto. inv orig. eauto.
eapply ceq_trans; eauto. eapply ceq_subs_typesafe; eauto. inv vseq. auto.
}{
inv orig.
assert (heq Σ D Γ (h_subs h1 i v_s) (h_subs h1 i v_s')).
eapply heq_subtype. 3:exact H0. eapply heq_subs_logicsafe_weak. all: eauto.
eapply heq_trans; eauto. eapply heq_subs_typesafe; eauto.
eapply Heq. 2: exact H0. all:eauto. inv vseq. assumption.
}
Qed.


(* ==================== Context Modification ==================== *)

Fixpoint veq_join_ctxs Γ Γ' v1 v2 A:
  wf_ctx Γ' -> veq A Γ v1 v2 -> veq A (join_ctxs Γ' Γ) v1 v2
with ceq_join_ctxs Γ Γ' c1 c2 C:
  wf_ctx Γ' -> ceq C Γ c1 c2 -> ceq C (join_ctxs Γ' Γ) c1 c2
with heq_join_ctxs Γ Γ' h1 h2 Σ D:
  wf_ctx Γ' -> heq Σ D Γ h1 h2 -> heq Σ D (join_ctxs Γ' Γ) h1 h2 .
Proof.
all: intros wfc' orig.
+ destruct Γ'.
  - rewrite join_ctxs_CtxØ. auto.
  - rewrite join_ctxs_CtxU. auto. 
    apply veq_join_ctxs. inv wfc'. eauto.
    rewrite <-(v_shift_too_high v1 1 (ctx_len Γ)).
    rewrite <-(v_shift_too_high v2 1 (ctx_len Γ)).
    apply veq_insert_typesafe. auto. inv wfc'. auto. 
    all: eapply has_vtype_is_under_ctx; inv orig; eauto.
+ destruct Γ'.
  - rewrite join_ctxs_CtxØ. auto.
  - rewrite join_ctxs_CtxU. auto. 
    apply ceq_join_ctxs. inv wfc'. eauto.
    rewrite <-(c_shift_too_high c1 1 (ctx_len Γ)).
    rewrite <-(c_shift_too_high c2 1 (ctx_len Γ)).
    apply ceq_insert_typesafe. auto. inv wfc'. auto. 
    all: eapply has_ctype_is_under_ctx; inv orig; eauto.
+ destruct Γ'.
  - rewrite join_ctxs_CtxØ. auto.
  - rewrite join_ctxs_CtxU. auto. 
    apply heq_join_ctxs. inv wfc'. eauto.
    rewrite <-(h_shift_too_high h1 1 (ctx_len Γ)).
    rewrite <-(h_shift_too_high h2 1 (ctx_len Γ)).
    apply heq_insert_typesafe. auto. inv wfc'. auto.
    all: inv orig; eapply has_htype_is_under_ctx; eauto.
Qed.

(* 
Lemma handle_t_makes_sense Γ' x c_r h A Σ E D Γ Z T:
  has_vtype Γ' (Handler x c_r h)  (TyHandler (CTy A Σ E) D) ->
  wf_t Γ Z T Σ ->
  ceq D (join_ctxs Γ' (join_ctx_tctx Γ Z D))
    (handle_t (ctx_len Γ) (tctx_len Z) h T)
    (Handle 
      (Sub.v_shift (Handler x c_r h) (ctx_len Γ + tctx_len Z) 0) 
      (instantiate_t (tctx_len Z) T))
.
Proof.
induction T; intros htys wft.
+ simpl. *)

(* h : C => D -> c1 ~C c2 -> with h handle c1 ~D with h handle c2 *)