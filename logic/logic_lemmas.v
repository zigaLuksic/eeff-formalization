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

Require Export syntax_lemmas substitution_lemmas type_lemmas.


Lemma operational_in_logic Γ c c' C:
  has_ctype Γ c C -> step c c'-> judg Γ HypØ (Ceq C c c'). 
Proof.
intros tys steps.
assert (has_ctype Γ c' C) as tys' by (eapply preservation; eauto).
revert C tys tys'. induction steps; intros C tys tys'; apply WfJudg.
all: apply WfCeq || apply WfHypØ || auto.
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
    apply wf_hyp_shift_typesafe. apply WfHypØ.
    inv ty1. auto. inv ty2. inv H. auto.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op. 
+ eapply shape_handle in tys. destruct tys as [C' [tyh tyc]].
  eapply CeqHandle. 
  - apply veq_refl. eauto. apply WfHypØ. inv tyc. auto.
  - apply IHsteps. assumption. eapply preservation; eauto.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
Qed.

(* ==================== Substitution is Safe in Logic ==================== *)

Fixpoint veq_subs_logicsafe_weak
  Γ Γ' Ψ A v (orig: has_vtype Γ' v A) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Veq A (v_subs v i v_s) (v_subs v i v_s'))

with ceq_subs_logicsafe_weak
  Γ Γ' Ψ C c (orig: has_ctype Γ' c C) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Ceq C (c_subs c i v_s) (c_subs c i v_s'))

with heq_subs_logicsafe_weak
  Γ Γ' Ψ Σ D h (orig: has_htype Γ' h Σ D) i v_s v_s' A_s {struct orig} :
  judg Γ Ψ (Veq A_s v_s v_s') -> Γ' = ctx_insert Γ i A_s -> ctx_len Γ >= i ->
  judg Γ Ψ (Heq Σ D (h_subs h i v_s) (h_subs h i v_s')).

Proof.
all: rename veq_subs_logicsafe_weak into VEQ.
all: rename ceq_subs_logicsafe_weak into CEQ.
all: rename heq_subs_logicsafe_weak into HEQ.
all: intros vseq ctxs clen.
all: assert (forall A, wf_vtype A -> 
      judg (CtxU Γ A) (hyp_shift Ψ 1 0) 
        (Veq A_s (v_shift v_s 1 0) (v_shift v_s' 1 0)) ) as vseq_ext by
  (intros; eapply judg_shift_typesafe in vseq; simpl in vseq; eauto).
{
apply WfJudg. apply WfVeq.
{ inv vseq. inv H. eapply v_subs_typesafe; eauto. }
{ inv vseq. inv H. eapply v_subs_typesafe; eauto. }
{ inv vseq. auto. }
destruct orig. destruct H1.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqInt.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. 
  destruct (n=?i) eqn: ni; simpl.
  - rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    apply Nat.eqb_eq in ni. subst. rewrite get_ctx_insert_new in H1. inv H1. 
    inv vseq. assumption. all: omega || assumption.
  - assert (judg Γ Ψ (Veq A 
      (if i <=? n then Var (n-1) else Var n)
      (if i <=? n then Var (n-1) else Var n))).
    apply veq_refl. apply TypeV; auto.
    { inv vseq. inv H2. inv H8. assumption. }
    destruct (i<=?n) eqn: cmp.
    * apply TypeVar. subst. erewrite get_ctx_insert_changed.
      all: apply Nat.eqb_neq in ni; apply leb_complete in cmp.
      assert (1+(n-1)=n) by omega. rewrite H2. eauto. omega.
    * apply TypeVar. subst. erewrite get_ctx_insert_unchanged. eauto.
      apply leb_complete_conv in cmp. assumption.
    * inv vseq. auto.
    * inv H2. assumption.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqPair; eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqInl. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqInr. eapply VEQ; eauto.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqListNil.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqListCons; eapply VEQ; eauto.
+ clear VEQ HEQ. unfold v_subs. unfold c_subs in CEQ. simpl. 
  apply VeqFun. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext.
  inv H0. auto. subst. apply ctx_insert_extend. simpl. all: omega.
+ clear VEQ. unfold v_subs. unfold c_subs in CEQ. unfold h_subs in HEQ. simpl.
  eapply VeqHandler. 3: apply csubtype_refl; inv H0; assumption.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_ext. inv H0. inv H6. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
  - eapply HEQ; eauto.
+ assert (judg Γ Ψ (Veq A' (v_subs v i v_s) (v_subs v i v_s'))).
  eapply veq_subtype. 2: reflexivity. all: eauto. inv H3. assumption.
}{
assert (forall A B, wf_vtype A -> wf_vtype B -> 
judg (CtxU (CtxU Γ B) A) (hyp_shift Ψ 2 0) 
  (Veq A_s (v_shift v_s 2 0) (v_shift v_s' 2 0)) ) as vseq_extext.
{ intros. eapply judg_shift_typesafe in vseq. 
  eapply judg_shift_typesafe in vseq. 
  rewrite hyp_shift_shift, form_shift_shift in vseq. simpl in vseq.
  eauto. all: eauto. } 
apply WfJudg. apply WfCeq.
{ inv vseq. inv H. eapply c_subs_typesafe; eauto. }
{ inv vseq. inv H. eapply c_subs_typesafe; eauto. }
{ inv vseq. auto. }
destruct orig. destruct H1.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqRet. eauto.
+ clear CEQ HEQ. unfold c_subs. unfold v_subs in VEQ. simpl.
  apply CeqAbsurd. eauto.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqΠMatch. eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply vseq_extext.
  inv H1. inv H4. assumption. inv H1. inv H4. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqΣMatch. eauto.
  all: rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext. inv H1. inv H5.
  assumption. subst. apply ctx_insert_extend. simpl.
  all: try omega. 
  eapply CEQ; eauto. apply vseq_ext. inv H1. inv H5.
  assumption. subst. apply ctx_insert_extend. simpl. omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in VEQ. simpl.
  eapply CeqListMatch; eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply vseq_extext. inv H1. assumption. inv H1. inv H5. assumption.
  subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
  simpl. all: omega.
+ clear HEQ VEQ. unfold c_subs in *. simpl.
  eapply CeqDoBind. eauto. rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s').
  eapply CEQ; eauto. apply vseq_ext.
  inv H1. inv H4. assumption. subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs. unfold v_subs in *. simpl. eapply CeqApp; eauto.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl.
  eapply CeqHandle; eauto.
+ clear VEQ HEQ. unfold c_subs in *. simpl. eapply CeqLetRec.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_extext.
    inv H1. inv H3. eauto. inv H1. inv H3. inv H8. eauto.
    subst. rewrite ctx_insert_extend, ctx_insert_extend. reflexivity.
    simpl. all: omega.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
    apply vseq_ext. inv H2. inv H3. assumption.
    subst. apply ctx_insert_extend. simpl. all: omega.
+ clear HEQ. unfold c_subs in *. unfold v_subs in *. simpl. eapply CeqOp; eauto.
  rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). eapply CEQ; eauto.
  apply vseq_ext. inv H3. inv H4. assumption.
  subst. apply ctx_insert_extend. simpl. all: omega.
+ assert (judg Γ Ψ (Ceq C' (c_subs c i v_s) (c_subs c i v_s'))).
  eapply ceq_subtype. 2: reflexivity. all: eauto. inv H3. assumption.
}{
(* Delaying the WfJudg allows us to use the heq_case_extend_structural. *)
destruct orig. destruct H2.
+ clear VEQ CEQ HEQ. 
  unfold h_subs; simpl.
  apply WfJudg. eapply WfHeq. auto.
  all: apply HeqSigØ || apply TypeH || apply sig_subtype_refl || auto.
  all: apply WfSigØ || apply TypeCasesØ || inv vseq; auto.
  all: inv H2; inv H8; auto.
+ unfold h_subs in *. unfold c_subs in *. simpl.
  eapply HEQ in H3; eauto. eapply CEQ in H4. all: clear VEQ CEQ HEQ.
  4: instantiate (2:=CtxU (CtxU Γ Aop) (TyFun Bop D)).
  Focus 3. 
    erewrite <-ctx_insert_extend. f_equal. erewrite <-ctx_insert_extend.
    f_equal. eauto.
  Focus 2.
    eapply judg_shift_typesafe in vseq. eapply judg_shift_typesafe in vseq.
    simpl in vseq. eauto. apply WfTyFun. all: inv H0; auto.
  simpl in H4.
  eapply heq_case_extend_structural; auto.
  all: try rewrite v_shift_shift, v_shift_shift in H4; simpl in *.
  - apply negshift_get_case_None. apply sub_get_case_None. assumption.
  - apply negshift_get_case_None. apply sub_get_case_None. assumption.
  - rewrite v_shift_comm, (v_shift_comm _ _ _ _ v_s'). 
    rewrite hyp_shift_shift in H4. assumption. all: omega.
  - omega.
}
Qed.

