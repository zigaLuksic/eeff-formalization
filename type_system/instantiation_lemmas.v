Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".
Add LoadPath "???\logic".

Require Export subtyping_lemmas substitution_lemmas type_aux_lemmas.

Lemma InstU_is_insert I v:
  InstU I v = inst_insert I 0 v.
Proof.
destruct I; simpl; auto.
Qed.

(* =============== Extending Well Formed Instantiations =============== *)

Lemma wf_inst_InstU A Γ I Γ':
  wf_vtype A -> wf_inst Γ I Γ' ->
  wf_inst (CtxU Γ A) (InstU (inst_shift I 1 0) (Var 0)) (CtxU Γ' A).
Proof.
intros wfa wfi. apply WfInstU.
+ apply TypeV; auto.
  - apply WfCtxU. inv wfi. 2: inv H. all: auto.
  - apply TypeVar. auto.
+ apply wf_inst_shift_typesafe; auto.
Qed.


Fixpoint wf_inst_insert A Γ I Γ' n:
  wf_vtype A -> wf_inst Γ I Γ' ->
  wf_inst (CtxU Γ A) 
    (inst_insert  (inst_shift I 1 0) n (Var 0)) 
    (ctx_insert Γ' n A).
Proof.
intros wfa wfi. destruct I; destruct Γ'; destruct n; simpl; inv wfi.
+ apply WfInstU. apply TypeV. apply WfCtxU. all: auto.
  apply TypeVar. simpl. auto. apply WfInstØ. apply WfCtxU; auto.
+ apply WfInstØ. apply WfCtxU; auto.
+ apply WfInstU. apply TypeV. apply WfCtxU. all: auto. inv H3. auto.
  apply TypeVar. simpl. auto. apply WfInstU. apply v_shift_typesafe; auto.
  apply wf_inst_shift_typesafe; auto.
+ apply WfInstU. apply v_shift_typesafe; auto.
  assert (n-0=n) as same by omega. rewrite same. auto.
Qed.


(* =============== Padding Instantiations =============== *)

Fixpoint inst_pad_by_n I n :=
  match n with
  | 0 =>  I
  | S n => InstU (inst_shift (inst_pad_by_n I n) 1 0) (Var 0)
  end.


Lemma inst_len_pad_by_n I n :
  inst_len (inst_pad_by_n I n) = (inst_len I)+n.
Proof.
revert n. induction I; intros; induction n; simpl; auto.
all: rewrite inst_len_shift; rewrite IHn; simpl; auto.
Qed.


Fixpoint wf_inst_join_ctxs Γ I Γ' Γ0:
  wf_inst Γ I Γ' ->  wf_ctx Γ0 ->
  wf_inst (join_ctxs Γ Γ0) (inst_pad_by_n I (ctx_len Γ0)) (join_ctxs Γ' Γ0).
Proof.
intros orig wfg. destruct Γ0; simpl. auto. apply wf_inst_InstU. 
inv wfg. auto. apply wf_inst_join_ctxs. auto. inv wfg. auto.
Qed.


Lemma wf_inst_pad_for_handle_t Γ I Γ' Γ0 Z D:
  wf_inst Γ I Γ' -> wf_ctx Γ0 -> wf_tctx Z -> wf_ctype D ->
  wf_inst 
    (join_ctxs (join_ctxs Γ (tctx_to_ctx Z D)) Γ0)
    (inst_pad_by_n I (tctx_len Z + ctx_len Γ0))
    (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ0).
Proof.
intros orig wfg wfz wfd.
assert (forall n m, inst_pad_by_n I (n+m) 
  = inst_pad_by_n (inst_pad_by_n I n) m).
{ intros. induction m; simpl. auto.
  assert (n+ S m = S (n+m)) as same by omega. rewrite same. simpl.
  f_equal. rewrite IHm. auto. }
rewrite H. apply wf_inst_join_ctxs. erewrite len_tctx_to_ctx.
apply wf_inst_join_ctxs. auto. apply wf_tctx_to_ctx. all: auto.
Qed.


Fixpoint get_inst_val_shift_pad_var I n m k cut {struct n}:
  m < n ->
  get_inst_val (inst_shift (inst_pad_by_n I n) k cut) m 
  = Some (if cut <=? m then Var (k + m) else Var m).
Proof.
intros. destruct n; simpl. omega. destruct m. auto. 
rewrite get_inst_val_shift. rewrite get_inst_val_shift_pad_var. simpl. auto. omega.
Qed.


Fixpoint get_inst_pad_var I n m:
  m < n ->
  get_inst_val (inst_pad_by_n I n) m = Some (Var m).
Proof.
intro. specialize (get_inst_val_shift_pad_var I n m 0 0) as stronger.
rewrite inst_shift_0 in stronger. rewrite stronger. simpl. auto. omega.
Qed.


Fixpoint get_inst_pad_same I n m {struct n}:
  get_inst_val (inst_pad_by_n I n) (n+m) = 
  f_opt (get_inst_val I m) (fun v =>  Some (v_shift v n 0)).
Proof.
intros. destruct n; simpl. destruct (get_inst_val I m); auto.
simpl. rewrite v_shift_0. auto.
assert (forall I k m,
   get_inst_val (inst_shift I k 0) m 
   = f_opt (get_inst_val I m) (fun v => Some (v_shift v k 0))).
+ intros J. induction J; intros k j; simpl. auto.
  destruct j; simpl; auto.
+ rewrite H. rewrite get_inst_pad_same. 
  destruct (get_inst_val I m); simpl.
  rewrite v_shift_shift. do 2 f_equal. omega. auto.
Qed.


Fixpoint v_inst_shift_pad Γ v A n k cut I {orig:has_vtype Γ v A}:
  n >= ctx_len Γ ->
  v_inst v (inst_shift (inst_pad_by_n I n) k cut) = v_shift v k cut
with c_inst_shift_pad Γ c C n k cut I {orig:has_ctype Γ c C}:
  n >= ctx_len Γ ->
  c_inst c (inst_shift (inst_pad_by_n I n) k cut) = c_shift c k cut
with h_inst_shift_pad Γ h Σ D n k cut I {orig:has_htype Γ h Σ D}:
  n >= ctx_len Γ ->
  h_inst h (inst_shift (inst_pad_by_n I n) k cut) = h_shift h k cut.
Proof.
+ intros safe. destruct orig. destruct H1; simpl; eauto.
  all: try f_equal; eauto.
  * rewrite get_inst_val_shift_pad_var. auto.
    assert (n0 < ctx_len Γ). 
    { apply ctx_len_get_vtype. exists A. auto. }
    omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H1. simpl in H1. 
    rewrite <-inst_shift_comm in H1. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H1. simpl in H1. 
    rewrite <-inst_shift_comm in H1. eauto. all: simpl; omega.
+ intros safe. destruct orig. destruct H1; simpl; eauto.
  all: try f_equal; eauto.
  * eapply (c_inst_shift_pad _ _ _ (S(S n)) k (S(S cut))) in H2.
    simpl in H2. rewrite <-inst_shift_comm, <-inst_shift_comm in H2.
    rewrite inst_shift_shift in H2. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H2. simpl in H2. 
    rewrite <-inst_shift_comm in H2. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H3. simpl in H3. 
    rewrite <-inst_shift_comm in H3. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S(S n)) k (S(S cut))) in H3.
    simpl in H3. rewrite <-inst_shift_comm, <-inst_shift_comm in H3.
    rewrite inst_shift_shift in H3. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H2. simpl in H2. 
    rewrite <-inst_shift_comm in H2. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S(S n)) k (S(S cut))) in H1.
    simpl in H1. rewrite <-inst_shift_comm, <-inst_shift_comm in H1.
    rewrite inst_shift_shift in H1. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H2. simpl in H2. 
    rewrite <-inst_shift_comm in H2. eauto. all: simpl; omega.
  * eapply (c_inst_shift_pad _ _ _ (S n) k (S cut)) in H5. simpl in H5. 
    rewrite <-inst_shift_comm in H5. eauto. all: simpl; omega.
+ intros safe. destruct orig. destruct H2; simpl; eauto.
  all: try f_equal; eauto.
  eapply (c_inst_shift_pad _ _ _ (S(S n)) k (S(S cut))) in H3.
  simpl in H3. rewrite <-inst_shift_comm, <-inst_shift_comm in H3.
  rewrite inst_shift_shift in H3. eauto. all: simpl; omega.
Qed.


(* Instantiation with sufficient padding changes nothing. *)
Fixpoint v_inst_pad_same Γ v A n I {orig:has_vtype Γ v A}:
  n >= ctx_len Γ ->
  v_inst v (inst_pad_by_n I n) = v
with c_inst_pad_same Γ c C n I {orig:has_ctype Γ c C}:
  n >= ctx_len Γ ->
  c_inst c (inst_pad_by_n I n) = c
with h_inst_pad_same Γ h Σ D n I {orig:has_htype Γ h Σ D}:
  n >= ctx_len Γ ->
  h_inst h (inst_pad_by_n I n) = h.
Proof.
+ intros. eapply (v_inst_shift_pad _ _ _ n 0 0) in orig.
  rewrite inst_shift_0, v_shift_0 in orig. eauto. omega.
+ intros. eapply (c_inst_shift_pad _ _ _ n 0 0) in orig.
  rewrite inst_shift_0, c_shift_0 in orig. eauto. omega.
+ intros. eapply (h_inst_shift_pad _ _ _ _ n 0 0) in orig.
  rewrite inst_shift_0, h_shift_0 in orig. eauto. omega.
Qed.


(* =============== Instantiation and Substitution =============== *)

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
{ rename n0 into dbi.
  destruct (dbi=?n) eqn:dbin; simpl.
  2: destruct (n<=?dbi) eqn:cmp.
  - apply Nat.eqb_eq in dbin. subst. 
    rewrite inst_insert_same. simpl.
    assert (k=?k=true) as same by (apply Nat.eqb_eq; auto). rewrite same.
    rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    all: aomega. rewrite inst_len_shift. omega.
  - apply Nat.eqb_neq in dbin. apply leb_complete in cmp.
    destruct dbi. omega.
    rewrite inst_insert_above. simpl.
    assert (dbi-0=dbi) as same by omega. rewrite same, get_inst_val_shift. 
    destruct (get_inst_val I dbi) eqn:gets; simpl.
    rewrite v_sub_no_var_same, v_negshift_shift, v_shift_0.
    all: aomega.
    apply v_shift_makes_no_var. rewrite inst_len_shift. auto.
  - apply Nat.eqb_neq in dbin. apply leb_complete_conv in cmp.
    rewrite inst_insert_under. simpl.
    rewrite get_inst_val_shift.
    destruct (get_inst_val I dbi) eqn:gets; simpl.
    rewrite v_sub_no_var_same, v_negshift_shift, v_shift_0.
    all: aomega.
    apply v_shift_makes_no_var. rewrite inst_len_shift. auto. }
all: f_equal; simpl in *; try destruct undv; eauto.
all: rewrite inst_shift_insert, inst_shift_comm, v_shift_comm; try omega; simpl.
all: erewrite (c_inst_subs (S k)); simpl.
all: try rewrite inst_len_shift; aomega.
+ do 3 f_equal. do 2 f_equal. omega. rewrite v_shift_inst, v_shift_comm.
  simpl. rewrite InstU_is_insert, v_inst_no_var_same.
  rewrite v_negshift_shift, v_shift_0, v_shift_inst, v_shift_inst. 
  all: aomega. apply v_shift_makes_no_var.
  apply v_under_var_shift; try omega.
  rewrite inst_len_shift, inst_len_shift. auto.
+ apply v_under_var_shift; try omega. auto.
+ do 3 f_equal. do 2 f_equal. omega. rewrite v_shift_inst, v_shift_comm.
  simpl. rewrite InstU_is_insert, v_inst_no_var_same.
  rewrite v_negshift_shift, v_shift_0, v_shift_inst, v_shift_inst. 
  all: aomega. apply v_shift_makes_no_var.
  apply v_under_var_shift; try omega.
  rewrite inst_len_shift, inst_len_shift. auto.
+ apply v_under_var_shift; try omega. auto.
}{
intros safe undv undvs. 
destruct c; unfold v_subs in *; unfold c_subs in *; simpl; auto; f_equal.

all: rewrite v_shift_comm || rewrite c_shift_comm || auto; aomega.
all: try erewrite (v_inst_subs k); auto.
all: clear v_inst_subs h_inst_subs.
all: simpl in *; try destruct undv; try destruct H0; eaomega.

all: assert (forall n, S(S n)=2+n) as ssn by (intros; omega).
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; aomega.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; aomega.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; aomega.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: aomega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; aomega.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; aomega.
  - apply v_under_var_shift; aomega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: aomega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; aomega.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; aomega.
  - apply v_under_var_shift; aomega.
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; aomega.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; aomega.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; aomega.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: aomega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; aomega.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; aomega.
  - apply v_under_var_shift; aomega.
+ rewrite (c_inst_subs (S(S k))). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; aomega.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; aomega.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; aomega.
  - rewrite (ssn (inst_len I)). apply v_under_var_shift. auto. omega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: aomega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; aomega.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; aomega.
  - apply v_under_var_shift; aomega.
+ rewrite (c_inst_subs (S k)). clear c_inst_subs. simpl. do 3 f_equal.
  all: simpl; (try rewrite inst_len_shift); aomega.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite <-inst_shift_comm. all: aomega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_shift_0; aomega.
    * apply v_shift_makes_no_var.
    * apply v_under_var_shift; rewrite inst_len_shift; aomega.
  - apply v_under_var_shift; aomega.
}{
intros safe undv undvs. 
destruct h; unfold h_subs in *; unfold c_subs in *; simpl; auto; f_equal.
all: simpl in *; destruct undv; try rewrite v_shift_comm; simpl.
all: erewrite (c_inst_subs (S(S k))) || erewrite (h_inst_subs k) || auto.
all: simpl; try rewrite inst_len_shift; eaomega.
all: clear c_inst_subs h_inst_subs.
+ do 3 f_equal.
  - do 2 f_equal. rewrite inst_shift_insert. simpl. f_equal.
    rewrite (inst_shift_comm 1). f_equal. all: omega.
  - rewrite v_shift_comm. f_equal. rewrite v_shift_inst.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    rewrite InstU_is_insert, v_inst_no_var_same. all: try omega.
    * rewrite v_negshift_shift, v_negshift_shift, v_shift_0; aomega.
    * rewrite v_negshift_shift. apply v_shift_makes_no_var. omega.
    * rewrite v_negshift_shift. apply v_under_var_shift; simpl. 3: omega.
      all: rewrite inst_len_shift; aomega.
    * rewrite <-(v_shift_shift 1). apply v_shift_makes_no_var.
    * rewrite <-(v_shift_shift 1). apply v_under_var_shift; simpl.
      apply v_under_var_shift; simpl.
      all: rewrite inst_len_shift; aomega.
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
rewrite InstU_is_insert.
all: simpl; aomega.
Qed.


Lemma c_inst_subs2_out c vs1 vs2 I :
  c_under_var c (2+inst_len I) ->
  v_under_var vs1 (inst_len I) -> v_under_var vs2 (inst_len I) ->
    c_inst (c_subs2_out c vs1 vs2) I =
    c_subs (c_subs 
      (c_inst c (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
      0 (v_inst vs2 (inst_shift I 1 0)))
      0 (v_inst vs1 I).
Proof.
intros. unfold c_subs2_out.
rewrite c_inst_subs_out, c_inst_subs_out. simpl.
rewrite inst_shift_shift. f_equal. f_equal.
rewrite InstU_is_insert, v_inst_no_var_same, v_negshift_shift, v_shift_0.
all: simpl; aomega.
+ apply v_shift_makes_no_var.
+ apply v_under_var_shift. rewrite inst_len_shift. auto. omega.
+ rewrite inst_len_shift. auto.
+ apply v_under_var_shift. rewrite inst_len_shift. auto. omega.
+ unfold c_subs_out. apply c_under_var_subs. auto.
  - apply v_under_var_shift. auto. omega.
  - omega.
Qed.


(* =============== Instantiation and Handling Templates =============== *)

Fixpoint get_inst_val_shift_later_strong I n k v {struct v}:
  k <= v ->
    get_inst_val (inst_pad_by_n (inst_shift I n 0) k) v
  = (f_opt (get_inst_val (inst_pad_by_n I k) v)
      (fun v' : val => Some (v_shift v' n 0))).
Proof.
intros safe.
destruct I; simpl.
+ assert (forall k v, k <= v -> 
    get_inst_val (inst_pad_by_n InstØ k) v = None) as gnone.
  { intros k'. induction k'; intros v' safe'; simpl. auto. destruct v'. 
    omega. rewrite get_inst_val_shift. rewrite IHk'. simpl. auto. omega. }
  rewrite gnone. simpl. auto. omega.
+ destruct k; destruct v; simpl; auto.
  - rewrite get_inst_val_shift. auto.
  - omega.
  - rewrite get_inst_val_shift. simpl.
    specialize (get_inst_val_shift_later_strong (InstU I v0) n k v) as IH.
    simpl in IH. rewrite IH.
    rewrite get_inst_val_shift.
    destruct (get_inst_val (inst_pad_by_n (InstU I v0) k) v); simpl.
    rewrite v_shift_shift, v_shift_shift.
    do 2 f_equal. all: aomega.
Qed.


Fixpoint get_inst_val_shift_later I k n v {struct k}:
  k <= v ->
    f_opt (get_inst_val (inst_pad_by_n I k) v)
      (fun v0 : val => Some (v_shift v0 n 0))
  = get_inst_val (inst_pad_by_n (inst_shift I n 0) k) v.
Proof.
intros safe.
destruct k; simpl.
- revert v safe. induction I; intros w safe; simpl; auto.
  destruct w; simpl. auto. rewrite IHI. auto. omega.
- destruct v. omega.
  rewrite get_inst_val_shift, get_inst_val_shift.
  rewrite get_inst_val_shift_later_strong.
  destruct (get_inst_val (inst_pad_by_n I k) v); simpl.
  rewrite v_shift_shift, v_shift_shift. do 2 f_equal. all: aomega.
Qed.


Fixpoint v_inst_shift_move_to_inst k n v I: 
    v_inst (v_shift v n k) (inst_pad_by_n I (k + n))
  = v_inst v (inst_pad_by_n (inst_shift I n 0) k)
with c_inst_shift_move_to_inst k n c I: 
    c_inst (c_shift c n k) (inst_pad_by_n I (k + n))
  = c_inst c (inst_pad_by_n (inst_shift I n 0) k)
with h_inst_shift_move_to_inst k n h I: 
    h_inst (h_shift h n k) (inst_pad_by_n I (k + n))
  = h_inst h (inst_pad_by_n (inst_shift I n 0) k).
Proof.
all: rename v_inst_shift_move_to_inst into vaux.
all: rename c_inst_shift_move_to_inst into caux.
all: rename h_inst_shift_move_to_inst into haux.
{
destruct v; simpl; auto; try f_equal; auto.
+ destruct (k<=?n0) eqn:kn0.
  - simpl.
    assert (forall I k n, 
      inst_pad_by_n I (k + n) = inst_pad_by_n (inst_pad_by_n I n) k).
    { intros J l m. induction l; induction m; simpl; auto.
      do 3 f_equal. omega. do 2 f_equal. rewrite IHl. simpl. auto. }
    assert (k+n=n+k) as knnk by omega. rewrite knnk, H. clear H knnk.
    rewrite get_inst_pad_same.
    rewrite get_inst_val_shift_later. auto. apply leb_complete. auto.
  - apply leb_complete_conv in kn0. rewrite get_inst_pad_var. 
    simpl. rewrite get_inst_pad_var. all: aomega.
+ specialize (caux (S k) n c I). simpl in caux. rewrite caux. auto.
+ specialize (caux (S k) n c I). simpl in caux. rewrite caux. auto.
}{
destruct c; simpl; auto; try f_equal; auto.
+ specialize (caux (2+k) n c I). simpl in caux. 
  rewrite inst_shift_shift, inst_shift_shift in caux. simpl in caux. 
  rewrite caux. auto.
+ specialize (caux (S k) n c1 I). simpl in caux. rewrite caux. auto.
+ specialize (caux (S k) n c2 I). simpl in caux. rewrite caux. auto.
+ specialize (caux (2+k) n c2 I). simpl in caux. 
  rewrite inst_shift_shift, inst_shift_shift in caux. simpl in caux. 
  rewrite caux. auto.
+ specialize (caux (S k) n c I). simpl in caux. rewrite caux. auto.
+ specialize (caux (2+k) n c2 I). simpl in caux. 
  rewrite inst_shift_shift, inst_shift_shift in caux. simpl in caux. 
  rewrite caux. auto.
+ specialize (caux (S k) n c3 I). simpl in caux. rewrite caux. auto.
+ specialize (caux (S k) n c2 I). simpl in caux. rewrite caux. auto.
}{
destruct h; simpl; auto; try f_equal; auto.
specialize (caux (2+k) n c I). simpl in caux. 
rewrite inst_shift_shift, inst_shift_shift in caux. simpl in caux. 
rewrite caux. auto.
}
Qed.


Fixpoint form_inst_shift_move_to_inst k n φ I {struct φ}:
    form_inst (form_shift φ n k) (inst_pad_by_n I (k + n))
  = form_inst φ (inst_pad_by_n (inst_shift I n 0) k).
Proof.
destruct φ; simpl; f_equal.
all: rewrite v_inst_shift_move_to_inst || rewrite c_inst_shift_move_to_inst 
  || rewrite h_inst_shift_move_to_inst || auto.
all: auto.
all: assert (InstU (inst_shift (inst_pad_by_n I (k + n)) 1 0) (Var 0)
  = inst_pad_by_n I (1+k+n)) as same by (simpl; auto).
all: rewrite same, form_inst_shift_move_to_inst; auto.
Qed.


Lemma hyp_inst_shift_move_to_inst k n Ψ I :
    hyp_inst (hyp_shift Ψ n k) (inst_pad_by_n I (k + n))
  = hyp_inst Ψ (inst_pad_by_n (inst_shift I n 0) k).
Proof.
induction Ψ; simpl; f_equal; auto. apply form_inst_shift_move_to_inst.
Qed.



Fixpoint form_inst_subs k φ vs n I {struct φ}:
  n <= inst_len I -> 
  form_under_var φ (1+inst_len I) -> v_under_var vs (inst_len I) ->
    form_inst (form_subs φ n vs) I =
    form_subs (form_inst φ (inst_insert (inst_shift I 1 k) n (Var k)))
      k (v_inst vs I).
Proof.
intros safe un1 un2.
destruct φ; simpl; f_equal; auto; simpl in un1; try destruct un1.
all: erewrite v_inst_subs || erewrite c_inst_subs || erewrite h_inst_subs
  || erewrite form_inst_subs || auto; simpl; aomega.
all: try rewrite inst_len_shift; aomega.
all: f_equal || apply v_under_var_shift; aomega.
+ do 2 f_equal. rewrite inst_shift_insert, <-inst_shift_comm.
  simpl. f_equal. all: omega.
+  assert (InstU (inst_shift I 1 0) (Var 0) = inst_pad_by_n I 1) 
    as same by (simpl; auto).
  rewrite v_shift_inst, same, v_inst_shift_move_to_inst. simpl. auto.
+ do 2 f_equal. rewrite inst_shift_insert, <-inst_shift_comm.
  simpl. f_equal. all: omega.
+  assert (InstU (inst_shift I 1 0) (Var 0) = inst_pad_by_n I 1) 
    as same by (simpl; auto).
  rewrite v_shift_inst, same, v_inst_shift_move_to_inst. simpl. auto.
Qed.


Fixpoint inst_handle_t Γ Z I h T Σ D {struct T}:
  wf_t Γ Z T Σ -> h_under_var h (inst_len I) ->
    (c_inst (handle_t D (ctx_len Γ) (tctx_len Z) h T)
      (inst_pad_by_n I (tctx_len Z + ctx_len Γ))) 
  = (handle_t D (ctx_len Γ) (tctx_len Z) (h_inst h I) T).
Proof.
intros wft under. destruct T; simpl; inv wft.
all: assert (forall x y, x+(S y) = S (x+y)) as comm by (intros; omega).
+ rewrite get_inst_pad_var.
  erewrite v_inst_pad_same; eauto. omega.
  assert (tctx_len Z > n).
  apply tctx_len_get_ttype. exists A. auto. omega.
+ erewrite v_inst_pad_same; auto. exact H2. omega.
+ erewrite v_inst_pad_same; eauto.
  eapply inst_handle_t in H5. simpl in H5. rewrite <-H5.
  rewrite comm, comm. simpl. rewrite inst_shift_shift. all: aomega.
+ erewrite v_inst_pad_same; eauto.
  eapply inst_handle_t in H6. simpl in H6. rewrite <-H6.
  eapply inst_handle_t in H7. simpl in H7. rewrite <-H7.
  rewrite comm. simpl. all: aomega.
+ erewrite v_inst_pad_same; eauto.
  eapply inst_handle_t in H6. simpl in H6. rewrite <-H6.
  eapply inst_handle_t in H7. simpl in H7. rewrite <-H7.
  rewrite comm, comm. simpl. rewrite inst_shift_shift. all: aomega.
+ erewrite c_inst_pad_same; eauto.
  eapply inst_handle_t in H5. simpl in H5. rewrite <-H5.
  rewrite comm. simpl. all: aomega.
+ destruct (get_case h o) eqn: finds.
  - eapply inst_get_case_Some in finds as findss; eauto. rewrite findss.
    rewrite c_inst_subs2_out. unfold c_subs2_out. unfold c_subs_out. simpl.
    f_equal. f_equal.
    * rewrite c_shift_inst. simpl.
      assert (InstU
      (InstU (inst_shift (inst_pad_by_n I (tctx_len Z + ctx_len Γ)) 2 0)
         (Var 1)) (Var 0) =
         (inst_pad_by_n I (2+(tctx_len Z + ctx_len Γ)))).
      simpl. rewrite inst_shift_shift. auto. rewrite H.
      assert (InstU
      (InstU (inst_shift (inst_shift I 2 0) (ctx_len Γ + tctx_len Z) 2)
         (Var 1)) (Var 0) =
         (inst_pad_by_n (inst_shift I (ctx_len Γ+tctx_len Z) 0) 2)).
      simpl. rewrite inst_shift_shift. rewrite (inst_shift_comm _ _ 0).
      auto. omega. rewrite H0.
      rewrite <-c_inst_shift_move_to_inst. do 2 f_equal. omega.
    * f_equal. eapply inst_handle_t in H13. simpl in H13. rewrite <-H13.
      rewrite c_shift_inst. f_equal. rewrite comm, inst_shift_comm. simpl.
      all: aomega.
    * eapply v_inst_pad_same; eauto. omega.
    * rewrite inst_len_pad_by_n. simpl.
      assert (S (S (inst_len I + (tctx_len Z + ctx_len Γ))) 
        = (ctx_len Γ + tctx_len Z) + (S (S (inst_len I)))) by omega.
      rewrite H. apply c_under_var_shift. 
      eapply get_case_under_var; eauto. omega.
    * simpl. eapply handle_t_under_var in under as under'; eauto.
      simpl in under'. rewrite inst_len_pad_by_n. simpl.
      assert (forall x y z, x+(y+z)=x+y+z) as assoc by (intros; omega).
      rewrite comm, <-assoc in under'. apply has_vtype_is_under_ctx in H12.
      eapply v_under_var_weaken; eauto. omega.
    * rewrite inst_len_pad_by_n. simpl. eapply handle_t_under_var in H13; eauto.
      simpl in H13. simpl. rewrite comm in H13. auto.
      assert (forall x y z, x+(y+z)=x+y+z) as same by (intros; omega).
      rewrite same. exact H13.
  - eapply inst_get_case_None in finds as findss. rewrite findss. simpl.
    f_equal. erewrite v_inst_pad_same; eauto. omega.
    eapply inst_handle_t in H13; eauto. simpl in H13. rewrite comm in H13.
    simpl in H13. rewrite H13. auto.
(* Some issue with eauto magic *)
Unshelve. exact D.
Qed.


(* =============== Instantiation and OOTB =============== *)

Fixpoint smush_insts I I' :=
  match I' with
  | InstØ => InstØ
  | InstU i v => InstU (smush_insts I i) (v_inst v I)
  end.


Fixpoint smush_get I I' n {struct I'}:
    get_inst_val (smush_insts I I') n
  = f_opt (get_inst_val I' n) (fun v' => Some (v_inst v' I)).
Proof.
destruct I'; simpl. auto.
destruct n; simpl. auto. rewrite smush_get. auto.
Qed.


Fixpoint shift_smush n I I' Γ Γ' Γ'' {struct I'}:
  wf_inst Γ I Γ' -> wf_inst Γ' I' Γ'' ->
    inst_shift (smush_insts I I') n 0 
  = smush_insts (inst_pad_by_n I n) (inst_shift I' n 0).
Proof.
intros wfI wfI'. destruct I'; simpl. auto. f_equal. 
+ destruct Γ''; inv wfI'. eauto. 
+ rewrite v_shift_inst. rewrite v_inst_shift_move_to_inst. simpl. f_equal.
Qed.


Fixpoint v_smush_is_sequencing I I' v Γ Γ' Γ'' A (orig: has_vtype Γ'' v A)
  {struct orig}: wf_inst Γ I Γ' -> wf_inst Γ' I' Γ'' -> 
  v_inst v (smush_insts I I') = v_inst (v_inst v I') I

with c_smush_is_sequencing I I' c Γ Γ' Γ'' C (orig: has_ctype Γ'' c C)
  {struct orig}: wf_inst Γ I Γ' -> wf_inst Γ' I' Γ'' -> 
  c_inst c (smush_insts I I') = c_inst (c_inst c I') I

with h_smush_is_sequencing I I' h Γ Γ' Γ'' Σ D (orig:has_htype Γ'' h Σ D)
  {struct orig}: wf_inst Γ I Γ' -> wf_inst Γ' I' Γ'' ->
  h_inst h (smush_insts I I') = h_inst (h_inst h I') I.
  
Proof.
{
intros wfI wfI'. destruct orig. destruct H1; simpl; eauto.
all: try f_equal; eauto.
+ rewrite smush_get. destruct (get_inst_val I' n); simpl; eauto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H0; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H0; inv H6; auto.
}{
intros wfI wfI'. destruct orig. destruct H1; simpl; eauto.
all: try f_equal; eauto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wffI as wfffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  eapply wf_inst_InstU in wffI' as wfffI'.
  simpl in *. rewrite inst_shift_shift in wfffI. 
  rewrite inst_shift_shift in wfffI'. simpl in *.
  erewrite shift_smush; eauto. erewrite <-c_smush_is_sequencing; eauto; simpl.
  rewrite inst_shift_shift; eauto.
  all: inv H1; inv H4; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H1; inv H5; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H1; inv H5; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wffI as wfffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  eapply wf_inst_InstU in wffI' as wfffI'.
  simpl in *. rewrite inst_shift_shift in wfffI. 
  rewrite inst_shift_shift in wfffI'. simpl in *.
  erewrite shift_smush; eauto. erewrite <-c_smush_is_sequencing; eauto; simpl.
  rewrite inst_shift_shift; eauto.
  all: inv H1; auto; inv H5; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H1; inv H4; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wffI as wfffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  eapply wf_inst_InstU in wffI' as wfffI'.
  simpl in *. rewrite inst_shift_shift in wfffI. 
  rewrite inst_shift_shift in wfffI'. simpl in *.
  erewrite shift_smush; eauto. erewrite <-c_smush_is_sequencing; eauto; simpl.
  rewrite inst_shift_shift; eauto.
  all: inv H1; inv H3; auto; inv H8; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H1; inv H3; auto.
+ eapply wf_inst_InstU in wfI as wffI.
  eapply wf_inst_InstU in wfI' as wffI'.
  erewrite shift_smush, <-c_smush_is_sequencing; eauto.
  all: inv H5; inv H6; auto.
}{
intros wfI wfI'. destruct orig. destruct H2; simpl; eauto.
all: try f_equal; eauto.
eapply wf_inst_InstU in wfI as wffI.
eapply wf_inst_InstU in wffI as wfffI.
eapply wf_inst_InstU in wfI' as wffI'.
eapply wf_inst_InstU in wffI' as wfffI'.
simpl in *. rewrite inst_shift_shift in wfffI. 
rewrite inst_shift_shift in wfffI'. simpl in *.
erewrite shift_smush; eauto. erewrite <-c_smush_is_sequencing; eauto; simpl.
rewrite inst_shift_shift; eauto.
all: inv H3; inv H4; auto; inv H8; auto.
}
Qed.


(* =============== Safety =============== *)

Fixpoint v_wf_inst_typesafe Γ I Γ' v A (orig:has_vtype Γ' v A)  {struct orig}:
  wf_inst Γ I Γ' ->
  has_vtype Γ (v_inst v I) A

with c_wf_inst_typesafe Γ I Γ' c C (orig:has_ctype Γ' c C)  {struct orig}:
  wf_inst Γ I Γ' ->
  has_ctype Γ (c_inst c I) C

with h_wf_inst_typesafe Γ I Γ' h Σ D (orig:has_htype Γ' h Σ D)  {struct orig}:
  wf_inst Γ I Γ' ->
  has_htype Γ (h_inst h I) Σ D

with respect_wf_inst_typesafe Γ I Γ' h Σ D E (orig:respects Γ' h Σ D E) 
  {struct orig}: wf_inst Γ I Γ' ->
  respects Γ (h_inst h I) Σ D E

with judg_wf_inst_typesafe Γ I Γ' Ψ φ (orig: judg Γ' Ψ φ) {struct orig}:
  wf_inst Γ I Γ' ->
  judg Γ (hyp_inst Ψ I) (form_inst φ I)

with wf_hyp_wf_inst_typesafe Γ I Γ' Ψ (orig: wf_hyp Γ' Ψ) {struct orig} :
  wf_inst Γ I Γ' ->
  wf_hyp Γ (hyp_inst Ψ I)

with wf_form_wf_inst_typesafe Γ I Γ' φ (orig: wf_form Γ' φ) {struct orig} :
  wf_inst Γ I Γ' ->
  wf_form Γ (form_inst φ I)

with smush_insts_wfsafe Γ I Γ' I' Γ'' (orig:wf_inst Γ' I' Γ'') {struct orig}:
  wf_inst Γ I Γ' -> wf_inst Γ (smush_insts I I') Γ''.

Proof.
all: rename v_wf_inst_typesafe into VL.
all: rename c_wf_inst_typesafe into CL.
all: rename h_wf_inst_typesafe into HL.
all: rename respect_wf_inst_typesafe into RL.
all: rename judg_wf_inst_typesafe into JL.
all: rename wf_hyp_wf_inst_typesafe into WFHL.
all: rename wf_form_wf_inst_typesafe into WFFL.
all: rename smush_insts_wfsafe into WS.
all: intro wfinst; assert (wf_ctx Γ) by (inv wfinst; auto; inv H; auto).
{
destruct orig. destruct H2; simpl.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeUnit.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeInt.
+ clear VL CL HL RL JL WFHL WFFL WS.
  eapply wf_inst_get_Some in H2 as gets; eauto. 
  destruct gets as [v''[gets tys]]. rewrite gets. auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypePair; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeLeft; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeRight; auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeNil; auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeCons; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply CL in H2; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeFun; eauto.
  inv H1. auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply HL in H3 as tysh; eauto.
  eapply RL in H4; eauto.
  eapply CL in H2; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. apply TypeHandler; auto.
  inv H1. inv H7. auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeV; auto. eapply TypeVSubsume; eauto.
}{
destruct orig. destruct H2; simpl.
+ eapply VL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. apply TypeRet; auto.
+ eapply VL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. apply TypeAbsurd; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl in H3. rewrite inst_shift_shift in H3.
  apply TypeC; auto. eapply TypeProdMatch; eauto.
  all: inv H2; inv H5; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc1.
  eapply wf_inst_InstU in wfinst as wfinsc2.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeSumMatch; eauto.
  all: inv H2; inv H6; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl in H4. rewrite inst_shift_shift in H4.
  apply TypeC; auto. eapply TypeListMatch; eauto.
  all: inv H2; auto; inv H6; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply CL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeDo; eauto.
  inv H2. inv H5. auto.
+ eapply VL in H2; eauto.
  eapply VL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeApp; eauto.
+ eapply VL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeHandle; eauto.
+ eapply wf_inst_InstU in wfinst as wfinsc1.
  eapply wf_inst_InstU in wfinsc1 as wfinsc1.
  eapply wf_inst_InstU in wfinst as wfinsc2.
  eapply CL in H2; eauto.
  eapply CL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl in H2. rewrite inst_shift_shift in H2.
  apply TypeC; auto. eapply TypeLetRec; eauto.
  all: inv H2; inv H4; auto; inv H9; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc1.
  eapply VL in H5; eauto.
  eapply CL in H6; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeOp; eauto.
  all: auto. inv H6. inv H7. auto.
+ eapply CL in H2; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeC; auto. eapply TypeCSubsume; eauto.
}{
destruct orig. destruct H3; simpl.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply TypeH; auto. apply TypeCasesØ; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply HL in H3; eauto.
  eapply CL in H4; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl in H4. rewrite inst_shift_shift in H4.
  apply TypeH; auto. eapply TypeCasesU; eauto.
  all: inv H4; inv H5; auto. inv H9. auto.
}{
destruct orig. destruct H5; simpl.
+ eapply HL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply Respects; auto. apply RespectEqsØ.
+ eapply RL in H5; eauto.
  eapply JL in H6 as ce.
  eapply HL in H4 as tyss; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  2: instantiate (2:= (join_ctxs (join_ctxs Γ (tctx_to_ctx Z D)) Γ0)).
  2: instantiate (1:= (inst_pad_by_n I (tctx_len Z + ctx_len Γ0))).
  apply wf_inst_ctx_len_same in wfinst as same_len.
  apply Respects; auto. apply RespectEqsU; eauto.
  inv H3. erewrite <-inst_handle_t; eauto. erewrite <-inst_handle_t; eauto.
  all: try (rewrite same_len; eapply has_htype_is_under_ctx; eauto).
  apply wf_inst_pad_for_handle_t; eauto. all: inv H3; auto.
}{
destruct orig. apply WfJudg; eauto. destruct H3.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply VeqSym. auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply VeqTrans; eauto.
+ eapply WFHL in H2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply wf_inst_get_Some in H3; eauto.
  destruct H3 as [v'[gets tys]].
  simpl. rewrite gets. eapply (veq_refl _ (hyp_inst Ψ I)) in tys.
  inv tys. all: auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply VeqUnit.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply VeqInt; auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply VeqPair; auto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply VeqLeft; eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply VeqRight; eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  eapply VeqNil; eauto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply VeqCons; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply JL in H3; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply VeqFun; auto. simpl in H3.
  specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad. simpl in pad.
  rewrite hyp_shift_inst, <-pad. auto.
  inv H1. inv H7. inv H4. auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  eapply RL in H5; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply VeqHandler; eauto.
  specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad. simpl in pad.
  rewrite hyp_shift_inst, <-pad. auto.
  inv H1. inv H9. inv H6. inv H10. auto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply VeqSubsume; eauto.
+ all: clear VL CL HL RL JL WFHL WFFL WS.
  apply ηUnit.
+ eapply WFHL in H2 as wfhy; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. rewrite InstU_is_insert.
  rewrite v_inst_no_var_same, v_negshift_shift, v_shift_0. 
  rewrite <-v_shift_inst. apply ηFun.
  all: aomega.
  apply v_shift_makes_no_var.
  apply v_under_var_shift. erewrite inst_len_shift, wf_inst_ctx_len_same.
  eapply has_vtype_is_under_ctx. all: omega || eauto.
  inv H1. eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply CeqSym. auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply CeqTrans; eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply CeqRet; auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply CeqAbsurd; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqProdMatch; eauto.
  specialize (hyp_inst_shift_move_to_inst 0 2 Ψ I) as pad. simpl in pad.
  rewrite hyp_shift_inst, <-pad, <-(inst_shift_shift 1 1). auto.
  all: inv H4; inv H5; inv H10; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc1.
  eapply wf_inst_InstU in wfinst as wfinsc2.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  eapply JL in H5; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqSumMatch; eauto.
  all: specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad; simpl in pad.
  - rewrite hyp_shift_inst, <-pad. auto.
  - rewrite hyp_shift_inst, <-pad. auto.
  - inv H4; inv H6. auto.
  - inv H5; inv H6. auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  eapply JL in H5; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqListMatch; eauto.
  specialize (hyp_inst_shift_move_to_inst 0 2 Ψ I) as pad. simpl in pad.
  rewrite hyp_shift_inst, <-pad, <-(inst_shift_shift 1 1). auto.
  all: inv H5; inv H6; inv H11; auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqDo; eauto.
  specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad; simpl in pad.
  rewrite hyp_shift_inst, <-pad. auto.
  inv H4. inv H5. auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply CeqApp; eauto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply CeqHandle; eauto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply wf_inst_InstU in wfinst as wfinscf.
  eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqLetRec; eauto.
  - specialize (hyp_inst_shift_move_to_inst 0 2 Ψ I) as pad. simpl in pad.
    rewrite hyp_shift_inst, <-pad, <-(inst_shift_shift 1 1). eauto.
  - specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad; simpl in pad.
    rewrite hyp_shift_inst, <-pad. auto.
  - inv H4. inv H5. auto.
  - inv H3. inv H5. auto.
  - inv H4. inv H5. inv H11. auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply JL in H4; eauto.
  eapply JL in H5; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply CeqOp; eauto.
  specialize (hyp_inst_shift_move_to_inst 0 1 Ψ I) as pad; simpl in pad.
  rewrite hyp_shift_inst, <-pad. all: auto.
  inv H5. inv H6. auto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply CeqSubsume; eauto.
+ specialize (WS _ _ _ _ _ H4 wfinst) as smush.
  clear VL CL HL RL JL WFHL WFFL WS.
  assert (wf_eqs E Σ) as wfe. {inv H1. inv H10. inv H5. auto. }
  eapply has_eq_wf_parts in H3 as parts; eauto.
  destruct parts as [wfg0[wfz[wft1 wft2]]].
  eapply OOTB; eauto; subst.
  all: erewrite c_smush_is_sequencing; eauto.
  all: apply tmpl_to_comp_has_ctype; eauto; inv H1; auto.
  all: inv H8; auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. simpl. apply shape_prodmatch in H6 as parts. 
  destruct parts as [A[B[tyv tyc]]].
  specialize (βMatchPair (v_inst v1 I) (v_inst v2 I)
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
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_summatch in H6 as parts. 
  destruct parts as [A'[B'[tyv[tyc1 tyc2]]]].
  simpl in *. 
  specialize (βMatchLeft (v_inst v I)
    (c_inst c1 (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out.
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc1. auto.
  - eapply shape_left in tyv. 2: eauto. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_summatch in H6 as parts. 
  destruct parts as [A'[B'[tyv[tyc1 tyc2]]]].
  simpl in *. 
  specialize (βMatchRight (v_inst v I)
    (c_inst c1 (InstU (inst_shift I 1 0) (Var 0)))
    (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out.
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc2. auto.
  - eapply shape_right in tyv. 2: eauto. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_listmatch in H6 as parts. 
  destruct parts as [A'[tyv[tyc1 tyc2]]].
  simpl in *. 
  specialize (βMatchNil (c_inst c1 I) ) as rule.
  apply rule.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_listmatch in H6 as parts. 
  destruct parts as [A[tyv[tyc1 tyc2]]].
  simpl in *. 
  specialize (βMatchCons (v_inst v I) (v_inst vs I)
    (c_inst c1 I)
    (c_inst c2 (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    ) as rule.
  unfold c_subs2_out in rule. unfold c_subs_out in rule.
  rewrite c_inst_subs2_out. rewrite v_shift_inst in rule. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc2. auto.
  - apply shape_cons in tyv. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
  - apply shape_cons in tyv. destruct tyv.
    eapply has_vtype_is_under_ctx. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_app in H6 as parts.
  destruct parts as [tyc tyv].
  simpl in *. 
  specialize (βApp 
    (c_inst c (InstU (inst_shift I 1 0) (Var 0))) (v_inst v I)
    A C) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. auto.
  - eapply has_vtype_is_under_ctx. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. eapply shape_letrec_full in H6 as parts. 2: reflexivity.
  destruct parts as [tyc1 tyc2].
  simpl in *. 
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
  all: simpl; aomega.
  all: clear rule; try clear same.
  - apply c_shift_makes_no_var.
  - rewrite inst_len_shift, inst_len_shift, same_len. apply c_under_var_shift.
    eapply has_ctype_is_under_ctx in tyc1. auto. omega.
  - eapply has_ctype_is_under_ctx in tyc2. rewrite same_len. auto.
  - rewrite same_len. eapply has_ctype_is_under_ctx in tyc1. aconstructor.
    eapply c_under_var_shift. auto. omega.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  destruct C as [A Σ E].
  inv H1. apply shape_do in H6 as parts.
  destruct parts as [A'[tyret tyc]].
  simpl in *. 
  specialize (βDoRet (v_inst v I)
    (c_inst c (InstU (inst_shift I 1 0) (Var 0)))
    ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len.
  - apply has_ctype_is_under_ctx in tyc. auto.
  - eapply has_vtype_is_under_ctx. apply shape_ret in tyret. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  destruct C as [Ac Σ E].
  inv H1. apply shape_do in H6 as parts.
  destruct parts as [A'[tyc1 tyc2]].
  simpl in *. 
  specialize (βDoOp op A B (v_inst v I)
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
  all: simpl; aomega.
  - apply c_shift_makes_no_var.
  - rewrite inst_len_shift, inst_len_shift, same_len.
    apply c_under_var_shift. apply has_ctype_is_under_ctx in tyc2.
    auto. omega.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_handle in H6 as parts.
  destruct parts as [C'[tyh tyc]].
  simpl in *. 
  specialize (βHandleRet (c_inst c_r (InstU (inst_shift I 1 0) (Var 0)))
  (h_inst h I) (v_inst v I)
  ) as rule.
  unfold c_subs_out in rule. rewrite c_inst_subs_out. 
  apply rule. all: try clear rule; try rewrite same_len; destruct C'.
  - apply shape_handler in tyh. destruct tyh as [Σ[D[tycr _]]].
    apply has_ctype_is_under_ctx in tycr. auto.
  - eapply has_vtype_is_under_ctx. apply shape_ret in tyc. eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  eapply inst_get_case_Some in H3 as finds. 2: reflexivity.
  inv H1. apply shape_handle in H7 as parts.
  destruct parts as [C'[tyh tyc]].
  simpl in *.
  specialize (βHandleOp A
    (c_inst c_r (InstU (inst_shift I 1 0) (Var 0)))
    (h_inst h I) op Aop Bop (v_inst v I)
    (c_inst c_k (InstU (inst_shift I 1 0) (Var 0)))
    (c_inst c_op (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
    C Γ (hyp_inst Ψ I) finds
    ) as rule.
  simpl in *.
  unfold c_subs2_out in rule. unfold c_subs_out in rule.
  rewrite c_inst_subs2_out. rewrite c_shift_inst in rule. simpl in *.
  assert (forall I',
    InstU (InstU I' (Var 1)) (Var 0) =
    inst_insert (InstU I' (Var 0)) 1 (Var 1)) as insert1.
  { intros. simpl. destruct I'; auto. }
  assert (forall I',
    (InstU I' (Var 0)) =
    inst_insert I' 0 (Var 0)) as insert0.
  { intros. simpl. destruct I'; auto. }
  rewrite (insert1 (inst_shift (inst_shift (inst_shift I 1 0) 1 0) 1 0)).
  rewrite c_inst_no_var_same.
  rewrite (insert0 (inst_shift (inst_shift I 1 0) 1 0)).
  rewrite h_inst_no_var_same, <-insert0. clear insert1 insert0.
  rewrite c_shift_inst, h_shift_inst in rule. simpl in rule.
  rewrite c_shift_inst, h_shift_inst in rule. simpl in rule.
  rewrite c_negshift_shift, c_shift_0, h_negshift_shift, h_shift_0. simpl.
  assert (
      (inst_shift (inst_shift (inst_shift I 1 0) 1 0) 1 0)
    = (inst_shift (inst_shift (inst_shift I 1 0) 1 1) 1 2)
    ) as sameshift3.
  { rewrite (inst_shift_comm 1 0 0 1 I), (inst_shift_comm). f_equal.
    rewrite inst_shift_comm. all: aomega. }
  assert (
      (inst_shift (inst_shift I 1 0) 1 0) = (inst_shift (inst_shift I 1 0) 1 1)
    ) as sameshift2.
  { rewrite inst_shift_comm. all: aomega. }
  rewrite sameshift3, sameshift2.
  apply rule.
  all: simpl; aomega; try clear rule.
  all: try rewrite inst_len_shift; try rewrite inst_len_shift.
  all: try rewrite same_len.
  all: destruct C' as [Ac Σ E]; apply shape_handler in tyh;
       destruct tyh as [Σ'[D'[tycr[tyh[res[asty[sty csty]]]]]]].
  all: eapply shape_op_full in tyc; eauto.
  all: destruct tyc as [tyv[tyck[A'[B'[gets[stya styb]]]]]].
  7: constructor. 7: constructor.
  - apply h_shift_makes_no_var.
  - apply h_under_var_shift. eapply has_htype_is_under_ctx. eauto. omega.
  - apply c_shift_makes_no_var.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in tycr. 
    rewrite inst_len_shift, same_len. auto. omega.
  - simpl in H9. eapply sig_subtype_get_Some in sty; eauto.
    destruct sty as [A''[B''[g _]]].
    eapply case_has_type in H3; eauto.
    eapply has_ctype_is_under_ctx in H3. auto. 
  - apply has_vtype_is_under_ctx in tyv. auto.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in tycr. auto. omega.
  - apply h_under_var_shift. eapply has_htype_is_under_ctx. eauto. omega.
  - apply has_ctype_is_under_ctx in tyck. auto.
+ eapply CL in H4 as tys3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_absurd in H10 as vtys.
  simpl in *.
  erewrite (c_inst_subs 0).
  apply ηEmpty. all: aomega.
  all: try rewrite inst_len_shift; try rewrite same_len. exact tys3.
  - apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. auto. omega.
  - apply has_vtype_is_under_ctx in vtys. auto.
  - assert (ctx_insert Γ 0 TyEmpty = CtxU Γ TyEmpty) as same.
    { destruct Γ; simpl; auto. }
    rewrite same. apply wf_inst_insert. 
    apply WfTyEmpty. auto.
+ eapply CL in H4 as tys3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_prodmatch in H10 as parts.
  destruct parts as [A'[B'[tyv tyc]]].
  simpl in *.
  erewrite (c_inst_subs 0), (c_inst_subs 2).
  specialize (ηPair Γ (hyp_inst Ψ I) (v_inst v I) 0
    (c_inst c (inst_insert (inst_shift I 1 0) n (Var 0))) C A B
  ) as rule.
  rewrite c_shift_inst, inst_shift_insert in rule. simpl in *.
  assert (c_inst (c_shift c 2 0)
    (InstU (InstU (inst_insert (inst_shift (inst_shift I 2 0) 1 2) (n - 0)
      (Var 2)) (Var 1)) (Var 0))
    = c_inst c (inst_insert (inst_shift (inst_shift I 1 0) 2 0) n (Var 2))).
  { rewrite <-(c_shift_shift 1), InstU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0, InstU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0. do 2 f_equal.
    rewrite (inst_shift_comm 1). all: aomega.
    + apply c_shift_makes_no_var.
    + apply c_under_var_shift; omega || simpl.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.
      apply has_ctype_is_under_ctx in H4.
      rewrite ctx_len_insert in H4. simpl in H4. auto. omega.
      rewrite inst_len_shift, inst_len_shift. omega.
    + apply c_shift_makes_no_var.
    + simpl. apply c_under_var_shift. apply c_under_var_shift.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.
      apply has_ctype_is_under_ctx in H4.
      rewrite ctx_len_insert in H4. simpl in H4. auto. 
      all: try omega. rewrite inst_len_shift, inst_len_shift, same_len. omega.
  }
  rewrite H1. eapply rule. omega.
  all: try clear rule; simpl; aomega.
  all: try rewrite inst_len_shift; try rewrite same_len. exact tys3. omega.
  - assert (S (S (S (ctx_len Γ0))) = 2+S (ctx_len Γ0)) as same by omega.
    rewrite same. apply c_under_var_shift.
    apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. all: omega.
  - apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. omega.
  - apply has_vtype_is_under_ctx in tyv. auto.
  - assert (ctx_insert Γ 0 (TyProd A B) = CtxU Γ (TyProd A B)) as same.
    { destruct Γ; simpl; auto. }
    rewrite same. apply wf_inst_insert. 
    inv H4. apply wf_ctx_insert_vtype in H5. all: aomega.
+ eapply CL in H4 as tys3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_summatch in H10 as parts.
  destruct parts as [A'[B'[tyv[tyc1 tyc2]]]].
  simpl in *.
  erewrite (c_inst_subs 0), (c_inst_subs 1), (c_inst_subs 1).
  specialize (ηSum Γ (hyp_inst Ψ I) (v_inst v I) 0
    (c_inst c (inst_insert (inst_shift I 1 0) n (Var 0))) C A B
  ) as rule.
  rewrite c_shift_inst, inst_shift_insert in rule. simpl in *.
  assert (c_inst (c_shift c 1 0) (InstU
     (inst_insert (inst_shift (inst_shift I 1 0) 1 1) (n - 0) (Var 1)) (Var 0))
    = (c_inst c (inst_insert (inst_shift (inst_shift I 1 0) 1 0) n (Var 1)))).
  { rewrite InstU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0. do 2 f_equal.
    rewrite <-(inst_shift_comm). all: aomega.
    + apply c_shift_makes_no_var.
    + simpl. apply c_under_var_shift.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.
      apply has_ctype_is_under_ctx in H4.
      rewrite ctx_len_insert in H4. simpl in H4. auto. 
      all: try omega. rewrite inst_len_shift, inst_len_shift, same_len. omega.
  }
  rewrite H1. eapply rule. omega. exact tys3.
  all: try clear rule; simpl; aomega.
  all: try rewrite inst_len_shift; try rewrite same_len; aomega.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. all: omega.
  - apply c_under_var_shift. apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. all: omega.
  - apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. all: omega.
  - apply has_vtype_is_under_ctx in tyv. auto.
  - assert (ctx_insert Γ 0 (TySum A B) = CtxU Γ (TySum A B)) as same.
    { destruct Γ; simpl; auto. }
    rewrite same. apply wf_inst_insert. 
    inv H4. apply wf_ctx_insert_vtype in H5. all: aomega.
+ eapply CL in H4 as tys3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  inv H1. apply shape_listmatch in H10 as parts.
  destruct parts as [A'[tyv[tyc1 tyc2]]].
  simpl in *.
  erewrite (c_inst_subs 0), (c_inst_subs 0), (c_inst_subs 2).
  specialize (ηList Γ (hyp_inst Ψ I) (v_inst v I) 0
    (c_inst c (inst_insert (inst_shift I 1 0) n (Var 0))) C A
  ) as rule.
  rewrite c_shift_inst, inst_shift_insert in rule. simpl in *.
  assert (c_inst (c_shift c 2 0)
    (InstU (InstU (inst_insert (inst_shift (inst_shift I 2 0) 1 2) (n - 0)
      (Var 2)) (Var 1)) (Var 0))
    = c_inst c (inst_insert (inst_shift (inst_shift I 1 0) 2 0) n (Var 2))).
  { rewrite <-(c_shift_shift 1), InstU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0, InstU_is_insert, c_inst_no_var_same.
    rewrite c_negshift_shift, c_shift_0. do 2 f_equal.
    rewrite (inst_shift_comm 1). all: aomega.
    + apply c_shift_makes_no_var.
    + apply c_under_var_shift; omega || simpl.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.
      apply has_ctype_is_under_ctx in H4.
      rewrite ctx_len_insert in H4. simpl in H4. auto. omega.
      rewrite inst_len_shift, inst_len_shift. omega.
    + apply c_shift_makes_no_var.
    + simpl. apply c_under_var_shift. apply c_under_var_shift.
      rewrite inst_len_insert, inst_len_shift, inst_len_shift, same_len.
      apply has_ctype_is_under_ctx in H4.
      rewrite ctx_len_insert in H4. simpl in H4. auto. 
      all: try omega. rewrite inst_len_shift, inst_len_shift, same_len. omega.
  }
  rewrite H1. eapply rule. omega. exact tys3.
  all: try clear rule; simpl; aomega.
  all: try rewrite inst_len_shift; try rewrite same_len. omega.
  - assert (S (S (S (ctx_len Γ0))) = 2+S (ctx_len Γ0)) as same by omega.
    rewrite same. apply c_under_var_shift.
    apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. all: omega.
  - apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. omega.
  - apply has_ctype_is_under_ctx in H4.
    rewrite ctx_len_insert in H4. simpl in H4. auto. omega.
  - apply has_vtype_is_under_ctx in tyv. auto.
  - assert (ctx_insert Γ 0 (TyList A) = CtxU Γ (TyList A)) as same.
    { destruct Γ; simpl; auto. }
    rewrite same. apply wf_inst_insert. 
    inv H4. apply wf_ctx_insert_vtype in H5. all: aomega.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply ηDo.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply DoLoop.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply HandleLoop.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply HeqSym. auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply HeqTrans; eauto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  eapply HeqSigØ.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply JL in H5; eauto.
  eapply JL in H6; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply HeqSigU; eauto; simpl.
  - apply inst_get_case_Some; auto. eauto.
  - apply inst_get_case_Some; auto. eauto.
  - specialize (hyp_inst_shift_move_to_inst 0 2 Ψ I) as pad. simpl in pad.
    rewrite hyp_shift_inst, <-pad, <-(inst_shift_shift 1 1). eauto.
  - inv H5. inv H7. auto.
  - inv H5. inv H7. inv H12. auto.
+ eapply wf_inst_InstU in wfinst as wfinsc.
  eapply wf_inst_InstU in wfinsc as wfinsc.
  eapply JL in H3; eauto.
  eapply JL in H6; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. eapply HeqExtend; eauto; simpl.
  - apply inst_get_case_None; auto.
  - apply inst_get_case_None; auto.
  - specialize (hyp_inst_shift_move_to_inst 0 2 Ψ I) as pad. simpl in pad.
    rewrite hyp_shift_inst, <-pad, <-(inst_shift_shift 1 1). eauto.
  - inv H6. inv H7. auto.
  - inv H6. inv H7. inv H12. auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  apply IsHyp. apply has_hypothesis_inst. auto.
+ clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply TruthIn.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply FalsityEl. simpl in H3. eauto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply AndIn; eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. eapply AndElLeft. eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. eapply AndElRight. eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply OrLefteft. eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply OrRightight. eauto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  eapply JL in H5; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. apply OrEl; eauto.
+ eapply JL in H3; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. apply ImpliesIn. eauto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. eapply ImpliesEl. exact H3. eauto.
+ eapply JL in H3.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. apply ForallIn. rewrite hyp_shift_inst.
  2: instantiate (2:=(CtxU Γ A)).
  2: instantiate (1:= inst_pad_by_n I 1).
  rewrite hyp_inst_shift_move_to_inst in H3. simpl in H3. auto.
  simpl. apply wf_inst_InstU. 
  inv H3. inv H4. auto. auto.
+ eapply JL in H3 as IH1; eauto.
  eapply VL in H4 as IH2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. erewrite form_inst_subs. rewrite InstU_is_insert in IH1.
  eapply ForallEl; eauto. omega.
  all: apply wf_inst_ctx_len_same in wfinst; rewrite wfinst.
  inv H3. apply wf_form_is_under_ctx in H6. simpl in H6. auto.
  apply has_vtype_is_under_ctx in H4. auto.
+ eapply VL in H3 as IH1; eauto.
  eapply JL in H4 as IH2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl in *. eapply ExistsIn. eauto.
  erewrite form_inst_subs in IH2. rewrite InstU_is_insert. eauto. omega.
  all: apply wf_inst_ctx_len_same in wfinst; rewrite wfinst.
  apply wf_form_is_under_ctx in H1. simpl in H1. auto.
  apply has_vtype_is_under_ctx in H3. auto.
+ eapply JL in H3; eauto.
  eapply JL in H4; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  2: instantiate (2:=(CtxU Γ A)).
  2: instantiate (1:= inst_pad_by_n I 1).
  simpl in *. eapply ExistsEl. eauto.
  rewrite hyp_shift_inst, form_shift_inst.
  assert (InstU (inst_shift I 1 0) (Var 0) = inst_pad_by_n I 1) as same.
  { simpl. auto. }
  rewrite same, hyp_inst_shift_move_to_inst, form_inst_shift_move_to_inst in H4.
  simpl in H4. auto.
  simpl. apply wf_inst_InstU. 
  inv H4. inv H5. auto. auto.
+ eapply JL in H4 as IH1.
  2: instantiate (2:= (CtxU Γ A)).
  2: instantiate (1:= inst_pad_by_n I 1).
  assert (
    forall op Aop Bop,
     get_op_type Σ op = Some (Aop, Bop) ->
      judg (CtxU (CtxU Γ Aop) (TyFun Bop (CTy A Σ E)))
      (hyp_inst
          (HypU (hyp_shift Ψ 2 0)
            (Forall Bop
                (form_subs (form_shift φ 3 0) 3 (Fun TyUnit (App (Var 2) (Var 1))))))
          (InstU (inst_shift (InstU (inst_shift I 1 0) (Var 0)) 1 0) (Var 0)))
      (form_inst
          (form_subs (form_shift φ 2 0) 2
            (Fun TyUnit (Op op Aop Bop (Var 2) (App (Var 2) (Var 0)))))
          (InstU (inst_shift (InstU (inst_shift I 1 0) (Var 0)) 1 0) (Var 0)))
  ) as IH2.
  { intros op Aop Bop gets. specialize (H5 op Aop Bop gets).
    apply get_op_type_wf in gets. destruct gets.
    eapply JL in H5. all: clear VL CL HL RL JL WFHL WFFL WS. eauto.
    apply wf_inst_InstU. apply WfTyFun. auto. inv H1. inv H12. auto.
    apply wf_inst_InstU; auto. inv H1. inv H10. inv H9. auto. }
  eapply JL in H6 as IH3.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  2: instantiate (2:= Γ).
  2: instantiate (1:= I).
  inv H1. inv H10.
  apply wf_inst_ctx_len_same in wfinst as same_len.
  simpl. eapply CompInduction; eauto.
  - clear IH1 IH2 IH3 H5. rewrite InstU_is_insert. 
    apply var_admissible_inst; aomega.
    * apply inst_shift_makes_no_var.
    * rewrite inst_len_shift, same_len. apply wf_form_is_under_ctx in H11.
      simpl in H11. auto.
  - clear IH2. 
    rewrite hyp_shift_inst. rewrite hyp_inst_shift_move_to_inst in IH1.
    erewrite (form_inst_subs 1) in IH1. rewrite form_shift_inst.
    simpl in *. 
    assert (InstU
    (inst_insert (inst_shift (inst_shift I 1 0) 1 1) 0 (Var 1))
    (Var 0) = inst_pad_by_n (InstU (inst_shift I 1 0) (Var 0)) 1).
    { simpl. f_equal. rewrite InstU_is_insert. f_equal.
      rewrite <-inst_shift_comm; aomega. }
    rewrite H1, form_inst_shift_move_to_inst in IH1. clear H1. simpl in *.
    auto. simpl. omega.
    * apply form_under_var_shift. simpl. rewrite inst_len_shift, same_len.
      apply wf_form_is_under_ctx in H11. simpl in H11. auto. omega.
    * simpl. omega.
  - intros op Aop Bop gets. specialize (IH2 op Aop Bop gets).
    specialize (H5 op Aop Bop gets). clear IH1.
    apply get_op_type_wf in gets. destruct gets. simpl in *.
    rewrite hyp_shift_inst, form_shift_inst.
    rewrite (form_inst_subs 3), (form_inst_subs 2) in IH2. simpl in IH2.
    assert (
      InstU (InstU (inst_shift (inst_shift I 1 0) 1 0) (Var 1)) (Var 0)
      = inst_pad_by_n I 2) as pad2.
    { clear IH2. simpl. auto. }
    rewrite pad2, hyp_inst_shift_move_to_inst in IH2.
    assert (
      InstU (InstU (InstU (inst_insert
        (inst_shift (inst_shift (inst_shift (inst_shift I 1 0) 1 0) 1 0) 1 3)
        0 (Var 3)) (Var 2)) (Var 1)) (Var 0)
      = inst_pad_by_n (InstU (inst_shift I 1 0) (Var 0)) 3) as pad3.
    { clear IH2. simpl. do 4 f_equal.
      rewrite InstU_is_insert. f_equal.
      rewrite <-inst_shift_comm, <-inst_shift_comm, <-inst_shift_comm; aomega. }
    rewrite pad3, form_inst_shift_move_to_inst in IH2. clear pad2 pad3.
    rewrite form_shift_inst.
    assert (
      (InstU (InstU (inst_insert (inst_shift (inst_shift 
        (inst_shift I 1 0) 1 0) 1 2) 0 (Var 2)) (Var 1)) (Var 0))
      = inst_pad_by_n (InstU (inst_shift I 1 0) (Var 0)) 2)
      as pad2.
    { clear IH2. simpl. do 2 f_equal. rewrite InstU_is_insert. f_equal.
      rewrite <-inst_shift_comm. rewrite <-inst_shift_comm. all: aomega. }
    rewrite pad2, form_inst_shift_move_to_inst in IH2. auto.
    all: clear IH2; simpl; try rewrite inst_len_shift, inst_len_shift.
    all: try rewrite same_len; aomega.
    * rewrite <-(form_shift_shift 1). apply wf_form_is_under_ctx in H11.
      apply form_under_var_shift. apply form_under_var_shift. 
      simpl in H11. all: aomega.
    * rewrite <-(form_shift_shift 1), <-(form_shift_shift 1 1).
      apply form_under_var_shift. apply form_under_var_shift. 
      apply form_under_var_shift. apply wf_form_is_under_ctx in H11.
      rewrite inst_len_shift, same_len. simpl in H11. all: aomega.
    * inv H5. inv H9. auto.
  - clear IH1 IH2. erewrite form_inst_subs in IH3.
    rewrite InstU_is_insert. eauto. omega.
    * rewrite same_len. apply wf_form_is_under_ctx in H11. simpl in H11. auto.
    * simpl. constructor; constructor; aomega.
  - auto.
  - apply wf_inst_InstU; auto. inv H1. inv H10. inv H9. auto.
}{
destruct orig; simpl.
- clear VL CL HL RL JL WFHL WFFL WS.
  apply WfHypØ.
- eapply WFFL in H0; eauto.
  eapply WFHL in orig; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply WfHypU; auto.
}{
destruct orig; simpl.
- eapply VL in H0; eauto.
  eapply VL in H1; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply WfVeq; auto.
- eapply CL in H0; eauto.
  eapply CL in H1; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply WfCeq; auto.
- eapply HL in H3; eauto.
  eapply HL in H4; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  eapply WfHeq. 2: exact H1. all: eauto.
- clear VL CL HL RL JL WFHL WFFL WS.
  apply WfTruth. auto.
- clear VL CL HL RL JL WFHL WFFL WS.
  apply WfFalsity. auto.
- eapply WFFL in orig1; eauto.
  eapply WFFL in orig2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply WfAnd; eauto.
- eapply WFFL in orig1; eauto.
  eapply WFFL in orig2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply WfOr; eauto.
- eapply WFFL in orig1; eauto.
  eapply WFFL in orig2; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply WfImplies; eauto.
- eapply WFFL in orig; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply WfForall; eauto.
  apply wf_inst_InstU; eauto.
- eapply WFFL in orig; eauto.
  all: clear VL CL HL RL JL WFHL WFFL WS.
  simpl. apply WfExists; eauto.
  apply wf_inst_InstU; eauto.
}{
destruct orig; simpl.
- clear VL CL HL RL JL WFHL WFFL WS.
  apply WfInstØ. auto.
- eapply VL in H0; eauto.
  specialize (WS _ _ _ _ _ orig wfinst) as wff; eauto.
  clear VL CL HL RL JL WFHL WFFL WS.
  apply WfInstU; auto.
}
Qed.
