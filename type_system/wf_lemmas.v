Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export syntax_lemmas declarational.


Lemma get_vtype_wf Γ num A : 
    wf_ctx Γ -> get_vtype Γ num = Some A -> wf_vtype A.
Proof.
intros wf. revert num. induction wf; intros num gets; simpl in *.
+ discriminate.
+ destruct num. inv gets. auto. eauto.
Qed.


Lemma wf_ctx_insert Γ A i:
  wf_ctx Γ -> wf_vtype A -> wf_ctx (ctx_insert Γ i A).
Proof.
revert i A. induction Γ; intros i A orig wfv; induction i; simpl.
all: (try inv orig); apply WfCtxU || apply WfCtxØ; auto.
all: apply WfCtxU || apply WfCtxØ; auto.
Qed.


Lemma wf_ctx_insert_rev Γ A i:
  wf_ctx (ctx_insert Γ i A) -> wf_ctx Γ.
Proof.
revert i A. induction Γ; intros i A orig. apply WfCtxØ.
destruct i; simpl in *; inv orig. auto. apply WfCtxU; eauto.
Qed.


Lemma wf_ctx_insert_vtype Γ A i:
  wf_ctx (ctx_insert Γ i A) -> i <= ctx_len Γ -> wf_vtype A.
Proof.
revert i. induction Γ; intros i wf safe; simpl in *.
+ destruct i. inv wf. auto. omega.
+ destruct i. inv wf. auto. inv wf. eapply IHΓ; eauto. omega.
Qed.


Lemma get_op_type_wf Σ op A_op B_op:
  wf_sig Σ -> get_op_type Σ op = Some (A_op, B_op) ->
  wf_vtype A_op /\ wf_vtype B_op.
Proof.
induction Σ; intros orig gets; constructor; simpl in *; try discriminate.
all: destruct (op == o); inv orig; try inv gets; auto; apply IHΣ; auto.
Qed.


Lemma wf_join_ctxs Γ Γ' :
  wf_ctx Γ -> wf_ctx Γ' -> wf_ctx (join_ctxs Γ Γ').
Proof.
intros wf wf'. induction wf'; simpl; auto. apply WfCtxU; auto.
Qed.


Lemma wf_join_ctxs_rev Γ Γ' :
  wf_ctx (join_ctxs Γ Γ') -> wf_ctx Γ /\ wf_ctx Γ'.
Proof.
intros orig. induction Γ'; simpl in *.
constructor. auto. apply WfCtxØ.
inv orig. apply IHΓ' in H1. destruct H1. constructor. auto.
apply WfCtxU; auto.
Qed.


Lemma wf_tctx_to_ctx Z D:
  wf_tctx Z -> wf_ctype D -> wf_ctx (tctx_to_ctx Z D).
Proof.
intros wfZ wfD. induction wfZ; simpl. apply WfCtxØ. 
apply WfCtxU. auto. apply WfTyFun; auto.
Qed.


Lemma wf_tctx_to_ctx_rev Z D:
  wf_ctx (tctx_to_ctx Z D) -> wf_tctx Z.
Proof.
intros orig. induction Z; simpl in *. apply WfTCtxØ. 
inv orig. inv H2. apply WfTCtxU; auto.
Qed.


Lemma has_eq_wf_parts E Σ Γ Z T1 T2:
  wf_eqs E Σ -> has_eq E Γ Z T1 T2 ->
  wf_ctx Γ /\ wf_tctx Z /\ wf_t Γ Z T1 Σ /\ wf_t Γ Z T2 Σ.
Proof.
intros wf_eqs has. induction wf_eqs; inv has; auto.
destruct H4 as [a [b [c d]]]. subst. do 3 aconstructor.  
Qed.

(* ==================== Instantiations ==================== *)

Lemma wf_inst_wf_ctx Γ' I Γ:
  wf_inst Γ' I Γ -> wf_ctx Γ.
Proof.
revert Γ' I. induction Γ; intros Γ' I orig.
+ apply WfCtxØ.
+ inv orig. inv H3. apply WfCtxU; eauto.
Qed.


Lemma wf_inst_ctx_len_same Γ' I Γ:
  wf_inst Γ' I Γ -> inst_len I = ctx_len Γ.
Proof.
intros orig. induction orig; simpl; auto.
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
Qed.

(* ==================== Hypotheses ==================== *)

Lemma wf_hyp_ctx Γ Ψ:
  wf_hypotheses Γ Ψ -> wf_ctx Γ.
Proof.
intros wf. induction wf; auto.
Qed.


Lemma wf_has_hypothesis Γ Ψ φ:
  wf_hypotheses Γ Ψ -> has_hypothesis Ψ φ ->
  wf_formula Γ φ.
Proof.
intros wfhy has.
induction wfhy; simpl in has; destruct has.
subst. auto. auto.
Qed.


Lemma hyp_subset_has_hypothesis Ψ Ψ' φ:
  has_hypothesis Ψ φ -> hyp_subset Ψ Ψ' ->
  has_hypothesis Ψ' φ.
Proof.
intros has subset. induction subset; simpl in has; destruct has.
subst. auto. auto.
Qed.


Lemma wf_subset Γ Ψ Ψ':
  wf_hypotheses Γ Ψ' -> hyp_subset Ψ Ψ' ->
  wf_hypotheses Γ Ψ.
Proof.
intros wf' subset.
induction subset.
- apply WfHypØ. eapply wf_hyp_ctx. eauto.
- apply WfHypU; auto. eapply wf_has_hypothesis; eauto.
  eapply hyp_subset_has_hypothesis; eauto.
Qed.