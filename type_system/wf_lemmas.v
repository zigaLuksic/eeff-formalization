(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".

Require Export syntax_lemmas declarational substitution_lemmas.


Lemma get_vtype_wf Γ num A : 
    wf_ctx Γ -> get_vtype Γ num = Some A -> wf_vtype A.
Proof.
intros wf. revert num. induction wf; intros num gets; simpl in *.
discriminate. destruct num.
- inv gets. assumption.
- eapply IHwf. exact gets.
Qed.


Lemma wf_ctx_insert Γ A i:
  wf_ctx Γ -> wf_vtype A -> wf_ctx (ctx_insert Γ A i).
Proof.
revert i A; induction Γ; intros i A orig wfv; induction i; simpl.
all: (try inv orig); apply WfCtxU || apply WfCtxØ; auto.
all: apply WfCtxU || apply WfCtxØ; auto.
Qed.

Lemma wf_ctx_insert_rev Γ A i:
  wf_ctx (ctx_insert Γ A i) -> wf_ctx Γ.
Proof.
revert i A. induction Γ; intros i A orig. apply WfCtxØ.
destruct i; simpl in *; inv orig. assumption. apply WfCtxU; eauto.
Qed.

Lemma wf_ctx_remove Γ i:
  wf_ctx Γ -> wf_ctx (ctx_remove Γ i).
Proof.
revert i; induction Γ; intros i orig; induction i; simpl.
all: apply WfCtxØ || (inv orig; apply WfCtxU || auto); auto.
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


Lemma wf_tctx_to_ctx Z D:
  wf_tctx Z -> wf_ctype D -> wf_ctx (tctx_to_ctx Z D).
Proof.
intros wfZ wfD. induction wfZ; simpl. apply WfCtxØ. 
apply WfCtxU. auto. apply WfTyFun; auto.
Qed.

Lemma has_eq_wf_parts E Σ Γ Z T1 T2:
  wf_eqs E Σ -> has_eq E Γ Z T1 T2 ->
  wf_ctx Γ /\ wf_tctx Z /\ wf_t Γ Z T1 Σ /\ wf_t Γ Z T2 Σ.
Proof.
intros wf_eqs has. induction wf_eqs; inv has.
- destruct H4 as [a [b [c d]]]. subst. 
  constructor. 2:constructor. 3:constructor. all: auto.
- auto.
Qed.