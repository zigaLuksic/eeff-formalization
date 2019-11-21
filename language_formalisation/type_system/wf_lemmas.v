Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Export syntax_lemmas declarational substitution_lemmas.


Lemma get_vtype_wf Γ num A : 
    wf_ctx Γ -> get_vtype Γ num = Some A -> wf_vtype A.
Proof.
intros wf. revert num. induction wf; intros num gets; simpl in *.
discriminate. destruct num.
- inv gets. assumption.
- eapply IHwf. exact gets.
Qed.


Lemma ctx_insert_wf Γ A i:
  wf_ctx Γ -> wf_vtype A -> wf_ctx (ctx_insert Γ A i).
Proof.
revert i A; induction Γ; intros i A orig wfv; induction i; simpl.
all: (try inv orig); apply WfCtxU || apply WfCtxØ; auto.
all: apply WfCtxU || apply WfCtxØ; auto.
Qed.


Lemma ctx_remove_wf Γ i:
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


Lemma join_ctxs_wf Γ Γ' :
  wf_ctx Γ -> wf_ctx Γ' -> wf_ctx (join_ctxs Γ Γ').
Proof.
intros wf wf'. induction wf'; simpl; auto. apply WfCtxU; auto.
Qed.


Lemma join_ctx_tctx_wf Γ Z D:
  wf_ctx Γ -> wf_tctx Z -> wf_ctype D -> wf_ctx (join_ctx_tctx Γ Z D).
Proof.
intros wfctx wfZ wfD. induction wfZ; simpl. auto. 
apply WfCtxU. auto. apply WfTyFun; auto.
Qed.
