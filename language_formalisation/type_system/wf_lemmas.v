(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".

Require Export syntax_lemmas declarational substitution_lemmas.

Lemma ctx_gets_wf Γ num A : 
    wf_ctx Γ -> get_vtype Γ num = Some A -> wf_vtype A.
Proof.
intros wf. revert num. induction wf; intros num gets.
+ simpl in gets. discriminate.
+ simpl in gets. destruct num.
  - inv gets. assumption.
  - eapply IHwf. exact gets.
Qed.

Lemma ctx_insert_wf Γ A i:
  wf_ctx Γ -> wf_vtype A -> wf_ctx (ctx_insert_var Γ A i).
Proof.
revert i A; induction Γ; intros i A orig wfv.
+ induction i; simpl.
  * apply WfCtxU; assumption.
  * apply WfCtxØ.
+ induction i; simpl.
  * apply WfCtxU; assumption.
  * inv orig. apply WfCtxU; try apply IHΓ; assumption.
Qed.

Lemma ctx_remove_wf Γ i:
  wf_ctx Γ -> wf_ctx (ctx_remove_var Γ i).
Proof.
revert i; induction Γ; intros i orig.
+ induction i; simpl; apply WfCtxØ.
+ induction i; simpl; inv orig.
  * assumption.
  * apply WfCtxU; try apply IHΓ; assumption.
Qed.

Lemma get_op_type_wf Σ op A_op B_op:
  wf_sig Σ -> get_op_type Σ op = Some (A_op, B_op) ->
  wf_vtype A_op /\ wf_vtype B_op.
Proof.
induction Σ; intros orig gets; constructor.
+ simpl in gets. discriminate.
+ simpl in gets. discriminate.
+ simpl in *. destruct (op == o).
  - inv gets. inv orig. assumption.
  - inv orig. apply IHΣ; assumption.
+ simpl in *. destruct (op == o).
  - inv gets. inv orig. assumption.
  - inv orig. apply IHΣ; assumption.
Qed.

Lemma join_ctxs_wf Γ Γ' :
  wf_ctx Γ -> wf_ctx Γ' -> wf_ctx (join_ctxs Γ Γ').
Proof.
intros wf wf'. induction wf'; simpl; auto.
apply WfCtxU; auto.
Qed.

Lemma join_ctx_tctx_wf Γ Z D:
  wf_ctx Γ -> wf_tctx Z -> wf_ctype D -> wf_ctx (join_ctx_tctx Γ Z D).
Proof.
intros wfctx wfZ wfD. induction wfZ; simpl. auto.
apply WfCtxU. auto. apply WfTyFun; auto.
Qed.