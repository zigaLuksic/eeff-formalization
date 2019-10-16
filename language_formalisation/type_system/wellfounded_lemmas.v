Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas.

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
  - injection gets. intros. subst. inv orig. assumption.
  - inv orig. apply IHΣ; assumption.
+ simpl in *. destruct (op == o).
  - injection gets. intros. subst. inv orig. assumption.
  - inv orig. apply IHΣ; assumption.
Qed.