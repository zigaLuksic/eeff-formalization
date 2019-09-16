Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
Require Export syntax bidirectional substitution Omega Logic.

Ltac inv H := inversion H; clear H; subst.


Lemma vsub_lemma 
  (Γ : ctx) (v : val) (A : vtype)
  (v_s : val) (α : vtype) :
  vcheck (CtxU Γ α) v A ->
  vcheck Γ v_s α ->
  vcheck Γ (vsub_out v v_s) A
with csub_lemma 
  (Γ : ctx) (c : comp) (C : ctype)
  (v_s : val) (α : vtype) :
  ccheck (CtxU Γ α) c C ->
  vcheck Γ v_s α ->
  ccheck Γ (csub_out c v_s) C
with hsub_lemma 
  (Γ : ctx) (h : hcases) (Σ : sig) (D : ctype)
  (v_s : val) (α : vtype) :
  hcheck (CtxU Γ α) h Σ D ->
  vcheck Γ v_s α ->
  hcheck Γ (hsub_out h v_s) Σ D.
Proof.
{
intros orig ty_v_s.
induction v.
- inv orig. inv H. unfold vsub_out. simpl.
  destruct v as (name, db_i). simpl.
  induction db_i; simpl.
  + simpl in H2.
}

Qed.


(* 
Lemma v_sub_lemma
  (Γ : ctx) (vprog : val) (A : vtype)
  (x : var_id) (v : val) (α : vtype) :
  vcheck (CtxU Γ α) vprog A ->
  vcheck Γ v α ->
  vcheck Γ (Sub.v_sub vprog (0, v)) A
with c_sub_lemma
  (Γ : ctx) (cprog : comp) (C : ctype)
  (x : var_id) (v : val) (α : vtype) :
  ccheck (CtxU Γ α) cprog C ->
  vcheck Γ v α ->
  ccheck Γ (Sub.c_sub cprog (0, v)) C.
Proof.
{
induction vprog; intros typed_original typed_v.
+ simpl. inv typed_original. inv H.
  destruct v0 as (name, db_i).
  induction db_i.
  - simpl. simpl in H2. injection H2. 
    intro sametype. rewrite sametype in typed_v. assumption.
  - simpl. simpl in H2.
}
Qed. *)