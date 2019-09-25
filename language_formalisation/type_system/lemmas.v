(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas.


Ltac inv H := inversion H; clear H; subst.

Lemma v_subs_typesafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A_s:vtype) :
  has_vtype Γ v A -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (i:nat) (v_s:val) (A_s:vtype) :
  has_ctype Γ c C -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (i:nat) (v_s:val) (A_s:vtype) :
  has_htype Γ h Σ D -> get_vtype_i Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
{
clear v_subs_typesafe.
revert Γ A i. induction v; intros Γ A i orig in_ctx vstyped;
simpl; inv orig.
+ destruct v as (name, num). simpl.
  remember (num=?i) as cmp. destruct cmp.
  - rewrite (gets_same _ _ i) in H1.
    * rewrite H1 in in_ctx. injection in_ctx. intro samety.
      rewrite samety. assumption.
    * simpl. apply eq_sym. assumption.
  - apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv; auto.
+ apply TypeInr. apply IHv; auto.
+ apply TypePair; try apply IHv1 || apply IHv2; auto.
+ apply TypeFun. eapply c_subs_typesafe.
  - assumption.
  - assert (i+1=S i) by omega. rewrite H. simpl.
    exact in_ctx.
  - 




}





(* 
Lemma vcheck_sub_lemma 
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (A:vtype) :
  vcheck (CtxU Γ A) v A ->
  vcheck Γ v_s A ->
  vcheck Γ (vsub_out v v_s) A

with vsynth_sub_lemma 
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (A:vtype) :
  vsynth (CtxU Γ A) v A ->
  vcheck Γ v_s A ->
  vsynth Γ (vsub_out v v_s) A

with ccheck_sub_lemma 
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (A:vtype) :
  ccheck (CtxU Γ A) c C ->
  vcheck Γ v_s A ->
  ccheck Γ (csub_out c v_s) C

with csynth_sub_lemma 
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (A:vtype) :
  csynth (CtxU Γ A) c C ->
  vcheck Γ v_s A ->
  csynth Γ (csub_out c v_s) C

with hcheck_sub_lemma 
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (v_s:val) (A:vtype) :
  hcheck (CtxU Γ A) h Σ D ->
  vcheck Γ v_s A ->
  hcheck Γ (hsub_out h v_s) Σ D.

Proof. *)


    }

Qed.
