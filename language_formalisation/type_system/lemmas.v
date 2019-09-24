(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas.


Ltac inv H := inversion H; clear H; subst.

Lemma v_subs_checksafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (α:vtype) :
  vcheck Γ v A -> get_vtype_i Γ i = Some α ->
  vcheck Γ v_s α ->
  vcheck Γ (Sub.v_sub v (i, v_s)) A
Lemma v_subs_synthsafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (α:vtype) :
  vsynth Γ v A -> get_vtype_i Γ i = Some α ->
  vcheck Γ v_s α ->
  vsynth Γ (Sub.v_sub v (i, v_s)) A


(* 
Lemma vcheck_sub_lemma 
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (α:vtype) :
  vcheck (CtxU Γ α) v A ->
  vcheck Γ v_s α ->
  vcheck Γ (vsub_out v v_s) A

with vsynth_sub_lemma 
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (α:vtype) :
  vsynth (CtxU Γ α) v A ->
  vcheck Γ v_s α ->
  vsynth Γ (vsub_out v v_s) A

with ccheck_sub_lemma 
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (α:vtype) :
  ccheck (CtxU Γ α) c C ->
  vcheck Γ v_s α ->
  ccheck Γ (csub_out c v_s) C

with csynth_sub_lemma 
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (α:vtype) :
  csynth (CtxU Γ α) c C ->
  vcheck Γ v_s α ->
  csynth Γ (csub_out c v_s) C

with hcheck_sub_lemma 
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (v_s:val) (α:vtype) :
  hcheck (CtxU Γ α) h Σ D ->
  vcheck Γ v_s α ->
  hcheck Γ (hsub_out h v_s) Σ D.

Proof. *)


    }

Qed.
