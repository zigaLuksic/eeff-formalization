(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas.


Ltac inv H := inversion H; clear H; subst.

Lemma v_subs_checksafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A:vtype) :
  vcheck Γ v A -> get_vtype_i Γ i = Some A ->
  vcheck Γ v_s A ->
  vcheck Γ (Sub.v_sub v (i, v_s)) A
Lemma v_subs_synthsafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A:vtype) :
  vsynth Γ v A -> get_vtype_i Γ i = Some A ->
  vcheck Γ v_s A ->
  vsynth Γ (Sub.v_sub v (i, v_s)) A


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
