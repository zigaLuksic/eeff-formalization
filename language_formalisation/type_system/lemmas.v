(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional substitution
  subs_lemmas Omega Logic type_aux_lemmas.


Ltac inv H := inversion H; clear H; subst.

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

Proof.
{
clear vcheck_sub_lemma.
clear csynth_sub_lemma.
revert Γ A.
induction v; intros Γ A orig ty_v_s; inv orig; try inv H
; unfold vsub_out; simpl.
- destruct v as (name, db_i). simpl.
  destruct db_i; simpl.
  + simpl in H2.
    rewrite (vshifts_cancel 1 1 0 v_s). simpl.
    rewrite (vzero_shift 0 v_s).
    injection H2. intro sametype.
    rewrite <-sametype. assumption. omega.
  + apply CheckVBySynth. apply SynthVar.
    simpl in *. assert (db_i - 0 = db_i) by omega. rewrite H.
    assumption.
- apply CheckVBySynth. apply SynthUnit.
- apply CheckVBySynth. apply SynthInt.
- apply CheckInl. apply IHv; auto.
- apply CheckInr. apply IHv; auto.
- apply CheckVBySynth. apply SynthPair;
  apply (vsynth_sub_lemma _ _ _ _ α); auto.
- apply CheckFun.
  apply c_switch10_checksafe in H3.
  apply (ccheck_sub_lemma _ _ _ v_s) in H3.
  unfold csub_out in H3. simpl in *.
  specialize (ccheck_sub_lemma (CtxU Γ α0) c C v_s α).
  
  



    }

Qed.
