Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Require Export syntax bidirectional substitution Omega Logic.

Ltac inv H := inversion H; clear H; subst.

Lemma v_add_to_ctx_safe (Γ:ctx) (α:vtype) (v:val) (A:vtype) :
  vcheck Γ v A -> vcheck (CtxU Γ α) (Sub.v_shift v 1 0) A
with c_add_to_ctx_safe (Γ:ctx) (α:vtype) (c:comp) (C:ctype) :
  ccheck Γ c C -> ccheck (CtxU Γ α) (Sub.c_shift c 1 0) C
with h_add_to_ctx_safe (Γ:ctx) (α:vtype) (h:hcases) (Σ:sig) (D:ctype) :
  hcheck Γ h Σ D -> hcheck (CtxU Γ α) (Sub.h_shift h 1 0) Σ D.
Proof.
all:
rename v_add_to_ctx_safe into v_lemma;
rename c_add_to_ctx_safe into c_lemma;
rename h_add_to_ctx_safe into h_lemma.
{
clear v_lemma.
revert Γ α A. induction v; intros Γ α A orig; simpl.
+ inv orig. inv H. apply CheckVBySynth. apply SynthVar.
  destruct v as (name, num). simpl.
  assert (num + 1 =? 0 = false).
  { apply beq_nat_false_iff. omega. }
  rewrite H. assert (num+1-1=num) by omega.
  rewrite H0. auto.
+ inv orig. inv H. apply CheckVBySynth. apply SynthUnit.
+ inv orig. inv H. apply CheckVBySynth. apply SynthInt.
+ inv orig. inv H. apply CheckInl. apply IHv. assumption.
+ inv orig. inv H. apply CheckInr. apply IHv. assumption.
+ inv orig. inv H.
  - apply CheckPair.
    * apply IHv1. apply CheckVBySynth. assumption. 
    * apply IHv2. apply CheckVBySynth. assumption.
  - apply CheckPair.
    * apply IHv1. assumption. 
    * apply IHv2. assumption.
+ inv orig. inv H. apply CheckFun. apply c_lemma.  

}