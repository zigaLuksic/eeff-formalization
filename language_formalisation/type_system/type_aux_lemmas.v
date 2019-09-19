(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics".

Require Export syntax bidirectional substitution Omega Logic.

Ltac inv H := inversion H; clear H; subst.

(* Switch lemmas *)
Lemma v_switch_safe
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (v:val) (A:vtype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  vcheck Γ v A ->
  vcheck (ctx_switch_vars Γ i j αi αj p_i p_j) (v_switch_vars v i j) A

with c_switch_safe 
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (c:comp) (C:ctype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  ccheck Γ c C -> 
  ccheck (ctx_switch_vars Γ i j αi αj p_i p_j) (c_switch_vars c i j) C

with h_switch_safe
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (h:hcases) (Σ:sig) (D:ctype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  hcheck Γ h Σ D ->
  hcheck (ctx_switch_vars Γ i j αi αj p_i p_j) (h_switch_vars h i j) Σ D.
Proof.
{
clear v_switch_safe.
revert Γ i j αi αj A p_i p_j; induction v;
intros Γ i j αi αj A p_i p_j orig; simpl.
{ (* relevant case *)
  destruct v as (num, name).
  inv orig. inv H.
  remember (name =? i) as cmpi.
  induction cmpi.
  + apply CheckVBySynth. apply SynthVar. simpl.
    simpl in H2. rewrite <-Heqcmpi in H2. assumption.
  + remember (name =? 1) as cmpj.
    induction cmpj.
    * apply CheckVBySynth. apply SynthVar. simpl.
      simpl in H2. rewrite <-Heqcmpi in H2.
      apply eq_sym in Heqcmpj.
      apply beq_nat_true in Heqcmpj. rewrite Heqcmpj in H2. simpl in H2.
      assumption.
    * apply CheckVBySynth. apply SynthVar. simpl.
      rewrite <-Heqcmpi. simpl.
      simpl in H2. rewrite <-Heqcmpi in H2.
      apply eq_sym in Heqcmpi. apply eq_sym in Heqcmpj.
      apply beq_nat_false in Heqcmpi. apply beq_nat_false in Heqcmpj.
      assert (name-1 <> 0) by omega.
      apply beq_nat_false_iff in H. rewrite H. rewrite H in H2. simpl.
      assumption.
}
all: inv orig; try inv H; simpl.
+ apply CheckVBySynth. apply SynthUnit.
+ apply CheckVBySynth. apply SynthInt.
+ apply CheckInl. apply IHv. assumption.
+ apply CheckInr. apply IHv. assumption.
+ apply CheckPair; apply IHv1 || apply IHv2; apply CheckVBySynth; assumption.
+ apply CheckPair; apply IHv1 || apply IHv2; assumption.
+ apply CheckFun. 

}




(* Other lemmas *)
Lemma v_add_to_ctx_safe (Γ:ctx) (α:vtype) (v:val) (A:vtype) :
  vcheck Γ v A ->
  vcheck (CtxU Γ α) (Sub.v_shift v 1 0) A
  /\
  v_no_var_j v j
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