Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics". *)

Require Export syntax syntax_lemmas bidirectional substitution Omega Logic.

Ltac inv H := inversion H; clear H; subst.


Lemma extend_get_proof Γ α i αi:
  get_vtype_i Γ i = Some αi-> get_vtype_i (CtxU Γ α) (i + 1) = Some αi.
Proof.
assert (i + 1 = S i) by omega.
induction Γ; rewrite H; auto.
Qed.

(* Switch lemmas *)
Fixpoint v_switch_checksafe
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (v:val) (A:vtype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) 
  {struct v} :
  vcheck Γ v A ->
  vcheck (ctx_switch_vars Γ i j αi αj p_i p_j) (v_switch_vars v i j) A

with v_switch_synthsafe
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (v:val) (A:vtype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj)
  {struct v}:
  vsynth Γ v A ->
  vsynth (ctx_switch_vars Γ i j αi αj p_i p_j) (v_switch_vars v i j) A

with c_switch_checksafe 
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (c:comp) (C:ctype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj)
  {struct c}:
  ccheck Γ c C -> 
  ccheck (ctx_switch_vars Γ i j αi αj p_i p_j) (c_switch_vars c i j) C

with c_switch_synthsafe 
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (c:comp) (C:ctype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj)
  {struct c}:
  csynth Γ c C -> 
  csynth (ctx_switch_vars Γ i j αi αj p_i p_j) (c_switch_vars c i j) C

with h_switch_checksafe
  (Γ:ctx) i (αi:vtype) j (αj:vtype) (h:hcases) (Σ:sig) (D:ctype)
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj)
  {struct h}:
  hcheck Γ h Σ D ->
  hcheck (ctx_switch_vars Γ i j αi αj p_i p_j) (h_switch_vars h i j) Σ D.
Proof.
{
clear v_switch_checksafe.
clear c_switch_synthsafe.
revert Γ i j αi αj A p_i p_j; induction v;
intros Γ i j αi αj A p_i p_j orig.

all: inv orig; try inv H.
{ (* relevant case *)
  apply CheckVBySynth. simpl.
  destruct v as (name, num).
  remember (num =? i) as cmpi.
  induction cmpi; try apply SynthVar; simpl.
  + simpl in H2. apply eq_sym in Heqcmpi. apply beq_nat_true in Heqcmpi.
    rewrite Heqcmpi in H2. rewrite <-H2. apply eq_sym.
    apply get_in_switched_i.
  + remember (num =? j) as cmpj.
    induction cmpj.
    * simpl in H2. apply eq_sym in Heqcmpj. apply beq_nat_true in Heqcmpj.
      rewrite Heqcmpj in H2. apply SynthVar. rewrite <-H2. apply eq_sym.
      apply get_in_switched_j.
    * rewrite (gets_same Γ (name,num) num) in H2. apply SynthVar.
      rewrite <-H2. apply eq_sym. apply get_in_switched_other.
      apply eq_sym in Heqcmpi. apply beq_nat_false in Heqcmpi. auto.
      apply eq_sym in Heqcmpj. apply beq_nat_false in Heqcmpj. auto.
      simpl. apply eq_sym. apply beq_nat_refl.
}
+ apply CheckVBySynth. apply SynthUnit.
+ apply CheckVBySynth. apply SynthInt.
+ apply CheckInl. apply IHv. assumption.
+ apply CheckInr. apply IHv. assumption.
+ apply CheckPair; apply IHv1 || apply IHv2; apply CheckVBySynth; assumption.
+ apply CheckPair; apply IHv1 || apply IHv2; assumption.
+ apply CheckFun.
  apply (extend_get_proof _ α) in p_i as pp_i.
  apply (extend_get_proof _ α) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ α i j αi αj p_i p_j pp_i pp_j).
  apply c_switch_checksafe. auto.
+ apply CheckHandler.
  * apply (extend_get_proof _ α) in p_i as pp_i.
    apply (extend_get_proof _ α) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ α i j αi αj p_i p_j pp_i pp_j).
    apply c_switch_checksafe. auto.
  * apply h_switch_checksafe. auto.
+ apply CheckVBySynth. apply SynthVAnnot. apply IHv. auto.
}
{
clear v_switch_synthsafe.
clear c_switch_synthsafe.
clear h_switch_checksafe.
revert Γ i j αi αj A p_i p_j; induction v;
intros Γ i j αi αj A p_i p_j orig; inv orig; try inv H; simpl.
{ (* relevant case *)
  destruct v as (name, num).
  remember (num =? i) as cmpi.
  induction cmpi; try apply SynthVar; simpl.
  + simpl in H1. apply eq_sym in Heqcmpi. apply beq_nat_true in Heqcmpi.
    rewrite Heqcmpi in H1. rewrite <-H1. apply eq_sym.
    apply get_in_switched_i.
  + remember (num =? j) as cmpj.
    induction cmpj.
    * simpl in H1. apply eq_sym in Heqcmpj. apply beq_nat_true in Heqcmpj.
      rewrite Heqcmpj in H1. apply SynthVar. rewrite <-H1. apply eq_sym.
      apply get_in_switched_j.
    * rewrite (gets_same Γ (name,num) num) in H1. apply SynthVar.
      rewrite <-H1. apply eq_sym. apply get_in_switched_other.
      apply eq_sym in Heqcmpi. apply beq_nat_false in Heqcmpi. auto.
      apply eq_sym in Heqcmpj. apply beq_nat_false in Heqcmpj. auto.
      simpl. apply eq_sym. apply beq_nat_refl.
} 
+ apply SynthUnit.
+ apply SynthInt.
+ apply SynthPair; apply IHv1 || apply IHv2; assumption.
+ apply SynthVAnnot. apply v_switch_checksafe. assumption.
}
{
clear c_switch_checksafe.
clear h_switch_checksafe.
revert Γ i j αi αj C p_i p_j; induction c;
intros Γ i j αi αj C p_i p_j orig; inv orig; try inv H.
+ remember (CTy α SigØ EqsØ) as C.
  apply (CheckCBySynth _ _ C C); auto.
  rewrite HeqC. apply SynthRet.
  apply v_switch_synthsafe. assumption.
+ apply (CheckCBySynth _ _ C' C'); auto.
  apply (SynthΠMatch _ _ α β).
  apply v_switch_synthsafe. assumption.
  clear v_switch_checksafe.
  apply (extend_get_proof _ α) in p_i as pp_i.
  apply (extend_get_proof _ α) in p_j as pp_j.
  apply (extend_get_proof _ β) in pp_i.
  apply (extend_get_proof _ β) in pp_j.
  assert (i+1+1=i+2) by omega. rewrite H in pp_i.
  assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
  rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
  apply c_switch_synthsafe; assumption.
+ apply (CheckΣMatch _ _ α β); try apply v_switch_synthsafe; auto.
  - apply (extend_get_proof _ α) in p_i as pp_i;
    apply (extend_get_proof _ α) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ α i j αi αj p_i p_j pp_i pp_j).
    apply IHc1. assumption.
  - apply (extend_get_proof _ β) in p_i as pp_i;
    apply (extend_get_proof _ β) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ β i j αi αj p_i p_j pp_i pp_j).
    apply IHc2. assumption.
+ apply (CheckCBySynth _ _ C' C'); auto.
  apply (SynthApp _ _ _ α C'). apply v_switch_synthsafe; assumption. auto.
+ simpl. apply (CheckOp _ _ _ _ _ α_op β_op α Σ eqs); auto.
  apply (extend_get_proof _ β_op) in p_i as pp_i.
  apply (extend_get_proof _ β_op) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ β_op i j αi αj p_i p_j pp_i pp_j).
  apply IHc. assumption.
+ apply (CheckCBySynth _ _ C' C'); auto.
  apply SynthLetRec.
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ (TyFun A C)) in pp_i.
    apply (extend_get_proof _ (TyFun A C)) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply IHc1. auto.
  - apply (extend_get_proof _ (TyFun A C)) in p_i as pp_i.
    apply (extend_get_proof _ (TyFun A C)) in p_j as pp_j.
    rewrite (ctx_switch_extend1 _ _ _ _ _ _  p_i p_j pp_i pp_j).
    apply c_switch_synthsafe. auto.
+ apply (CheckCBySynth _ _ C' C'); auto.
  apply (SynthHandle _ _ _ ctyC); auto.
+ apply (CheckCBySynth _ _ C' C'); auto.
  apply SynthCAnnot. auto.
}
{
clear c_switch_synthsafe.
clear h_switch_checksafe.
revert Γ i j αi αj C p_i p_j; induction c;
intros Γ i j αi αj C p_i p_j orig; inv orig; try inv H; simpl.
+ apply SynthRet. apply v_switch_synthsafe. auto.
+ apply (SynthΠMatch _ _ α β).
  apply v_switch_synthsafe. assumption.
  clear v_switch_checksafe.
  apply (extend_get_proof _ α) in p_i as pp_i.
  apply (extend_get_proof _ α) in p_j as pp_j.
  apply (extend_get_proof _ β) in pp_i.
  apply (extend_get_proof _ β) in pp_j.
  assert (i+1+1=i+2) by omega. rewrite H in pp_i.
  assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
  rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
  apply IHc. assumption.
+ apply (SynthApp _ _ _ α C); auto.
+ apply (SynthLetRec).
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ (TyFun A C0)) in pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply c_switch_checksafe. auto.
  - apply (extend_get_proof _ (TyFun A C0)) in p_i as pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in p_j as pp_j.
    rewrite (ctx_switch_extend1 _ _ _ _ _ _  p_i p_j pp_i pp_j).
    apply IHc2. auto.
+ apply (SynthHandle _ _ _ ctyC C).
  - apply v_switch_synthsafe. auto.
  - apply c_switch_checksafe. auto.
+ apply SynthCAnnot. apply c_switch_checksafe. auto.
}
{
clear c_switch_synthsafe.
clear h_switch_checksafe.
revert Γ i j αi αj Σ D p_i p_j; induction h;
intros Γ i j αi αj Σ D p_i p_j orig; inv orig; try inv H; simpl.
apply CheckCasesØ.
apply CheckCasesU.
+ apply hcases_switch_None. auto.
+ apply IHh. auto.
+ apply (extend_get_proof _ (TyFun β_op D)) in p_i as pp_i.
  apply (extend_get_proof _ (TyFun β_op D)) in p_j as pp_j.
  apply (extend_get_proof _ α_op) in pp_i.
  apply (extend_get_proof _ α_op) in pp_j.
  assert (i+1+1=i+2) by omega. rewrite H in pp_i.
  assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
  rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
  apply c_switch_checksafe. auto.
}
Qed.
(* 


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

} *)