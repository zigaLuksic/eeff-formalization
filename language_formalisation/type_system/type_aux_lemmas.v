Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics". *)

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas.

Ltac inv H := inversion H; clear H; subst.


Lemma extend_get_proof Γ A i Ai:
  get_vtype_i Γ i = Some Ai-> get_vtype_i (CtxU Γ A) (i + 1) = Some Ai.
Proof.
assert (i + 1 = S i) by omega.
induction Γ; rewrite H; auto.
Qed.



(* Switch lemmas *)
Fixpoint v_switch_typesafe
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (v:val) (A:vtype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj) 
  {struct v} :
  has_vtype Γ v A ->
  has_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (v_switch_vars v i j) A

with c_switch_typesafe 
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (c:comp) (C:ctype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj)
  {struct c}:
  has_ctype Γ c C -> 
  has_ctype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (c_switch_vars c i j) C

with h_switch_typesafe
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (h:hcases) (Σ:sig) (D:ctype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj)
  {struct h}:
  has_htype Γ h Σ D ->
  has_htype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (h_switch_vars h i j) Σ D.
Proof.
{
clear v_switch_typesafe.
revert Γ i j Ai Aj A p_i p_j; induction v; intros Γ i j Ai Aj A p_i p_j orig.
all: inv orig; try inv H; simpl.
{ (* relevant case *)
  destruct v as (name, num).
  remember (num =? i) as cmpi. destruct cmpi; simpl.
  + apply TypeVar. simpl.
    simpl in *. apply eq_sym in Heqcmpi. apply beq_nat_true in Heqcmpi.
    rewrite Heqcmpi in H1. rewrite <-H1. apply eq_sym.
    apply switch_ij_get_j.
  + remember (num =? j) as cmpj. destruct cmpj.
    * simpl in *. apply eq_sym in Heqcmpj. apply beq_nat_true in Heqcmpj.
      rewrite Heqcmpj in H1. apply TypeVar. rewrite <-H1. apply eq_sym.
      apply switch_ij_get_i.
    * rewrite (gets_same Γ (name,num) num) in H1. apply TypeVar.
      rewrite <-H1. apply eq_sym. apply switch_ij_get_k.
      - apply eq_sym in Heqcmpi. apply beq_nat_false in Heqcmpi. auto.
      - apply eq_sym in Heqcmpj. apply beq_nat_false in Heqcmpj. auto.
      - simpl. apply eq_sym. apply beq_nat_refl.
}
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. auto.
+ apply TypeInr. auto.
+ apply TypePair; auto.
+ apply TypeFun. auto.
  apply (extend_get_proof _ A0) in p_i as pp_i.
  apply (extend_get_proof _ A0) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ A0 i j Ai Aj p_i p_j pp_i pp_j).
  auto.
+ apply TypeHandler; auto.
  apply (extend_get_proof _ A0) in p_i as pp_i.
  apply (extend_get_proof _ A0) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ A0 i j Ai Aj p_i p_j pp_i pp_j).
  auto.
+ apply TypeVAnnot. auto.
}{
clear c_switch_typesafe.
revert Γ i j Ai Aj C p_i p_j; induction c;
intros Γ i j Ai Aj C p_i p_j orig; inv orig; try inv H.
+ apply TypeRet. auto.
+ eapply TypeΠMatch.
  - apply v_switch_typesafe. exact H4.
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ B) in pp_i.
    apply (extend_get_proof _ B) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply IHc. assumption.
+ eapply TypeΣMatch. 
  - apply v_switch_typesafe; exact H6.
  - apply (extend_get_proof _ A) in p_i as pp_i;
    apply (extend_get_proof _ A) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ A i j Ai Aj p_i p_j pp_i pp_j).
    apply IHc1. assumption.
  - apply (extend_get_proof _ B) in p_i as pp_i;
    apply (extend_get_proof _ B) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ B i j Ai Aj p_i p_j pp_i pp_j).
    apply IHc2. assumption.
+ eapply TypeApp.
  - apply v_switch_typesafe. exact H2.
  - apply v_switch_typesafe. assumption.
+ eapply TypeOp. exact H5. auto.
  apply (extend_get_proof _ B_op) in p_i as pp_i.
  apply (extend_get_proof _ B_op) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ B_op i j Ai Aj p_i p_j pp_i pp_j).
  apply IHc. assumption.
+ apply TypeLetRec.
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ (TyFun A C0)) in pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply IHc1. assumption.
  - apply (extend_get_proof _ (TyFun A C0)) in p_i as pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in p_j as pp_j.
    rewrite (ctx_switch_extend1 _ _ _ _ _ _  p_i p_j pp_i pp_j).
    apply IHc2. assumption.
+ eapply TypeHandle.
  - apply v_switch_typesafe. exact H2.
  - apply IHc. assumption.
+ apply TypeCAnnot. apply IHc. assumption.
}{
clear h_switch_typesafe.
revert Γ i j Ai Aj Σ D p_i p_j; induction h;
intros Γ i j Ai Aj Σ D p_i p_j orig; inv orig; try inv H; simpl.
apply TypeCasesØ.
apply TypeCasesU.
+ apply find_op_None_switch. assumption.
+ apply IHh. assumption.
+ apply (extend_get_proof _ (TyFun B_op D)) in p_i as pp_i.
  apply (extend_get_proof _ (TyFun B_op D)) in p_j as pp_j.
  apply (extend_get_proof _ A_op) in pp_i.
  apply (extend_get_proof _ A_op) in pp_j.
  assert (i+1+1=i+2) by omega. rewrite H in pp_i.
  assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
  rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
  apply c_switch_typesafe. assumption.
}
Qed.

(* Switch lemmas *)
Fixpoint v_switch10_typesafe
  (Γ:ctx) (A1:vtype) (A0:vtype) (v:val) (A:vtype)
  {struct v} :
  has_vtype (CtxU (CtxU Γ A1) A0) v A ->
  has_vtype (CtxU (CtxU Γ A0) A1) (v_switch_vars v 1 0) A

with c_switch10_typesafe 
  (Γ:ctx) (A1:vtype) (A0:vtype) (c:comp) (C:ctype)
  {struct c}:
  has_ctype (CtxU (CtxU Γ A1) A0) c C -> 
  has_ctype (CtxU (CtxU Γ A0) A1) (c_switch_vars c 1 0) C

with h_switch10_typesafe
  (Γ:ctx) (A1:vtype) (A0:vtype) (h:hcases) (Σ:sig) (D:ctype)
  {struct h}:
  has_htype (CtxU (CtxU Γ A1) A0) h Σ D ->
  has_htype (CtxU (CtxU Γ A0) A1) (h_switch_vars h 1 0) Σ D.
Proof.
all: intro orig; remember (CtxU (CtxU Γ A1) A0) as Γ'.
all: assert (get_vtype_i Γ' 1 = Some A1) as p_1.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ' 0 = Some A0) as p_0.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (ctx_switch_vars Γ' 1 0 A1 A0 p_1 p_0 = CtxU (CtxU Γ A0) A1).
all: try (unfold ctx_switch_vars; rewrite HeqΓ'; simpl; f_equal).
all: rewrite <-H.
+ apply v_switch_typesafe. assumption.
+ apply c_switch_typesafe. assumption.
+ apply h_switch_typesafe. assumption.
Qed.

(* Switch lemmas *)
Fixpoint v_switch210_typesafe
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (v:val) (A:vtype)
  {struct v} :
  has_vtype (CtxU (CtxU (CtxU Γ A2) A1) A0) v A ->
  has_vtype (CtxU (CtxU (CtxU Γ A0) A2) A1) (v_switch210_vars v) A

with c_switch210_typesafe 
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (c:comp) (C:ctype)
  {struct c}:
  has_ctype (CtxU (CtxU (CtxU Γ A2) A1) A0) c C -> 
  has_ctype (CtxU (CtxU (CtxU Γ A0) A2) A1) (c_switch210_vars c) C

with h_switch210_typesafe
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (h:hcases) (Σ:sig) (D:ctype)
  {struct h}:
  has_htype (CtxU (CtxU (CtxU Γ A2) A1) A0) h Σ D ->
  has_htype (CtxU (CtxU (CtxU Γ A0) A2) A1) (h_switch210_vars h) Σ D.
Proof.
all: intro orig; remember (CtxU (CtxU (CtxU Γ A2) A1) A0) as Γ'.
all: remember (CtxU (CtxU (CtxU Γ A2) A0) A1) as Γ''.
all: remember (CtxU (CtxU (CtxU Γ A0) A2) A1) as Γ'''.
all: assert (get_vtype_i Γ' 0 = Some A0) as p_0.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ' 1 = Some A1) as p_1.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ'' 1 = Some A0) as p'_0.
all: try (rewrite HeqΓ''; simpl; f_equal).
all: assert (get_vtype_i Γ'' 2 = Some A2) as p'_2.
all: try (rewrite HeqΓ''; simpl; f_equal).
all: assert (ctx_switch_vars Γ' 1 0 A1 A0 p_1 p_0 = Γ'').
all: try (unfold ctx_switch_vars; rewrite HeqΓ'; rewrite HeqΓ''; simpl; f_equal).
all: assert (ctx_switch_vars Γ'' 2 1 A2 A0 p'_2 p'_0 = Γ''').
all: try (unfold ctx_switch_vars; rewrite HeqΓ''; rewrite HeqΓ'''; simpl; f_equal).
all: rewrite <-H0.
+ apply v_switch_typesafe. rewrite <-H.
  apply v_switch_typesafe. assumption.
+ apply c_switch_typesafe. rewrite <-H.
  apply c_switch_typesafe. assumption.
+ apply h_switch_typesafe. rewrite <-H.
  apply h_switch_typesafe. assumption.
Qed.



Fixpoint v_shift_typesafe
  (Γ:ctx) (A0:vtype) v A {struct v} :
  has_vtype Γ v A ->
  has_vtype (CtxU Γ A0) (Sub.v_shift v 1 0) A

with c_shift_typesafe
  (Γ:ctx) (A0:vtype) c C {struct c} :
  has_ctype Γ c C ->
  has_ctype (CtxU Γ A0) (Sub.c_shift c 1 0) C

with h_shift_typesafe
  (Γ:ctx) (A0:vtype) h Σ D {struct h} :
  has_htype Γ h Σ D ->
  has_htype (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D.
Proof.
{
clear v_shift_typesafe.
revert Γ A0 A. induction v; intros Γ A0 A orig; simpl; inv orig.
+ destruct v as (name, num). simpl.
  apply TypeVar. assert (num+1=S num) by omega. rewrite H.
  simpl. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv. assumption.
+ apply TypeInr. apply IHv. assumption.
+ apply TypePair. apply IHv1. assumption. apply IHv2. assumption.
+ apply TypeFun.
  specialize (c_switch10_typesafe Γ A1 A0 (Sub.c_shift c 1 0) C) as Hs.
  rewrite c_switch_1_0_shift_1_0 in Hs. auto.
+ apply TypeHandler.
  - specialize (c_switch10_typesafe Γ A1 A0 (Sub.c_shift c 1 0) D) as Hs.
    rewrite c_switch_1_0_shift_1_0 in Hs. auto.
  - apply h_shift_typesafe. assumption.
+ apply TypeVAnnot. apply IHv. assumption.
}{
clear c_shift_typesafe.
revert Γ A0 C. induction c; intros Γ A0 C orig; simpl; inv orig.
+ apply TypeRet. apply v_shift_typesafe. assumption.
+ eapply TypeΠMatch.
  - apply v_shift_typesafe. exact H4.
  - specialize (c_switch210_typesafe Γ A B A0 (Sub.c_shift c 1 0) C) as Hs.
    rewrite <-c_switch_2_1_0_shift_1_0. apply Hs.
    apply IHc. assumption.
+ eapply TypeΣMatch.
  - apply v_shift_typesafe. exact H6.
  - rewrite <-c_switch_1_0_shift_1_0. apply c_switch10_typesafe.
    apply IHc1. assumption.
  - rewrite <-c_switch_1_0_shift_1_0. apply c_switch10_typesafe.
    apply IHc2. assumption.
+ eapply TypeApp.
  - apply v_shift_typesafe. exact H2.
  - auto.
+ eapply TypeOp.
  - exact H5.
  - auto.
  - rewrite <-c_switch_1_0_shift_1_0.
    apply c_switch10_typesafe. auto.
+ apply TypeLetRec.
  - rewrite <-c_switch_2_1_0_shift_1_0.
    apply c_switch210_typesafe. auto.
  - rewrite <-c_switch_1_0_shift_1_0.
    apply c_switch10_typesafe. auto.
+ eapply TypeHandle.
  - apply v_shift_typesafe. exact H2.
  - auto.
+ apply TypeCAnnot. auto.
}{
clear h_shift_typesafe.
revert Γ Σ. induction h; intros Γ Σ orig; simpl; inv orig.
+ apply TypeCasesØ.
+ apply TypeCasesU.
  - assert (forall h', find_op_case h' o = None 
      -> find_op_case (Sub.h_shift h' 1 0) o = None).
    { intros h' orig'. induction h'. auto.
      simpl. simpl in orig'. destruct (o==o0); try discriminate || auto. }
    apply H. assumption.
  - apply IHh. assumption.
  - rewrite <-c_switch_2_1_0_shift_1_0. apply c_switch210_typesafe.
    apply c_shift_typesafe. assumption.
}
Qed.

