(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Export Arith syntax.
Require Import Le Compare_dec.

Lemma gets_same Γ (id:var_id) (db_i:nat) :
  id_has_dbi id db_i = true -> get_vtype Γ id = get_vtype_i Γ db_i.
Proof.
revert id db_i. induction Γ; intros id db_i matches; destruct id as (name, num).
+ auto.
+ simpl in matches. apply beq_nat_true in matches.
  rewrite matches. simpl. auto.
Qed.

Lemma get_in_changed_other Γ j k αj :
  j <> k -> get_vtype_i Γ k = get_vtype_i (ctx_change_var Γ j αj) k.
Proof.
revert j k. induction Γ; intros j k neq_jk.
auto.
simpl.
destruct k.
+ destruct j; auto.
  apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ destruct j; auto.
  simpl. apply IHΓ. omega.
Qed.

Lemma get_in_changed_same Γ j αj_orig αj 
  (p_j : get_vtype_i Γ j = Some αj_orig) :
  get_vtype_i (ctx_change_var Γ j αj) j = Some αj.
Proof.
revert j p_j. induction Γ; intros j p_j.
+ simpl in p_j. discriminate.
+ destruct j; auto. simpl.
  apply IHΓ. simpl in p_j. assumption.
Qed.

Lemma get_in_switched_other Γ k i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  i <> k -> j <> k ->
  get_vtype_i Γ k = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) k.
Proof.
revert k i j p_i p_j. induction Γ;
intros k i j p_i p_j neq_ik neq_jk.
auto.
revert i j p_i p_j neq_ik neq_jk. destruct k;
intros i j p_i p_j neq_ik neq_jk.
+ destruct i.
  - apply beq_nat_false_iff in neq_ik. simpl in neq_ik. discriminate.
  - simpl. destruct j; auto.
    apply beq_nat_false_iff in neq_jk. simpl in neq_jk. discriminate.
+ destruct i.
  - destruct j; auto.
    simpl. apply get_in_changed_other. omega.
  - destruct j; simpl.
    * apply get_in_changed_other. omega.
    * unfold ctx_switch_vars in IHΓ. apply IHΓ.
      auto. auto. omega. omega.
Qed.
      
Lemma get_in_switched_i Γ i j αi αj
  (p_i : get_vtype_i Γ i = Some αi) (p_j : get_vtype_i Γ j = Some αj) :
  get_vtype_i Γ i = get_vtype_i (ctx_switch_vars Γ i j αi αj p_i p_j) j.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_i. rewrite p_i.
  apply (get_in_changed_same Γ j αj). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.