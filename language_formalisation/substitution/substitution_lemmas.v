Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export substitution syntax_lemmas.
Require Import Arith Le PeanoNat.


Lemma v_shift_shift n m cut (v:val) :
  Sub.v_shift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n + m) cut)

with c_shift_shift n m cut (c:comp) :
  Sub.c_shift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n + m) cut)

with h_shift_shift n m cut (h:hcases) :
  Sub.h_shift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n + m) cut).
Proof.
{
clear v_shift_shift.
revert cut. induction v; intros cut; simpl; f_equal.
{ (* The only relevant case. *)
  destruct v as (name, db_i).
  destruct (cut <=? db_i) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (cut <= db_i + n) by omega.
    apply leb_correct in H. rewrite H.
    f_equal. f_equal. omega.
  - rewrite cmp. reflexivity. }
all : try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : try apply c_shift_shift || apply h_shift_shift; assumption.
}{
clear c_shift_shift.
revert cut. induction c; intros cut; try destruct p; simpl; f_equal;
try apply v_shift_shift || apply IHc || apply IHc1 || apply IHc2.
}{
clear h_shift_shift.
revert cut. induction h; intros cut; simpl; f_equal.
reflexivity. apply IHh. apply c_shift_shift.
}
Qed.

Lemma v_shift_makes_no_var v j:
  v_no_var_j (Sub.v_shift v 1 j) j
with c_shift_makes_no_var c j:
  c_no_var_j (Sub.c_shift c 1 j) j
with h_shift_makes_no_var h j:
  h_no_var_j (Sub.h_shift h 1 j) j.
Proof.
{
clear v_shift_makes_no_var.
revert j; induction v; intros j; simpl; auto.
destruct v as (name, num). simpl.
destruct (j<=?num) eqn:cmp; simpl.
+ apply leb_complete in cmp. omega.
+ apply leb_iff_conv in cmp. omega.
}{
revert j; induction c; intros j; try destruct p; simpl; auto.
}{
revert j; induction h; intros j; simpl; auto.
}
Qed.

Lemma v_no_var_shift (v:val) j cut:
  v_no_var_j v j -> (cut <= j) -> v_no_var_j (Sub.v_shift v 1 cut) (j+1)

with c_no_var_shift (c:comp) j cut:
  c_no_var_j c j -> (cut <= j) -> c_no_var_j (Sub.c_shift c 1 cut) (j+1)
  
with h_no_var_shift (h:hcases) j cut:
  h_no_var_j h j -> (cut <= j) -> h_no_var_j (Sub.h_shift h 1 cut) (j+1).
Proof.
{
clear v_no_var_shift.
revert j. induction v; intros j orig_clean j_le_cut; simpl; simpl in orig_clean;
try constructor; try inv orig_clean; auto.
+ destruct v as (name, num). destruct (cut <=? num) eqn:cmp; simpl;
  try rewrite leb_iff_conv in cmp; omega.
+ apply c_no_var_shift. assumption. omega. 
+ apply c_no_var_shift. assumption. omega.
}{
clear c_no_var_shift.
revert j cut. induction c; intros j cut orig_clean j_le_cut; simpl; simpl in *; 
try destruct p; try inv orig_clean; try constructor; try constructor; auto;
try apply IHc || apply IHc1 || apply IHc2; try omega; auto.
+ assert (j+1+2=j+2+1) by omega. rewrite H1. apply IHc. assumption. omega.
+ inv H0. assumption.
+ inv H0. assumption.
+ assert (j+1+2=j+2+1) by omega. rewrite H1. apply IHc1. assumption. omega.
}{
clear h_no_var_shift.
revert j cut. induction h; intros j cut orig_clean j_le_cut; simpl;
destruct orig_clean; auto. constructor. auto.
assert (j+1+2=j+2+1) by omega. rewrite H1.
apply c_no_var_shift. assumption. omega.
}
Qed.


Lemma v_no_var_sub (v:val) j v_s :
  v_no_var_j v_s j -> v_no_var_j (Sub.v_sub v (j, v_s)) j

with c_no_var_sub (c:comp) j v_s :
  v_no_var_j v_s j -> c_no_var_j (Sub.c_sub c (j, v_s)) j

with h_no_var_sub (h:hcases) j v_s :
  v_no_var_j v_s j -> h_no_var_j (Sub.h_sub h (j, v_s)) j.
Proof.
{
clear v_no_var_sub.
revert j. induction v; intros j v_s_clean; simpl; try constructor;
try (apply IHv; assumption); auto.
- destruct v as (x, n). simpl.
  induction (n =? j) eqn:fits.
  + assumption.
  + simpl. apply Nat.eqb_neq in fits. omega.
- apply c_no_var_sub. apply v_no_var_shift. assumption. omega.
- apply c_no_var_sub. apply v_no_var_shift. assumption. omega.
}{
clear c_no_var_sub.
revert j v_s. induction c; intros j v_s v_s_clean; simpl; try constructor;
try destruct p; simpl; try constructor; auto;
try apply IHc || apply IHc1 || apply IHc2;
try (apply v_no_var_shift; assumption || omega).
all:
assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)) by
  (apply v_no_var_shift; auto || omega);
apply (v_no_var_shift _ _ 0) in H; try omega;
simpl in H; rewrite v_shift_shift in H; simpl in H;
assert (j+1+1=j+2) by omega; rewrite H0 in H; assumption.
}{
clear h_no_var_sub.
revert j v_s. induction h; intros j v_s v_s_clean; simpl; auto.
constructor. auto.
assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)).
{ apply v_no_var_shift. auto. omega. }
apply (v_no_var_shift _ _ 0) in H. simpl in H.
rewrite (v_shift_shift _ _ _) in H.
assert (j+1+1=j+2) by omega. rewrite H0 in H. auto. omega.
}
Qed.