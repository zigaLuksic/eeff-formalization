Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export substitution Arith syntax_lemmas.
Require Import Le Compare_dec PeanoNat.


Lemma v_shift_0 (cut:nat) (v:val) :
  Sub.v_shift v 0 cut = v
with c_shift_0 (cut:nat) (c:comp) :
  Sub.c_shift c 0 cut = c
with h_shift_0 (cut:nat) (h:hcases) :
  Sub.h_shift h 0 cut = h.
Proof.
{
clear v_shift_0.
revert cut. induction v; intros cut;
simpl; try (specialize (IHv cut)); try rewrite IHv; try reflexivity.
+ destruct v. simpl. destruct (cut <=? v0); try reflexivity.
  assert (v0 + 0 = v0) by omega.
  rewrite H; reflexivity.
+ rewrite IHv1, IHv2. reflexivity.
+ rewrite c_shift_0. reflexivity.
+ f_equal; try apply c_shift_0 || apply h_shift_0.
}{
clear c_shift_0.
revert cut. induction c; intros cut; simpl;
try destruct p; f_equal;
try apply v_shift_0 || apply IHc || apply IHc1 || apply IHc2.
}{
clear h_shift_0.
revert cut. induction h; intros cut; simpl; f_equal.
reflexivity. apply IHh. apply c_shift_0.
}
Qed.


Lemma v_negshift_0 (cut:nat) (v:val) :
  Sub.v_negshift v 0 cut = v
with c_negshift_0 (cut:nat) (c:comp) :
  Sub.c_negshift c 0 cut = c
with h_negshift_0 (cut:nat) (h:hcases) :
  Sub.h_negshift h 0 cut = h.
Proof.
{
clear v_negshift_0.
revert cut. induction v; intros cut; simpl; f_equal; auto.
unfold Sub.id_down. destruct v. destruct (cut<=?v0).
+ assert (v0 - 0 = v0) by omega. rewrite H. reflexivity.
+ reflexivity.
}{
clear c_negshift_0.
revert cut. induction c; intros cut; simpl; try destruct p; f_equal;
try apply v_negshift_0 || apply IHc || apply IHc1 || apply IHc2.
}{
clear h_negshift_0.
revert cut. induction h; intros cut; simpl; f_equal. 
reflexivity. apply IHh. apply c_negshift_0.
}
Qed.


Lemma v_negshift_shift (n:nat) (m:nat) (cut:nat) (v:val) :
  (m <= n) ->
  Sub.v_negshift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n - m) cut)

with c_negshift_shift (n:nat) (m:nat) (cut:nat) (c:comp) :
  (m <= n) ->
  Sub.c_negshift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n - m) cut)

with h_negshift_shift (n:nat) (m:nat) (cut:nat) (h:hcases) :
  (m <= n) ->  
  Sub.h_negshift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n - m) cut).
Proof.
{
clear v_negshift_shift.  
revert cut. induction v; intros cut m_le_n; simpl; f_equal.
{ (* The only relevant case. *)
  destruct v as (name, db_i). simpl.
  induction (cut <=? db_i) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (cut <= db_i + 1) by omega.
    assert (cut <= db_i + n) by omega.
    apply (leb_correct _ _) in H0. rewrite H0.
    f_equal. omega.
  - rewrite cmp. reflexivity. }
all : try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : try apply c_negshift_shift || apply h_negshift_shift; assumption.
}{
clear c_negshift_shift.
revert cut. induction c; intros cut m_le_n; try destruct p; simpl; f_equal;
try apply v_negshift_shift || apply IHc || apply IHc1 || apply IHc2; assumption.
}{
clear h_negshift_shift.
revert cut. induction h; intros cut m_le_n; simpl; f_equal.
reflexivity. apply IHh. assumption. apply c_negshift_shift. assumption.
}
Qed.

Lemma v_shift_shift (n:nat) (m:nat) (cut:nat) (v:val) :
  Sub.v_shift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n + m) cut)

with c_shift_shift (n:nat) (m:nat) (cut:nat) (c:comp) :
  Sub.c_shift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n + m) cut)

with h_shift_shift (n:nat) (m:nat) (cut:nat) (h:hcases) :
  Sub.h_shift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n + m) cut).
Proof.
{
clear v_shift_shift.
revert cut. induction v; intros cut; simpl; f_equal.
{ (* The only relevant case. *)
  destruct v as (name, db_i). simpl.
  destruct (cut <=? db_i) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (cut <= db_i + n) by omega.
    apply leb_correct in H. rewrite H.
    f_equal. omega.
  - simpl. rewrite cmp. reflexivity. }
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

Lemma v_shift_makes_no_var v (j:nat):
  v_no_var_j (Sub.v_shift v 1 j) j
with c_shift_makes_no_var c (j:nat):
  c_no_var_j (Sub.c_shift c 1 j) j
with h_shift_makes_no_var h (j:nat):
  h_no_var_j (Sub.h_shift h 1 j) j.
Proof.
{
clear v_shift_makes_no_var.
revert j; induction v; intros j; simpl; auto.
destruct v as (name, num). simpl.
destruct (j<=?num) eqn:cmp.
+ apply leb_complete in cmp. omega.
+ apply leb_iff_conv in cmp. omega.
}{
revert j; induction c; intros j; try destruct p; simpl; auto.
}{
revert j; induction h; intros j; simpl; auto.
}
Qed.

Lemma v_no_var_shift (v:val) (j:nat) (cut:nat):
  v_no_var_j v j -> (cut <= j) -> 
  v_no_var_j (Sub.v_shift v 1 cut) (j+1)

with c_no_var_shift (c:comp) (j:nat) (cut:nat):
  c_no_var_j c j -> (cut <= j) -> 
  c_no_var_j (Sub.c_shift c 1 cut) (j+1)
  
with h_no_var_shift (h:hcases) (j:nat) (cut:nat):
  h_no_var_j h j -> (cut <= j) -> 
  h_no_var_j (Sub.h_shift h 1 cut) (j+1).
Proof.
{
clear v_no_var_shift.
revert j. induction v; intros j orig_clean j_le_cut; simpl; simpl in orig_clean;
try constructor || unfold Sub.id_up; auto.
+ destruct v as (name, num). simpl. simpl in orig_clean.
  destruct (cut <=? num) eqn:cmp; try rewrite leb_iff_conv in cmp; omega.
+ inv orig_clean. apply IHv1; assumption.
+ inv orig_clean. apply IHv2; assumption.
+ apply c_no_var_shift. assumption. omega. 
+ inv orig_clean. apply c_no_var_shift. assumption. omega.
+ inv orig_clean. apply h_no_var_shift; assumption.
}{
clear c_no_var_shift.
revert j cut. induction c; intros j cut orig_clean j_le_cut; simpl; simpl in *; try destruct p; try inv orig_clean; try constructor; try constructor; auto;
try apply IHc || apply IHc1 || apply IHc2; try omega; auto.
+ assert (j+1+2=j+2+1) by omega. rewrite H1. apply IHc. assumption. omega.
+ inv H0. assumption.
+ inv H0. assumption.
+ assert (j+1+2=j+2+1) by omega. rewrite H1. apply IHc1. assumption. omega.
}{
clear h_no_var_shift.
revert j cut. induction h; intros j cut orig_clean j_le_cut; simpl;
destruct orig_clean; auto. constructor.
+ apply IHh; assumption.
+ assert (j+1+2=j+2+1) by omega. rewrite H1.
  apply c_no_var_shift. assumption. omega.
}
Qed.


Lemma v_no_var_sub (v:val) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  v_no_var_j (Sub.v_sub v (j, v_s)) j

with c_no_var_sub (c:comp) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  c_no_var_j (Sub.c_sub c (j, v_s)) j

with h_no_var_sub (h:hcases) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  h_no_var_j (Sub.h_sub h (j, v_s)) j.
Proof.
{
clear v_no_var_sub.
revert j. induction v; intros j v_s_clean; simpl; try constructor;
try (apply IHv; assumption); auto.
- destruct v as (name, num). simpl.
  induction (num =? j) eqn:fits.
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
constructor.
+ apply IHh. assumption.
+ assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)).
  { apply v_no_var_shift. auto. omega. }
  apply (v_no_var_shift _ _ 0) in H. simpl in H.
  rewrite (v_shift_shift _ _ _) in H.
  assert (j+1+1=j+2) by omega. rewrite H0 in H. auto. omega.
}
Qed.
