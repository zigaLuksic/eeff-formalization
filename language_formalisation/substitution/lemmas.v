Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export substitution Arith.
Require Import Le Compare_dec.

Module SubLemma.

(* Main lemmas *)
Lemma vzero_shift (cut:nat) (v:val) :
  Sub.v_shift v 0 cut = v
with czero_shift (cut:nat) (c:comp) :
  Sub.c_shift c 0 cut = c
with hzero_shift (cut:nat) (h:hcases) :
  Sub.h_shift h 0 cut = h.
Proof.
{
clear vzero_shift.
revert cut. induction v; intros cut;
simpl; try (specialize (IHv cut)); try rewrite IHv; try reflexivity.
+ destruct v. simpl.
  induction (cut <=? v0).
  assert (forall n, n + 0 = n).
  intro n. induction n; simpl; try rewrite IHn; reflexivity.
  specialize (H v0).
  rewrite H; reflexivity. reflexivity.
+ specialize (IHv1 cut). rewrite IHv1.
  specialize (IHv2 cut). rewrite IHv2.
  reflexivity.
+ rewrite (czero_shift (cut+1) c). reflexivity.
+ rewrite (czero_shift (cut+1) c). rewrite (hzero_shift cut h). reflexivity.
}
{
clear czero_shift.
revert cut. induction c; intros cut; simpl; try (rewrite (vzero_shift cut v)).
+ reflexivity.
+ destruct p. simpl.
  specialize (IHc (cut+2)). rewrite IHc. reflexivity.
+ specialize (IHc1 (cut+1)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ rewrite (vzero_shift cut v0). reflexivity.
+ specialize (IHc (cut+1)). rewrite IHc. reflexivity.
+ specialize (IHc1 (cut+2)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ specialize (IHc1 (cut)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ specialize (IHc cut). rewrite IHc. reflexivity.
+ specialize (IHc cut). rewrite IHc. reflexivity. 
}
{
clear hzero_shift.
revert cut. induction h; intros cut; simpl.
+ reflexivity.
+ rewrite (czero_shift (cut+2) c).
  specialize (IHh cut). rewrite IHh.
  reflexivity.
}
Qed.


Lemma vzero_negshift (cut:nat) (v:val) :
  Sub.v_negshift v 0 cut = v
with czero_negshift (cut:nat) (c:comp) :
  Sub.c_negshift c 0 cut = c
with hzero_negshift (cut:nat) (h:hcases) :
  Sub.h_negshift h 0 cut = h.
Proof.
{
clear vzero_negshift.
revert cut. induction v; intros cut;
simpl; try (specialize (IHv cut)); try rewrite IHv; try reflexivity.
+ destruct v. simpl.
  induction (cut <=? v0).
  assert (v0 - 0 = v0) by omega.
  rewrite H; reflexivity. reflexivity.
+ specialize (IHv1 cut). rewrite IHv1.
  specialize (IHv2 cut). rewrite IHv2.
  reflexivity.
+ rewrite (czero_negshift (cut+1) c). reflexivity.
+ rewrite (czero_negshift (cut+1) c). rewrite (hzero_negshift cut h). reflexivity.
}
{
clear czero_negshift.
revert cut. induction c; intros cut; simpl; try (rewrite (vzero_negshift cut v)).
+ reflexivity.
+ destruct p. simpl.
  specialize (IHc (cut+2)). rewrite IHc. reflexivity.
+ specialize (IHc1 (cut+1)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ rewrite (vzero_negshift cut v0). reflexivity.
+ specialize (IHc (cut+1)). rewrite IHc. reflexivity.
+ specialize (IHc1 (cut+2)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ specialize (IHc1 (cut)). rewrite IHc1.
  specialize (IHc2 (cut+1)). rewrite IHc2.
  reflexivity.
+ specialize (IHc cut). rewrite IHc. reflexivity.
+ specialize (IHc cut). rewrite IHc. reflexivity. 
}
{
clear hzero_negshift.
revert cut. induction h; intros cut; simpl.
+ reflexivity.
+ rewrite (czero_negshift (cut+2) c).
  specialize (IHh cut). rewrite IHh.
  reflexivity.
}
Qed.


Lemma vshifts_cancel (n:nat) (m:nat) (cut:nat) (v:val) :
  (m <= n) ->
  Sub.v_negshift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n - m) cut)

with cshifts_cancel (n:nat) (m:nat) (cut:nat) (c:comp) :
  (m <= n) ->
  Sub.c_negshift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n - m) cut)

with hshifts_cancel (n:nat) (m:nat) (cut:nat) (h:hcases) :
  (m <= n) ->  
  Sub.h_negshift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n - m) cut).
Proof.
{
clear vshifts_cancel.  
revert cut.
induction v; intros cut m_le_n; simpl.
{ (* The only relevant case. *)
  f_equal.
  destruct v as (name, db_i). simpl.
  remember (cut <=? db_i) as cmp.
  induction cmp.
  - simpl. assert (cut <= db_i + 1).
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       omega.
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       assert (cut <= db_i + n) by omega.
       apply (leb_correct _ _) in H0. rewrite H0.
       f_equal. omega.
  - simpl. rewrite <-Heqcmp. reflexivity. }
all : f_equal; try reflexivity;
try specialize (IHv cut m_le_n); try assumption.
+ specialize (IHv1 cut m_le_n). assumption.
+ specialize (IHv2 cut m_le_n). assumption.
+ rewrite (cshifts_cancel n m (cut+1) c m_le_n). reflexivity.
+ rewrite (cshifts_cancel n m (cut+1) c m_le_n). reflexivity.
+ rewrite (hshifts_cancel n m cut h m_le_n). reflexivity.
}
{
clear cshifts_cancel.
revert cut.
induction c; intros cut m_le_n; simpl; try f_equal;
(* get rid of values *)
try rewrite (vshifts_cancel n m cut v m_le_n); try reflexivity;
(* get rid of trivial specialize cases *)
try specialize (IHc cut m_le_n) as SIHc; try assumption;
try specialize (IHc2 (cut+1) m_le_n) as SIHc2; try assumption.
(* dispatch the rest *)
+ destruct p. simpl. f_equal.
  rewrite (vshifts_cancel n m cut v m_le_n). reflexivity.
  specialize (IHc (cut+2) m_le_n). assumption.
+ specialize (IHc1 (cut+1) m_le_n). assumption.
+ rewrite (vshifts_cancel n m cut v0 m_le_n). reflexivity.
+ specialize (IHc (cut+1) m_le_n). assumption.
+ specialize (IHc1 (cut+2) m_le_n). assumption.
+ specialize (IHc1 cut m_le_n). assumption.
}
{
clear hshifts_cancel.
revert cut.
induction h; intros cut m_le_n; simpl.
reflexivity.
f_equal.
+ specialize (IHh cut m_le_n). assumption.
+ rewrite (cshifts_cancel n m (cut+2) c m_le_n). reflexivity.
}
Qed.

Lemma vshifts_add (n:nat) (m:nat) (cut:nat) (v:val) :
  Sub.v_shift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n + m) cut)

with cshifts_add (n:nat) (m:nat) (cut:nat) (c:comp) :
  Sub.c_shift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n + m) cut)

with hshifts_add (n:nat) (m:nat) (cut:nat) (h:hcases) :
  Sub.h_shift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n + m) cut).
Proof.
{
clear vshifts_add.
revert cut.
induction v; intros cut; simpl.
{ (* The only relevant case. *)
  f_equal.
  destruct v as (name, db_i). simpl.
  remember (cut <=? db_i) as cmp.
  induction cmp.
  - simpl. assert (cut <= db_i + 1).
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       assert (forall n, n + 1 = S n).
       intro. induction n0. auto. simpl. rewrite IHn0. auto.
       rewrite (H db_i).
       apply (le_n_S _ _) in Heqcmp. apply (le_Sn_le _ _) in Heqcmp.
       assumption.
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       assert (cut <= db_i + n) by omega.
       apply (leb_correct _ _) in H0. rewrite H0.
       f_equal. omega.
  - simpl. rewrite <-Heqcmp. reflexivity. }
all : f_equal; try reflexivity;
try specialize (IHv cut); try assumption.
+ specialize (IHv1 cut). assumption.
+ specialize (IHv2 cut). assumption.
+ rewrite (cshifts_add n m (cut+1) c). reflexivity.
+ rewrite (cshifts_add n m (cut+1) c). reflexivity.
+ rewrite (hshifts_add n m cut h). reflexivity.
}
{
clear cshifts_add.
revert cut.
induction c; intros cut; simpl; try f_equal;
(* get rid of values *)
try rewrite (vshifts_add n m cut v); try reflexivity;
(* get rid of trivial specialize cases *)
try specialize (IHc cut) as SIHc; try assumption;
try specialize (IHc2 (cut+1)) as SIHc2; try assumption.
(* dispatch the rest *)
+ destruct p. simpl. f_equal.
  rewrite (vshifts_add n m cut v). reflexivity.
  specialize (IHc (cut+2)). assumption.
+ specialize (IHc1 (cut+1)). assumption.
+ rewrite (vshifts_add n m cut v0). reflexivity.
+ specialize (IHc (cut+1)). assumption.
+ specialize (IHc1 (cut+2)). assumption.
+ specialize (IHc1 cut). assumption.
}
{
clear hshifts_add.
revert cut.
induction h; intros cut; simpl.
reflexivity.
f_equal.
+ specialize (IHh cut). assumption.
+ rewrite (cshifts_add n m (cut+2) c). reflexivity.
}
Qed.

Lemma vshift_moves_empty (v:val) (j:nat) (cut:nat):
  v_no_var_j v j -> (cut <= j) -> 
  v_no_var_j (Sub.v_shift v 1 cut) (j+1)

with cshift_moves_empty (c:comp) (j:nat) (cut:nat):
  c_no_var_j c j -> (cut <= j) -> 
  c_no_var_j (Sub.c_shift c 1 cut) (j+1)
  
with hshift_moves_empty (h:hcases) (j:nat) (cut:nat):
  h_no_var_j h j -> (cut <= j) -> 
  h_no_var_j (Sub.h_shift h 1 cut) (j+1).
Proof.
all: 
rename vshift_moves_empty into v_lemma;
rename cshift_moves_empty into c_lemma;
rename hshift_moves_empty into h_lemma.
{
clear v_lemma.
revert j. induction v; intros j orig_clean j_le_cut; simpl; auto.
+ destruct v as (name, num). simpl. simpl in orig_clean.
  remember (cut <=? num) as cmp. induction cmp.
  - omega.
  - apply eq_sym in Heqcmp. rewrite leb_iff_conv in Heqcmp.
    omega.
+ simpl in orig_clean. destruct orig_clean as (H1, H2). constructor.
  - specialize (IHv1 j H1 j_le_cut). assumption.
  - specialize (IHv2 j H2 j_le_cut). assumption.
+ simpl in orig_clean.
  assert (cut + 1 <= j + 1) by omega. 
  specialize (c_lemma c (j+1) (cut+1) orig_clean H).
  assumption.
+ simpl in orig_clean. destruct orig_clean as (H1, H2). constructor.
  - assert (cut + 1 <= j + 1) by omega. 
    specialize (c_lemma c (j+1) (cut+1) H1 H).
    assumption.
  - apply h_lemma; assumption. 
}
{
clear c_lemma.
revert j cut. induction c; intros j cut orig_clean j_le_cut; simpl;
simpl in orig_clean; try destruct orig_clean; try constructor; auto.
+ destruct p as (name, num). simpl.
  specialize (IHc (j + 2) (cut + 2) orig_clean).
  assert (cut + 2 <= j + 2) by omega. specialize (IHc H).
  assert (j + 1 + 2 = j + 2 + 1) by omega. rewrite H0.
  assumption.
+ apply (IHc1 (j+1) (cut+1)). assumption.
  assert (cut + 1 <= j + 1) by omega. assumption.
+ apply (IHc2 (j+1) (cut+1)). assumption.
  assert (cut + 1 <= j + 1) by omega. assumption.
+ apply (IHc (j+1) (cut+1)). assumption.
  assert (cut + 1 <= j + 1) by omega. assumption.
+ specialize (IHc1 (j+2) (cut+2) H).
  assert (cut + 2 <= j + 2) by omega. specialize (IHc1 H1).
  assert (j + 1 + 2 = j + 2 + 1) by omega. rewrite H2. assumption.
+ apply IHc2. auto. assert (cut + 1 <= j + 1) by omega. auto.
+ apply IHc2. auto. assert (cut + 1 <= j + 1) by omega. auto.
}
{
clear h_lemma.
revert j cut. induction h; intros j cut orig_clean j_le_cut; simpl;
destruct orig_clean; auto. constructor.
+ apply IHh. auto. auto.
+ assert (cut+2<=j+2) by omega.
  specialize (c_lemma c (j+2) (cut+2) H0 H1).
  assert (j + 1 + 2 = j + 2 + 1) by omega. rewrite H2. assumption.
}
Qed.

Lemma v_sub_j_removes_j (v:val) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  v_no_var_j (Sub.v_sub v (j, v_s)) j

with c_sub_j_removes_j (c:comp) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  c_no_var_j (Sub.c_sub c (j, v_s)) j

with h_sub_j_removes_j (h:hcases) (j:nat) (v_s:val) :
  v_no_var_j v_s j ->
  h_no_var_j (Sub.h_sub h (j, v_s)) j.
Proof.
all:
rename v_sub_j_removes_j into v_lemma;
rename c_sub_j_removes_j into c_lemma;
rename h_sub_j_removes_j into h_lemma.
{
clear v_lemma.
revert j. induction v; intros j v_s_clean; simpl;
try specialize (IHv j v_s_clean) as sIHv; try assumption; try auto.
- destruct v as (name, num). simpl.
  remember (num =? j) as fits.
  induction fits.
  + assumption.
  + simpl. apply eq_sym in Heqfits as H.
    apply (beq_nat_false) in H. apply not_eq_sym. assumption.
- apply c_lemma. apply vshift_moves_empty. auto. omega.
- constructor.
  + apply c_lemma. apply vshift_moves_empty. auto. omega.
  + apply h_lemma. assumption.
}
{
clear c_lemma.
revert j v_s. induction c; intros j v_s v_s_clean; simpl; try constructor; auto.
{ destruct p as (name, num). simpl.
  apply IHc.
  assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)).
  { apply vshift_moves_empty. auto. omega. }
  apply (vshift_moves_empty _ _ 0) in H.
  simpl in H. rewrite (vshifts_add _ _ _) in H.
  assert (1+1=2) by omega. rewrite H0 in H.
  assert (j+1+1=j+2) by omega. rewrite H1 in H.
  auto. omega. }
all: try apply IHc; try apply IHc1; try apply IHc2;
try apply vshift_moves_empty; auto; try omega.
+ assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)).
  { apply vshift_moves_empty. auto. omega. }
  apply (vshift_moves_empty _ _ 0) in H.
  simpl in H. rewrite (vshifts_add _ _ _) in H.
  assert (1+1=2) by omega. rewrite H0 in H.
  assert (j+1+1=j+2) by omega. rewrite H1 in H.
  auto. omega.
}
{
clear h_lemma.
revert j v_s. induction h; intros j v_s v_s_clean; simpl; auto.
constructor.
+ apply IHh. assumption.
+ assert (v_no_var_j (Sub.v_shift v_s 1 0) (j + 1)).
  { apply vshift_moves_empty. auto. omega. }
  apply (vshift_moves_empty _ _ 0) in H.
  simpl in H. rewrite (vshifts_add _ _ _) in H.
  assert (1+1=2) by omega. rewrite H0 in H.
  assert (j+1+1=j+2) by omega. rewrite H1 in H.
  auto. omega.
}
Qed.

End SubLemma.