Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export substitution Arith syntax_lemmas.
Require Import Le Compare_dec PeanoNat.


(* Main lemmas *)
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
  remember (cut <=? db_i) as cmp. induction cmp; simpl.
  - apply eq_sym in Heqcmp.
    apply (leb_complete _ _) in Heqcmp.
    assert (cut <= db_i + 1) by omega.
    assert (cut <= db_i + n) by omega.
    apply (leb_correct _ _) in H0. rewrite H0.
    f_equal. omega.
  - rewrite <-Heqcmp. reflexivity. }
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
  remember (cut <=? db_i) as cmp. destruct cmp; simpl.
  - apply eq_sym in Heqcmp.
    apply (leb_complete _ _) in Heqcmp.
    assert (cut <= db_i + n) by omega.
    apply leb_correct in H. rewrite H.
    f_equal. omega.
  - simpl. rewrite <-Heqcmp. reflexivity. }
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
  remember (cut <=? num) as cmp. destruct cmp.
  - omega.
  - apply eq_sym in Heqcmp. rewrite leb_iff_conv in Heqcmp. omega.
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
  remember (num =? j) as fits. induction fits.
  + assumption.
  + simpl. apply eq_sym in Heqfits as H.
    apply (beq_nat_false) in H. omega.
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

Lemma v_switch_shift v i j d cut:
  cut <= i -> cut <= j ->
  v_switch_vars (Sub.v_shift v d cut) (i + d) (j + d) 
    =
  Sub.v_shift (v_switch_vars v i j) d cut
with c_switch_shift c i j d cut:
  cut <= i -> cut <= j ->
  c_switch_vars (Sub.c_shift c d cut) (i + d) (j + d) 
    =
  Sub.c_shift (c_switch_vars c i j) d cut
with h_switch_shift h i j d cut:
  cut <= i -> cut <= j ->
  h_switch_vars (Sub.h_shift h d cut) (i + d) (j + d) 
    =
  Sub.h_shift (h_switch_vars h i j) d cut.
Proof.
all: revert i j.
{
induction v; intros i j cuti cutj; simpl; try f_equal; try reflexivity; simpl;
try apply IHv || apply IHv1 || apply IHv2 || apply h_switch_shift; try omega.
{
destruct v as (name, n). simpl.

remember (cut<=?n) as cut_n. destruct cut_n;
remember (n=?i) as n_i; destruct n_i; simpl;
apply leb_correct in cutj; try rewrite cutj; simpl.
+ apply beq_nat_eq in Heqn_i. rewrite Heqn_i. rewrite <-beq_nat_refl. auto.
+ assert (n+d =? i+d = false).
  - apply beq_nat_false_iff. apply eq_sym in Heqn_i. 
    apply beq_nat_false_iff in Heqn_i. omega.
  - rewrite H.
    remember (n=?j) as n_j; destruct n_j; simpl.
    * apply beq_nat_eq in Heqn_j. rewrite Heqn_j. rewrite <-beq_nat_refl.
      assert (cut <=? i = true).
      { apply leb_correct. assumption. }
      rewrite H0. reflexivity.
    * assert (n+d =? j+d = false).
      -- apply beq_nat_false_iff. apply eq_sym in Heqn_j. 
         apply beq_nat_false_iff in Heqn_j. omega.
      -- rewrite H0. rewrite <-Heqcut_n. reflexivity.
+ apply beq_nat_eq in Heqn_i. rewrite Heqn_i.
  remember (d=?0) as d0. destruct d0.
  - apply beq_nat_eq in Heqd0. rewrite Heqd0.
    assert (i =? i+0 = true).
    { apply beq_nat_true_iff. omega. }
    rewrite H. reflexivity.
  - rewrite Heqn_i in Heqcut_n. apply leb_correct in cuti.
    rewrite cuti in Heqcut_n. discriminate.
+ remember (n=?j) as nj. destruct nj.
  - apply beq_nat_eq in Heqnj. rewrite <-Heqnj in cutj.
    rewrite cutj in Heqcut_n. discriminate.
  - remember (n=?j+d) as njd. destruct njd.
    * apply beq_nat_eq in Heqnjd. rewrite Heqnjd in Heqcut_n.
      apply leb_complete in cutj.
      assert ((cut <=? j + d) = true).
      apply leb_correct. omega.
      rewrite H in Heqcut_n. discriminate.
    * remember (n=?i+d) as nid. destruct nid.
      ** apply beq_nat_eq in Heqnid. rewrite Heqnid in Heqcut_n.
        assert ((cut <=? i + d) = true).
        apply leb_correct. omega.
        rewrite H in Heqcut_n. discriminate.
      ** simpl. rewrite <-Heqcut_n. reflexivity.
}
all: assert (i+d+1=i+1+d) by omega.
all: assert (j+d+1=j+1+d) by omega;
rewrite H, H0; apply c_switch_shift; omega.
}{
revert cut.
induction c; intros cut i j cuti cutj; try destruct p as (name, num); simpl;
try f_equal; try apply IHc || apply v_switch_shift || apply IHc1; try omega.
all:
  assert (i+d+1=i+1+d) as id1 by omega;
  assert (j+d+1=j+1+d) as jd1 by omega;
  assert (i+d+2=i+2+d) as id2 by omega;
  assert (j+d+2=j+2+d) as jd2 by omega;
  try rewrite id1, jd1; try rewrite id2, jd2;
  try apply IHc || apply IHc1 || apply IHc2; omega.
}{
revert cut. induction h; intros cut i j cuti cutj; simpl.
reflexivity.
f_equal.
+ apply IHh; omega.
+ assert (i+d+2=i+2+d) as id2 by omega.
  assert (j+d+2=j+2+d) as jd2 by omega.
  rewrite id2, jd2. apply c_switch_shift; omega.
}
Qed.

Lemma v_sub_switch v v_s i j:
  Sub.v_sub (v_switch_vars v i j) (i, v_s)
    =
  v_switch_vars (Sub.v_sub v (j, v_switch_vars v_s i j)) i j
with c_sub_switch c v_s i j:
  Sub.c_sub (c_switch_vars c i j) (i, v_s)
    =
  c_switch_vars (Sub.c_sub c (j, v_switch_vars v_s i j)) i j
with h_sub_switch h v_s i j:
  Sub.h_sub (h_switch_vars h i j) (i, v_s)
    =
  h_switch_vars (Sub.h_sub h (j, v_switch_vars v_s i j)) i j.
Proof.
all: revert i j.
{
clear v_sub_switch. induction v; intros i j; simpl; try reflexivity;
try f_equal; try apply IHv || apply IHv1 || apply IHv2.
+ destruct v as (name, num). simpl.
  remember (num=?i) as cmpi. destruct cmpi.
  - apply beq_nat_eq in Heqcmpi. rewrite Heqcmpi. simpl.
    remember (j=?i) as cmp. destruct cmp.
    * apply beq_nat_eq in Heqcmp. rewrite Heqcmp. rewrite <-beq_nat_refl.
      rewrite v_switch_ii. rewrite v_switch_ii. reflexivity.
    * apply eq_sym in Heqcmp. rewrite beq_nat_false_iff in Heqcmp.
      apply not_eq_sym in Heqcmp. rewrite <-beq_nat_false_iff in Heqcmp.
      rewrite Heqcmp. simpl. rewrite <-beq_nat_refl. reflexivity.
  - simpl. remember (num=?j) as cmpj. destruct cmpj.
    * simpl. rewrite <-beq_nat_refl. rewrite v_switchswitch. reflexivity.
    * simpl. rewrite <-Heqcmpi. rewrite <-Heqcmpj. reflexivity.
+ specialize (c_sub_switch c (Sub.v_shift v_s 1 0) (i+1) (j+1)).
  rewrite c_sub_switch. f_equal. f_equal. f_equal. apply v_switch_shift; omega.
+ specialize(c_sub_switch c (Sub.v_shift v_s 1 0) (i+1) (j+1)).
  rewrite c_sub_switch. f_equal. f_equal. f_equal. apply v_switch_shift; omega.
+ apply h_sub_switch.
}
{
clear c_sub_switch.
revert v_s. induction c; intros v_s i j; try destruct p as (name, num); 
simpl; f_equal; try apply v_sub_switch || apply IHc || apply IHc1;
try rewrite IHc || rewrite IHc1 || rewrite IHc2;
f_equal; f_equal; f_equal; apply v_switch_shift; omega.
}{
clear h_sub_switch.
induction h; intros i j; simpl; f_equal; try auto.
rewrite c_sub_switch. f_equal. f_equal. f_equal.
apply v_switch_shift; omega.
}
Qed.