(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
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

destruct (cut<=?n) eqn:cut_n;
destruct (n=?i) eqn:n_i; simpl;
apply leb_correct in cutj; try rewrite cutj; simpl.
+ apply Nat.eqb_eq in n_i. rewrite n_i. rewrite <-beq_nat_refl. auto.
+ assert (n+d =? i+d = false).
  - apply Nat.eqb_neq. apply Nat.eqb_neq in n_i. omega.
  - rewrite H.
    destruct (n=?j) eqn:n_j; simpl.
    * apply Nat.eqb_eq in n_j. rewrite n_j. rewrite <-beq_nat_refl.
      assert (cut <=? i = true).
      { apply leb_correct. assumption. }
      rewrite H0. reflexivity.
    * assert (n+d =? j+d = false).
      -- apply Nat.eqb_neq. apply Nat.eqb_neq in n_j. omega.
      -- rewrite H0. rewrite cut_n. reflexivity.
+ apply Nat.eqb_eq in n_i. rewrite n_i.
  destruct (d=?0) eqn:d0.
  - apply Nat.eqb_eq in d0. rewrite d0.
    assert (i =? i+0 = true).
    { apply Nat.eqb_eq. omega. }
    rewrite H. reflexivity.
  - rewrite n_i in cut_n. apply leb_correct in cuti.
    rewrite cuti in cut_n. discriminate.
+ destruct (n=?j) eqn:nj.
  - apply Nat.eqb_eq in nj. rewrite <-nj in cutj.
    rewrite cutj in cut_n. discriminate.
  - destruct (n=?j+d) eqn:njd.
    * apply Nat.eqb_eq in njd. rewrite njd in cut_n.
      apply leb_complete in cutj.
      assert ((cut <=? j + d) = true).
      apply leb_correct. omega.
      rewrite H in cut_n. discriminate.
    * destruct (n=?i+d) eqn:nid.
      ** apply Nat.eqb_eq in nid. rewrite nid in cut_n.
        assert ((cut <=? i + d) = true).
        apply leb_correct. omega.
        rewrite H in cut_n. discriminate.
      ** simpl. rewrite cut_n. reflexivity.
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
  destruct (num=?i) eqn:cmpi.
  - apply Nat.eqb_eq in cmpi. rewrite cmpi. simpl.
    destruct (j=?i) eqn:cmp.
    * apply Nat.eqb_eq in cmp. rewrite cmp. rewrite <-beq_nat_refl.
      rewrite v_switch_ii. rewrite v_switch_ii. reflexivity.
    * rewrite Nat.eqb_neq in cmp.
      apply not_eq_sym in cmp. rewrite <-Nat.eqb_neq in cmp.
      rewrite cmp. simpl. rewrite <-beq_nat_refl. reflexivity.
  - simpl. destruct (num=?j) eqn:cmpj.
    * simpl. rewrite <-beq_nat_refl. rewrite v_switchswitch. reflexivity.
    * simpl. rewrite cmpi. rewrite cmpj. reflexivity.
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

Lemma v_switch_Si_i_shift_1 v i:
  v_switch_vars (Sub.v_shift v 1 (S i)) (S i) i = Sub.v_shift v 1 i
with c_switch_Si_i_shift_1 c i:
  c_switch_vars (Sub.c_shift c 1 (S i)) (S i) i = Sub.c_shift c 1 i
with h_switch_Si_i_shift_1 h i:
  h_switch_vars (Sub.h_shift h 1 (S i)) (S i) i = Sub.h_shift h 1 i.
Proof.
{
clear v_switch_Si_i_shift_1.
revert i. induction v; intros i; simpl.
{
destruct v as (name, n). simpl.
destruct n; simpl.
+ destruct i; auto.
+ destruct (i <=? n) eqn:cmp; simpl.
  - apply leb_complete in cmp.
    assert (n + 1 <> i) by omega.
    rewrite <-Nat.eqb_neq in H. rewrite H.
    assert (i <= S n) by omega. apply leb_correct in H0. rewrite H0.
    destruct i; auto.
    assert (n + 1 <> i) by omega.
    rewrite <-Nat.eqb_neq in H1. rewrite H1. auto.
  - apply leb_iff_conv in cmp.
    assert (n<>i) by omega. rewrite <-Nat.eqb_neq in H. rewrite H.
    destruct (i =? S n) eqn:iSn. 
    * rewrite Nat.eqb_eq in iSn.
      assert (i<=S n) by omega. apply leb_correct in H0. rewrite H0.
      rewrite iSn. assert (true = (n =? n)) by apply beq_nat_refl.
      rewrite <-H1. f_equal. f_equal. omega.
    * rewrite Nat.eqb_neq in iSn.
      assert (i > S n) by omega. apply leb_iff_conv in H0. rewrite H0.
      destruct i; auto.
      assert (n<>i) by omega. apply Nat.eqb_neq in H1. rewrite H1. auto.
}
all: f_equal; auto.
}{
clear c_switch_Si_i_shift_1.
revert i. induction c; intros i; try destruct p; simpl; f_equal; auto.
}{
clear h_switch_Si_i_shift_1.
revert i. induction h; intros i; simpl; f_equal; auto.
}
Qed.

 
Lemma v_switch_SSi_Si_i_shift_1 v i:
  (v_switch_vars (v_switch_vars (Sub.v_shift v 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.v_shift v 1 (S (S i))
with c_switch_SSi_Si_i_shift_1 c i:
  (c_switch_vars (c_switch_vars (Sub.c_shift c 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.c_shift c 1 (S (S i))
with h_switch_SSi_Si_i_shift_1 h i:
  (h_switch_vars (h_switch_vars (Sub.h_shift h 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.h_shift h 1 (S (S i)).
Proof.
{
clear v_switch_SSi_Si_i_shift_1.
revert i. induction v; intros i; simpl.
{
destruct v as (name, n). simpl.
destruct (i <=? n) eqn:cmp; simpl.
+ destruct (n+1=?S i) eqn:eqSnSi; simpl.
  - apply Nat.eqb_eq in eqSnSi.
    assert (n+1=S n) by omega. rewrite H in eqSnSi.
    assert (i=n) by omega. rewrite H0.
    assert (n <> S (S n)) by omega. apply Nat.eqb_neq in H1. rewrite H1.
    assert (n <> S n) by omega. apply Nat.eqb_neq in H2. rewrite H2.
    destruct n; auto.
    destruct n; auto.
    assert (n < S (S n)) by omega. apply leb_iff_conv in H3. rewrite H3. auto.
  - apply leb_complete in cmp.
    assert (n+1 <> i) by omega. apply Nat.eqb_neq in H. rewrite H. simpl.
    destruct (n+1=?S(S i)) eqn:eqSnSSi; simpl.
    * apply Nat.eqb_eq in eqSnSSi.
      assert (n+1= S n) by omega. rewrite H0 in eqSnSSi. injection eqSnSSi.
      intro eq. rewrite eq. rewrite eq in *.
      destruct i. auto.
      assert (S i > i) by omega. apply leb_iff_conv in H1. rewrite H1. auto.
    * rewrite eqSnSi. destruct n.
      ++ assert (i=0) by omega. rewrite H0 in *. simpl in *. discriminate.
      ++ destruct n.
        ** apply Nat.eqb_neq in eqSnSi.
           assert (i = 0) by omega. rewrite H0 in *. simpl in *. discriminate.
        ** apply Nat.eqb_neq in eqSnSi. apply Nat.eqb_neq in eqSnSSi.
           assert (i<=n) by omega. apply leb_correct in H0. rewrite H0. auto.
+ apply leb_iff_conv in cmp.
  assert (n <> i) by omega. apply Nat.eqb_neq in H as Hneq.
  assert (n <> S i) by omega. apply Nat.eqb_neq in H0 as HSneq.
  assert (n <> S (S i)) by omega. apply Nat.eqb_neq in H1 as HSSneq.
  rewrite Hneq, HSneq. simpl. rewrite HSneq, HSSneq. f_equal.
  destruct n; auto. destruct n; auto.
  assert (i > n) by omega. apply leb_iff_conv in H2. rewrite H2. auto.
}
all: f_equal; auto.
}{
clear c_switch_SSi_Si_i_shift_1.
revert i. induction c; intros i; try destruct p; simpl; f_equal; auto.
}{
clear h_switch_SSi_Si_i_shift_1.
revert i. induction h; intros i; simpl; f_equal; auto.
}
Qed.

Lemma c_switch10_shift_1_0 c :
  c_switch_vars (Sub.c_shift c 1 0) 1 0 = Sub.c_shift c 1 1.
Proof.
  rewrite <-(c_switchswitch (Sub.c_shift c 1 1) 1 0).
  rewrite (c_switch_Si_i_shift_1 c 0). auto.
Qed.


Lemma v_negshift_1_switch_Si_i v i:
  v_no_var_j v i ->
  Sub.v_negshift (v_switch_vars v (S i) i) 1 (S i) 
    = Sub.v_negshift v 1 i
with c_negshift_1_switch_Si_i c i:
  c_no_var_j c i ->
  Sub.c_negshift (c_switch_vars c (S i) i) 1 (S i) 
    = Sub.c_negshift c 1 i
with h_negshift_1_switch_Si_i h i:
  h_no_var_j h i ->
  Sub.h_negshift (h_switch_vars h (S i) i) 1 (S i) 
    = Sub.h_negshift h 1 i.
Proof.
{
specialize (v_negshift_1_switch_Si_i v 0).
clear v_negshift_1_switch_Si_i.
revert i. induction v; intros i no_var; simpl.
{
destruct v as (name, n). simpl.
destruct n; simpl.
+ destruct i; auto.
+ destruct (i <=? S n) eqn:cmp; simpl.
  - apply leb_complete in cmp. simpl in no_var.
    assert (n-0=n) as nzero by omega. rewrite nzero.
    destruct (n=?i) eqn:ni.
    * simpl. apply Nat.eqb_eq in ni. rewrite ni.
      destruct i; auto. assert (S i > i) by omega. apply leb_iff_conv in H.
      rewrite H. reflexivity.
    * destruct i. { simpl. rewrite nzero. reflexivity. }
      assert (n<>i) by omega. apply Nat.eqb_neq in H. rewrite H.
      simpl. destruct n.
      ** assert (i=0) by omega. rewrite H0 in no_var. destruct no_var. auto.
      ** apply Nat.eqb_neq in ni.
         assert (i <= n) by omega. apply leb_correct in H0. rewrite H0. f_equal.
  - simpl in no_var. apply leb_iff_conv in cmp.
    assert (n<>i) by omega. apply Nat.eqb_neq in H. rewrite H.
    destruct i. omega.
    assert (n<>i) by omega. apply Nat.eqb_neq in H0. rewrite H0.
    simpl. destruct n; auto.
    apply Nat.eqb_neq in H. assert (n<i) by omega. apply leb_iff_conv in H1.
    rewrite H1. reflexivity.
}
all: f_equal; auto; try destruct no_var; auto.
}{
clear c_negshift_1_switch_Si_i.
revert i. induction c; intros i no_var; simpl in no_var; try destruct no_var;
try destruct p; simpl; f_equal; auto; try destruct no_var; auto;
try destruct H0; auto.
}{
clear h_negshift_1_switch_Si_i.
revert i. induction h; intros i no_var; simpl; simpl in no_var; auto.
f_equal; destruct no_var; auto.
}
Qed.


Lemma c_negshift_1_0_switch10 c :
  c_no_var_j c 1 ->
  Sub.c_negshift (c_switch_vars c 1 0) 1 0 = Sub.c_negshift c 1 1.
Proof.
  intro novar.
  rewrite <-(c_negshift_1_switch_Si_i).
  rewrite c_switchswitch. reflexivity.
  apply c_no_var_j_switch_i_j. assumption.
Qed.