(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Export substitution syntax_lemmas.
Require Import Arith Le.


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

Lemma h_shift_find_op_None h o i j :
  find_op_case h o = None <-> find_op_case (Sub.h_shift h i j) o = None.
Proof.
constructor; intro; induction h; auto; simpl in *;
destruct (o==o0) eqn:cmp; try discriminate; auto.
Qed.

Lemma h_shift_find_op_Some h o i j x k cop :
  find_op_case h o = Some (x, k, cop) -> 
  find_op_case (Sub.h_shift h i j) o = 
    Some (x, k, (Sub.c_shift cop i (j+2))).
Proof.
intro; induction h.
+ simpl in H. discriminate.
+ simpl in *. destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.



(* needed for tmpl handling *)
Lemma v_shift_comm_aux n i j d (v:val) :
i >= j ->
Sub.v_shift (Sub.v_shift v n i) d j = Sub.v_shift (Sub.v_shift v d j) n (i+d)

with c_shift_comm_aux n i j d (c:comp) :
i >= j ->
Sub.c_shift (Sub.c_shift c n i) d j = Sub.c_shift (Sub.c_shift c d j) n (i+d)

with h_shift_comm_aux n i j d (h:hcases) :
i >= j ->
Sub.h_shift (Sub.h_shift h n i) d j = Sub.h_shift (Sub.h_shift h d j) n (i+d).
Proof.
{
intros cmp. induction v; simpl.
{ 
  clear v_shift_comm_aux c_shift_comm_aux h_shift_comm_aux.
  destruct v as (x, dbi).
  destruct (i<=?dbi) eqn:cmpi; destruct (j<=?dbi) eqn:cmpj; simpl;
  destruct (i+d<=?dbi) eqn:cmpid; destruct (j<=?dbi+n) eqn:cmpjn; simpl;
  destruct (i+d<=?dbi+d) eqn:cmpidd; simpl;
  apply leb_complete in cmpj || apply leb_complete_conv in cmpj;
  apply leb_complete in cmpi || apply leb_complete_conv in cmpi;
  apply leb_complete in cmpjn || apply leb_complete_conv in cmpjn;
  apply leb_complete in cmpid || apply leb_complete_conv in cmpid;
  apply leb_complete in cmpidd || apply leb_complete_conv in cmpidd;
  try omega; simpl.  f_equal. f_equal. omega. f_equal. f_equal. omega.
  + assert (j<=?dbi=true) by (apply leb_correct in cmpj; assumption).
    rewrite H. auto.
  + assert (j<=?dbi=false) by (apply leb_correct_conv in cmpj; assumption).
    rewrite H. auto.
  + assert (j<=?dbi=false) by (apply leb_correct_conv in cmpj; assumption).
    rewrite H. auto. 
}
all: f_equal; auto.
+ assert (i+d+1=i+1+d) by omega. rewrite H. eapply c_shift_comm_aux. omega.
+ assert (i+d+1=i+1+d) by omega. rewrite H. eapply c_shift_comm_aux. omega.
}{
intros cmp. induction c; simpl; f_equal; auto; 
try eapply c_shift_comm_aux; try omega;
assert (i+d+1=i+1+d) by omega; try rewrite H;
assert (2=1+1) by omega; assert (i+d+(1+1)=i+(1+1)+d) by omega;
try rewrite H0; try rewrite H1; eapply c_shift_comm_aux; omega.
}{
intros cmp. induction h; simpl.
all: f_equal; auto.
assert (2=1+1) by omega; assert (i+d+(1+1)=i+(1+1)+d) by omega;
rewrite H; rewrite H0; eapply c_shift_comm_aux; omega.
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
    f_equal. f_equal. omega.
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



Lemma v_shift_0 cut v : Sub.v_shift v 0 cut = v
with c_shift_0 cut c : Sub.c_shift c 0 cut = c
with h_shift_0 cut h : Sub.h_shift h 0 cut = h.
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


Lemma v_shift_sub v v' i j (safe: j < i): 
  Sub.v_shift (v_sub v v' j) 1 i = 
  (v_sub (Sub.v_shift v 1 (i+1)) (Sub.v_shift v' 1 i) j)
with c_shift_sub c v' i j (safe: j < i): 
  Sub.c_shift (c_sub c v' j) 1 i = 
  (c_sub (Sub.c_shift c 1 (i+1)) (Sub.v_shift v' 1 i) j)
with h_shift_sub h v' i j (safe: j < i): 
  Sub.h_shift (h_sub h v' j) 1 i = 
  (h_sub (Sub.h_shift h 1 (i+1)) (Sub.v_shift v' 1 i) j).
Proof.
{
induction v; unfold v_sub; simpl.
{
clear v_shift_sub c_shift_sub h_shift_sub.
destruct v as (x, n). 
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
++ assert (i=?j=false) by (apply Nat.eqb_neq; omega).
  rewrite H. assert (i+1<=?i=false) by (apply leb_correct_conv; omega).
  rewrite H0. simpl. assert (j<=?i=true) by (apply leb_correct;omega).
  rewrite H1. assert (i=?j=false) by (apply Nat.eqb_neq; omega).
  rewrite H2. simpl. rewrite H1. assert (i<=?i-1=false).
  apply leb_correct_conv. omega. rewrite H3. reflexivity.
++ destruct (n=?j) eqn:nj.
+ apply Nat.eqb_eq in nj. subst.
  assert (i+1<=?j=false) by (apply leb_correct_conv; omega).
  rewrite H. simpl. assert (j=?j=true) by (apply Nat.eqb_eq; omega).
  rewrite H0. rewrite v_negshift_shift. rewrite v_negshift_shift.
  assert (1-1=0) by omega. rewrite H1. rewrite v_shift_0. rewrite v_shift_0.
  reflexivity. omega. omega.
+ destruct (i<=?n) eqn:iln; simpl.
  - destruct (j<=?n) eqn:jln; simpl.
    * apply leb_complete in jln. apply leb_complete in iln.
      assert (i<=?n-1=true).
      { apply leb_correct. apply Nat.eqb_neq in ni. omega. }
      rewrite H. simpl. assert (i+1<=?n=true).
      { apply leb_correct. apply leb_complete in H. omega. }
      rewrite H0. simpl. 
      assert (n+1=?j=false).
      { apply Nat.eqb_neq. omega. }
      rewrite H1. simpl. assert (j<=?n+1=true).
      { apply leb_correct. omega. }
      rewrite H2. simpl.
      f_equal. f_equal. assert (n>0) by omega. omega.
    * rewrite iln. apply leb_complete in iln. assert (i+1<=?n=true).
      { apply leb_correct. apply Nat.eqb_neq in ni. omega. }
      rewrite H. apply leb_complete in H. apply leb_complete_conv in jln. omega. 
  - apply leb_complete_conv in iln.
    assert (i+1<=?n=false) by (apply leb_correct_conv; omega).
    rewrite H. simpl. rewrite nj. simpl.
    destruct (j<=?n) eqn:jln.
    * simpl. assert (i<=?n-1=false).
      { apply leb_correct_conv. omega. }
      rewrite H0. reflexivity.
    * simpl. assert (i<=?n=false) by (apply leb_correct_conv; omega).
      rewrite H0. reflexivity.
}     
all: f_equal; auto.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ apply h_shift_sub. auto.
}{
induction c; unfold c_sub; simpl; f_equal;
try apply v_shift_sub; try assumption.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (j+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (j+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
}{
induction h; unfold h_sub; simpl. auto. f_equal.
+ apply h_shift_sub. assumption.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (j+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. f_equal. all: omega.
}
Qed.


(* 
Lemma v_shift_sub v v' i j (safe: i < j): 
  Sub.v_shift (v_sub v v' j) 1 i = 
  (v_sub (Sub.v_shift v 1 i) (Sub.v_shift v' 1 i) (j+1))
with c_shift_sub c v' i j (safe: i < j): 
  Sub.c_shift (c_sub c v' j) 1 i = 
  (c_sub (Sub.c_shift c 1 i) (Sub.v_shift v' 1 i) (j+1))
with h_shift_sub h v' i j (safe: i < j): 
  Sub.h_shift (h_sub h v' j) 1 i = 
  (h_sub (Sub.h_shift h 1 i) (Sub.v_shift v' 1 i) (j+1)).
Proof.
{
induction v; unfold v_sub; simpl.
{
clear v_shift_sub c_shift_sub h_shift_sub.
destruct v as (x, n). destruct (n=?j) eqn:nj.
+ apply Nat.eqb_eq in nj. subst.
  assert (i<=?j=true) by (apply leb_correct; omega).
  rewrite H. simpl. assert (j+1=?j+1=true) by (apply Nat.eqb_eq; omega).
  rewrite H0. rewrite v_negshift_shift. rewrite v_negshift_shift.
  assert (1-1=0) by omega. rewrite H1. rewrite v_shift_0. rewrite v_shift_0.
  reflexivity. omega. omega.
+ destruct (i<=?n) eqn:iln; simpl.
  - destruct (j<=?n) eqn:jln; simpl.
    * assert (i<=?n-1=true). all: apply leb_complete in jln.
      { apply leb_complete in iln. 
        apply leb_correct. omega. }
      rewrite H. assert (n+1=?j+1=false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in nj. omega. }
      rewrite H0. simpl. assert (j+1<=?n+1=true).
      { apply leb_correct. omega. }
      rewrite H1. f_equal. f_equal. assert (n>0) by omega. omega.
    * rewrite iln. assert (n+1=?j+1=false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in nj. omega. }
      rewrite H. simpl. assert (j+1<=?n+1=false).
      { apply leb_correct_conv. apply leb_complete_conv in jln. omega. }
      rewrite H0. reflexivity.
  - apply leb_complete_conv in iln. apply Nat.eqb_neq in nj.
    assert (j<=?n=false) by (apply leb_correct_conv; omega).
    rewrite H. assert (n=?j+1=false) by (apply Nat.eqb_neq; omega).
    rewrite H0. simpl. assert (i<=?n=false) by (apply leb_correct_conv;omega).
    rewrite H1. assert (j+1<=?n=false) by (apply leb_correct_conv; omega).
    rewrite H2. reflexivity.
}     
all: f_equal; auto.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ apply h_shift_sub. auto.
}{
induction c; unfold c_sub; simpl; f_equal;
try apply v_shift_sub; try assumption.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 (j+1)).
  rewrite (v_shift_comm_aux 1 (j+1+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 (j+1)).
  rewrite (v_shift_comm_aux 1 (j+1+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite v_shift_comm_aux. rewrite c_shift_sub.
  f_equal. f_equal. f_equal. rewrite (v_shift_comm_aux 1 (j+1)). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
}{
induction h; unfold h_sub; simpl. auto. f_equal.
+ apply h_shift_sub. assumption.
+ clear v_shift_sub h_shift_sub.
  unfold c_sub in c_shift_sub. rewrite <-(v_shift_shift 1).
  rewrite (v_shift_comm_aux 1 j). rewrite (v_shift_comm_aux 1 (j+1)).
  assert (j+1+1=j+2) by omega. rewrite H. rewrite c_shift_sub. clear c_shift_sub.
  f_equal. f_equal. f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0). rewrite (v_shift_comm_aux 1 (j+1)).
  rewrite (v_shift_comm_aux 1 (j+1+1)). f_equal. rewrite (v_shift_comm_aux 1 i).
  rewrite (v_shift_comm_aux 1 (i+1)). f_equal. all: omega.
}
Qed.



 *)
