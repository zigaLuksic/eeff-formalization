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
    assert (cut <= n + db_i) by omega.
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


(* Lemma v_shift_shift_alt n m cut (v:val) :
  Sub.v_shift (Sub.v_shift v n cut) m (n+cut) = (Sub.v_shift v (n + m) cut)

with c_shift_shift_alt n m cut (c:comp) :
  Sub.c_shift (Sub.c_shift c n cut) m (n+cut) = (Sub.c_shift c (n + m) cut)

with h_shift_shift_alt n m cut (h:hcases) :
  Sub.h_shift (Sub.h_shift h n cut) m (n+cut) = (Sub.h_shift h (n + m) cut).
Proof.
{
clear v_shift_shift_alt.
revert cut. induction v; intros cut; simpl; f_equal.
{ (* The only relevant case. *)
  destruct v as (name, db_i).
  destruct (cut <=? db_i) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (n+cut <= n+db_i) by omega.
    apply leb_correct in H. rewrite H.
    f_equal. f_equal. omega.
  - assert (n+cut <=? db_i = false).
    { apply leb_correct_conv. apply leb_complete_conv in cmp. omega. }
    rewrite H. reflexivity. }
all : try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : assert (S(n+cut)=n + S cut) by omega; try rewrite H.
all : try apply c_shift_shift_alt || apply h_shift_shift_alt; assumption.
}{
clear c_shift_shift_alt.
revert cut. induction c; intros cut; try destruct p; simpl; f_equal;
try apply v_shift_shift_alt.
all : assert (S(n+cut)=n + S cut) by omega; try rewrite H.
all : assert (S(n+ S cut)=n + S (S cut)) by omega; try rewrite H0.
all : try apply IHc || apply IHc1 || apply IHc2.
}{
clear h_shift_shift_alt.
revert cut. induction h; intros cut; simpl; f_equal.
reflexivity. apply IHh.
assert (S(S(n+cut))=n+S(S cut)) by omega. rewrite H. 
apply c_shift_shift_alt.
}
Qed. *)

Lemma v_shift_makes_no_var v j:
  v_no_var (Sub.v_shift v 1 j) j
with c_shift_makes_no_var c j:
  c_no_var (Sub.c_shift c 1 j) j
with h_shift_makes_no_var h j:
  h_no_var (Sub.h_shift h 1 j) j.
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


Lemma v_no_var_shift (v:val) j n cut:
  v_no_var v j -> (cut <= j) -> v_no_var (Sub.v_shift v n cut) (n+j)

with c_no_var_shift (c:comp) j n cut:
  c_no_var c j -> (cut <= j) -> c_no_var (Sub.c_shift c n cut) (n+j)
  
with h_no_var_shift (h:hcases) j n cut:
  h_no_var h j -> (cut <= j) -> h_no_var (Sub.h_shift h n cut) (n+j).
Proof.
all: assert (forall j, S(n+j)=n+(S j)) as snj by (intro; omega).
all: assert (forall j, S(S(n+j))=n+(S(S j))) as ssnj by (intro; omega).
{
clear v_no_var_shift.
revert j. induction v; intros j orig_clean j_le_cut; simpl; simpl in orig_clean;
try constructor; try inv orig_clean; auto.
+ destruct v as (name, num). destruct (cut <=? num) eqn:cmp; simpl;
  try rewrite leb_iff_conv in cmp; omega.
+ rewrite snj. apply c_no_var_shift. assumption. omega. 
+ rewrite snj. apply c_no_var_shift. assumption. omega.
}{
clear c_no_var_shift.
revert j cut. induction c; intros j cut orig_clean j_le_cut; simpl; simpl in *.
all: try inv orig_clean; try constructor; try constructor; auto.
all: try rewrite ssnj; try rewrite snj.
all: try apply IHc || apply IHc1 || apply IHc2; try omega; auto.
all: inv H0; assumption.
}{
clear h_no_var_shift.
revert j cut. induction h; intros j cut orig_clean j_le_cut; simpl;
destruct orig_clean; auto. constructor. auto.
rewrite ssnj. apply c_no_var_shift. assumption. omega.
}
Qed.


Lemma v_no_var_subbed (v:val) j v_s :
  v_no_var v_s j -> v_no_var (Sub.v_sub v (j, v_s)) j

with c_no_var_subbed (c:comp) j v_s :
  v_no_var v_s j -> c_no_var (Sub.c_sub c (j, v_s)) j

with h_no_var_subbed (h:hcases) j v_s :
  v_no_var v_s j -> h_no_var (Sub.h_sub h (j, v_s)) j.
Proof.
{
clear v_no_var_subbed.
revert j. induction v; intros j v_s_clean; try constructor.
all: try (apply IHv; assumption); auto.
- destruct v as (x, n). simpl.
  induction (n =? j) eqn:fits.
  + assumption.
  + simpl. apply Nat.eqb_neq in fits. omega.
- apply c_no_var_subbed. apply v_no_var_shift. assumption. omega.
- apply c_no_var_subbed. apply v_no_var_shift. assumption. omega.
}{
clear c_no_var_subbed.
revert j v_s. induction c; intros j v_s v_s_clean; simpl; try constructor;
try destruct p; simpl; try constructor; auto;
try apply IHc || apply IHc1 || apply IHc2;
try (apply v_no_var_shift; assumption || omega).
all:
assert (v_no_var (Sub.v_shift v_s 1 0) (1 + j)) by
  (apply v_no_var_shift; auto || omega).
all: apply (v_no_var_shift _ _ 1 0) in H; try omega.
all: rewrite v_shift_shift in H; simpl in H; assumption.
}{
clear h_no_var_subbed.
revert j v_s. induction h; intros j v_s v_s_clean; simpl; auto.
constructor. auto.
assert (v_no_var (Sub.v_shift v_s 1 0) (1+j)).
{ apply v_no_var_shift. auto. omega. }
apply (v_no_var_shift _ _ 1 0) in H.
rewrite (v_shift_shift _ _ _) in H. auto. omega.
}
Qed.


Lemma h_shift_find_op_None h o i j :
  find_op_case h o = None <-> find_op_case (Sub.h_shift h i j) o = None.
Proof.
constructor; intro; induction h; auto; simpl in *;
destruct (o==o0) eqn:cmp; try discriminate; auto.
Qed.

Lemma h_negshift_find_op_None h o i j :
  find_op_case h o = None <-> find_op_case (Sub.h_negshift h i j) o = None.
Proof.
constructor; intro; induction h; auto; simpl in *;
destruct (o==o0) eqn:cmp; try discriminate; auto.
Qed.

Lemma h_shift_find_op_Some h o i j x k cop :
  find_op_case h o = Some (x, k, cop) -> 
  find_op_case (Sub.h_shift h i j) o = 
    Some (x, k, (Sub.c_shift cop i (2+j))).
Proof.
intro; induction h.
+ simpl in H. discriminate.
+ simpl in *. destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.

Lemma h_negshift_find_op_Some h o i j x k cop :
  find_op_case h o = Some (x, k, cop) -> 
  find_op_case (Sub.h_negshift h i j) o = 
    Some (x, k, (Sub.c_negshift cop i (2+j))).
Proof.
intro; induction h.
+ simpl in H. discriminate.
+ simpl in *. destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.

Lemma h_sub_find_op_None h o i v_s :
  find_op_case h o = None -> 
  find_op_case (Sub.h_sub h (i, v_s)) o = None.
Proof.
intro; induction h.
+ simpl. reflexivity.
+ simpl in *. destruct (o==o0) eqn:cmp. discriminate. auto.
Qed.

Lemma h_sub_find_op_Some h o i v_s x k cop :
  find_op_case h o = Some (x, k, cop) -> 
  find_op_case (Sub.h_sub h (i, v_s)) o = 
    Some (x, k, (Sub.c_sub cop (2+i, Sub.v_shift v_s 2 0))).
Proof.
intro; induction h.
+ simpl in H. discriminate.
+ simpl in *. destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.


(* needed for tmpl handling *)
Lemma v_shift_comm_aux n i j d (v:val) :
i >= j ->
Sub.v_shift (Sub.v_shift v n i) d j = Sub.v_shift (Sub.v_shift v d j) n (d+i)

with c_shift_comm_aux n i j d (c:comp) :
i >= j ->
Sub.c_shift (Sub.c_shift c n i) d j = Sub.c_shift (Sub.c_shift c d j) n (d+i)

with h_shift_comm_aux n i j d (h:hcases) :
i >= j ->
Sub.h_shift (Sub.h_shift h n i) d j = Sub.h_shift (Sub.h_shift h d j) n (d+i).
Proof.
{
intros cmp. induction v; simpl.
{ 
  clear v_shift_comm_aux c_shift_comm_aux h_shift_comm_aux.
  destruct v as (x, dbi).
  destruct (i<=?dbi) eqn:cmpi; destruct (j<=?dbi) eqn:cmpj; simpl.
  + apply leb_complete in cmpi. apply leb_complete in cmpj.
    assert (j<=?n+dbi=true) by (apply leb_correct; omega).
    assert (d+i<=?d+dbi=true) by (apply leb_correct; omega).
    rewrite H, H0. f_equal. f_equal. omega.
  + apply leb_complete in cmpi. apply leb_complete_conv in cmpj. omega.
  + apply leb_complete_conv in cmpi. rewrite cmpj. apply leb_complete in cmpj.
    assert (d+i<=?d+dbi=false) by (apply leb_correct_conv; omega).  
    rewrite H. reflexivity.
  + rewrite cmpj. 
    apply leb_complete_conv in cmpi. apply leb_complete_conv in cmpj.
    assert (d+i<=?dbi=false) by (apply leb_correct_conv; omega).
    rewrite H.  reflexivity.
}
clear v_shift_comm_aux h_shift_comm_aux.
all: f_equal; auto.
all: assert (S(d+i)=d+S i) by omega; rewrite H. 
all: eapply c_shift_comm_aux; omega.
}{
intros cmp. induction c; simpl; f_equal; auto; 
clear v_shift_comm_aux h_shift_comm_aux.
try eapply c_shift_comm_aux; try omega.
all: assert (S(S(d+i))=d+S(S i)) by omega; try (rewrite H;
  eapply c_shift_comm_aux; omega).
all: assert (S(d+i)=d+S i) by omega; try rewrite H0;
  eapply c_shift_comm_aux; omega.
}{
clear v_shift_comm_aux h_shift_comm_aux.
intros cmp. induction h; simpl.
all: f_equal; auto.
assert (S(S(d+i))=d+S(S i)) by omega;
rewrite H; eapply c_shift_comm_aux; omega.
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
    assert (cut <= n + db_i) by omega.
    apply (leb_correct _ _) in H. rewrite H.
    f_equal. f_equal. omega.
  - rewrite cmp. reflexivity. }
all : try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : try apply c_negshift_shift || apply h_negshift_shift; assumption.
}{
clear c_negshift_shift h_negshift_shift.
revert cut. induction c; intros cut m_le_n; simpl; f_equal;
try apply v_negshift_shift || apply IHc || apply IHc1 || apply IHc2; assumption.
}{
clear h_negshift_shift v_negshift_shift.
revert cut. induction h; intros cut m_le_n; simpl; f_equal.
reflexivity. apply IHh. assumption. apply c_negshift_shift. assumption.
}
Qed.

Lemma v_shift_negshift_1j v n i j :
v_no_var v j -> i <= j ->
  Sub.v_shift (Sub.v_negshift v 1 j) n i 
= Sub.v_negshift (Sub.v_shift v n i) 1 (n+j) 
with c_shift_negshift_1j c n i j :
c_no_var c j -> i <= j ->
  Sub.c_shift (Sub.c_negshift c 1 j) n i 
= Sub.c_negshift (Sub.c_shift c n i) 1 (n+j) 
with h_shift_negshift_1j h n i j :
h_no_var h j -> i <= j ->
  Sub.h_shift (Sub.h_negshift h 1 j) n i 
= Sub.h_negshift (Sub.h_shift h n i) 1 (n+j).
Proof.
{
clear v_shift_negshift_1j.
revert j; induction v; intros j novar cmpij; simpl.
{ 
destruct v as (x, d). simpl.
destruct (j<=?d) eqn:jd.
+ apply leb_complete in jd. assert (i<=?d=true) by (apply leb_correct; omega).
  rewrite H. simpl. assert (n+j<=?n+d=true).
  { apply leb_correct; omega. }
  rewrite H0. assert (i<=?d-1=true).
  { apply leb_correct. simpl in novar. omega. }
  rewrite H1. do 2 f_equal. simpl in novar. omega.
+ apply leb_complete_conv in jd. simpl.
  destruct (i<=?d) eqn:id; simpl.
  - assert (n+j<=?n+d=false).
    { apply leb_correct_conv; omega. }
    rewrite H. reflexivity.
  - assert (n+j<=?d=false).
    { apply leb_correct_conv; omega. }
    rewrite H. reflexivity.
}
all : f_equal; try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : simpl in novar; try destruct novar; auto.
all : assert (S(n+j)=n+(S j)) as snj by omega; rewrite snj.
all : apply c_shift_negshift_1j; omega || auto.
}{
clear h_shift_negshift_1j.
revert j. destruct c; intros j novar cmpij; simpl in *; f_equal.
all : assert (S(S(n+j))=n+(S (S j))) as ssnj by omega; try rewrite ssnj.
all : assert (S(n+j)=n+(S j)) as snj by omega; try rewrite snj.
all: apply v_shift_negshift_1j || apply c_shift_negshift_1j.
all: omega || (try destruct novar; auto).
all: destruct H0; auto.
}{
clear h_shift_negshift_1j v_shift_negshift_1j.
revert j. induction h; intros j novar cmpij; simpl; f_equal. auto.
+ apply IHh. inv novar. assumption. assumption.
+ assert (S(S(n+j))=n+(S (S j))) as ssnj by omega; try rewrite ssnj.
  apply c_shift_negshift_1j. inv novar. auto. omega.
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


Lemma v_shift_sub v v' i cut j :
  cut <= j ->
  Sub.v_shift (Sub.v_sub v (j, v')) i cut 
  = Sub.v_sub (Sub.v_shift v i cut) (i+j, Sub.v_shift v' i cut)
with c_shift_sub c v' i cut j :
  cut <= j ->
  Sub.c_shift (Sub.c_sub c (j, v')) i cut 
  = Sub.c_sub (Sub.c_shift c i cut) (i+j, Sub.v_shift v' i cut)
with h_shift_sub h v' i cut j :
  cut <= j ->
  Sub.h_shift (Sub.h_sub h (j, v')) i cut
  = Sub.h_sub (Sub.h_shift h i cut) (i+j, Sub.v_shift v' i cut).
Proof.
{
revert i cut j; induction v; intros i cut j cmpcj; simpl.
{ 
destruct v as (x, d). simpl.
destruct (cut<=?d) eqn:cd.
+ destruct (d=?j) eqn:dj.
   * apply Nat.eqb_eq in dj. subst. simpl.
     assert (i+j=?i+j=true) by (apply Nat.eqb_eq; omega).
     rewrite H. reflexivity.
   * simpl. rewrite cd. assert (i+d=?i+j=false).
     { apply Nat.eqb_neq. apply Nat.eqb_neq in dj. omega. }
     rewrite H. reflexivity.
+ assert (d=?j=false).
  { apply Nat.eqb_neq. apply leb_complete_conv in cd. omega. }
  rewrite H. simpl. rewrite cd.
  assert (d=?i+j=false).
  { apply Nat.eqb_neq. apply leb_complete_conv in cd. omega. }
  rewrite H0. reflexivity.
}
all : f_equal; try reflexivity || apply IHv || apply IHv1 || apply IHv2; auto.
all : assert (S(i+j)=i+(S j)) as sij by omega; rewrite sij.
all : rewrite v_shift_comm_aux, c_shift_sub; try omega || f_equal.
}{
clear h_shift_sub.
revert i cut j; induction c; intros i cut j cmpcj; simpl; f_equal; auto.
all : assert (S(S(i+j))=i+(S (S j))) as ssij by omega; try rewrite ssij.
all : assert (S(i+j)=i+(S j)) as sij by omega; try rewrite sij.
all: rewrite v_shift_comm_aux, c_shift_sub; try omega || f_equal.
}{
clear v_shift_sub h_shift_sub.
revert i cut j; induction h; intros i cut j cmpcj; simpl; f_equal; auto.
+ assert (S(S(i+j))=i+(S (S j))) as ssij by omega. rewrite ssij.
  rewrite v_shift_comm_aux, c_shift_sub; try omega || f_equal.
}
Qed.

Lemma v_negshift_sub v v' cut j :
  cut < j -> v_no_var v cut -> v_no_var v' cut ->
  Sub.v_negshift (Sub.v_sub v (j, v')) 1 cut 
  = Sub.v_sub (Sub.v_negshift v 1 cut) (j-1, Sub.v_negshift v' 1 cut)
with c_negshift_sub c v' cut j :
  cut < j -> c_no_var c cut -> v_no_var v' cut ->
  Sub.c_negshift (Sub.c_sub c (j, v')) 1 cut 
  = Sub.c_sub (Sub.c_negshift c 1 cut) (j-1, Sub.v_negshift v' 1 cut)
with h_negshift_sub h v' cut j :
  cut < j -> h_no_var h cut -> v_no_var v' cut ->
  Sub.h_negshift (Sub.h_sub h (j, v')) 1 cut
  = Sub.h_sub (Sub.h_negshift h 1 cut) (j-1, Sub.v_negshift v' 1 cut).
Proof.
{
revert cut j; induction v; intros cut j cmpcj novar novar'; simpl.
{ 
destruct v as (x, d). simpl. simpl in novar.
destruct (cut<=?d) eqn:cd.
+ destruct (d=?j) eqn:dsj.
  - simpl. apply Nat.eqb_eq in dsj. subst.
    assert (j-1=?j-1=true) by (apply Nat.eqb_eq; omega).
    rewrite H. reflexivity.
  - simpl. rewrite cd. assert (d-1=?j-1=false).
    { apply Nat.eqb_neq. apply Nat.eqb_neq in dsj. omega. }
    rewrite H. reflexivity.
+ assert (d=?j=false).
  { apply Nat.eqb_neq. apply leb_complete_conv in cd. omega. }
  rewrite H. simpl. rewrite cd.
  assert (d=?j-1=false).
  { apply Nat.eqb_neq. apply leb_complete_conv in cd. omega. }
  rewrite H0. reflexivity.
}
all : f_equal; try reflexivity || apply IHv || apply IHv1 || apply IHv2; auto.
all : simpl in novar; try (destruct novar; auto).
all : rewrite c_negshift_sub; try omega || (f_equal; f_equal; auto).
all : clear v_negshift_sub c_negshift_sub h_negshift_sub.
all : try rewrite v_shift_negshift_1j; f_equal || omega || auto.
all : apply v_no_var_shift; omega || auto.
}{
clear h_negshift_sub.
revert cut j; induction c; intros cut j cmpcj novar novar'; simpl.
all : simpl in novar; f_equal; try destruct novar.
all : try apply v_negshift_sub; omega || auto.
all : clear v_negshift_sub.
all : assert (S(S cut)=1+(1+cut)) as ssc by omega; try rewrite ssc.
all : assert (S cut=1+cut) as sc by omega; try rewrite sc.
all : try destruct H0.
all : try rewrite c_negshift_sub; (f_equal; f_equal) || omega || auto.
all : clear c_negshift_sub.
all : try rewrite v_shift_negshift_1j; f_equal || omega || auto.
all : try apply v_no_var_shift; omega || auto.
all : assert (1+(1+cut)=2+cut) as cc by omega; rewrite cc.
all : apply v_no_var_shift; omega || auto.
}{
clear v_negshift_sub h_negshift_sub.
revert cut j; induction h; intros cut j cmpcj novar novar'.
all : simpl; f_equal; simpl in novar; try destruct novar; auto.
try rewrite c_negshift_sub; (f_equal; f_equal) || omega || auto.
omega. clear c_negshift_sub.
rewrite v_shift_negshift_1j; f_equal || omega || auto.
assert (S(S cut)=2+cut) as cc by omega; rewrite cc.
apply v_no_var_shift; omega || auto.
}
Qed.


Lemma v_sub_sub v v' v'' i j :
  v_no_var v j ->
  Sub.v_sub v (i, Sub.v_sub v' (j, v''))
  = Sub.v_sub (Sub.v_sub v (i, v')) (j, v'')
with c_sub_sub c v' v'' i j :
  c_no_var c j ->
  Sub.c_sub c (i, Sub.v_sub v' (j, v''))
  = Sub.c_sub (Sub.c_sub c (i, v')) (j, v'')
with h_sub_sub h v' v'' i j :
  h_no_var h j ->
  Sub.h_sub h (i, Sub.v_sub v' (j, v''))
  = Sub.h_sub (Sub.h_sub h (i, v')) (j, v'').
Proof.
{
revert i j; induction v; intros i j novar; simpl.
{ 
destruct v as (x, d). simpl.
destruct (d=?i) eqn:cd. reflexivity.
simpl. simpl in novar. assert (d=?j=false) by (apply Nat.eqb_neq; omega).
rewrite H. reflexivity.
}
all : f_equal; try reflexivity || apply IHv || apply IHv1 || apply IHv2; auto.
all : simpl in novar; try destruct novar; auto.
all : rewrite v_shift_sub, c_sub_sub; omega || auto.
}{
clear h_sub_sub.
revert i j; induction c; intros i j novar; simpl.
all : f_equal; simpl in novar; try destruct novar; auto.
all : rewrite v_shift_sub, c_sub_sub; omega || auto.
all : destruct H0; auto.
}{
clear v_sub_sub h_sub_sub.
revert i j; induction h; intros i j novar; simpl.
all : simpl in novar; f_equal; try destruct novar; auto.
rewrite v_shift_sub, c_sub_sub; omega || auto.
}
Qed.



Fixpoint v_under_var_shift v j n cut:
  v_under_var v j -> cut <= j -> v_under_var (Sub.v_shift v n cut) (n+j)

with c_under_var_shift c j n cut:
  c_under_var c j -> cut <= j -> c_under_var (Sub.c_shift c n cut) (n+j)

with h_under_var_shift h j n cut:
  h_under_var h j -> cut <= j -> h_under_var (Sub.h_shift h n cut) (n+j).
Proof.
{
intros under cmp. destruct v; simpl; simpl in under; auto.
{ destruct v. destruct (cut <=? v0) eqn:ccmp; simpl; omega. }
all: try (destruct under; constructor; auto).
all: assert (S(n+j)=n+S j) as Snj by omega; rewrite Snj.
all: eapply c_under_var_shift; eauto; omega.
}{
intros under cmp. destruct c; simpl; simpl in under; auto.
all: try (destruct under; constructor; auto).
all: assert (S(S(n+j))=n+S(S j)) as SSnj by omega; try rewrite SSnj.
all: assert (S(n+j)=n+S j) as Snj by omega; try rewrite Snj.
2: destruct H0; constructor.
all: eapply c_under_var_shift; eauto; omega.
}{
intros under cmp. destruct h; simpl; simpl in under. auto.
destruct under. constructor. auto.
assert (S(S(n+j))=n+S(S j)) as SSnj by omega; try rewrite SSnj.
eapply c_under_var_shift; eauto; omega.
}
Qed.

Fixpoint v_shift_too_high v n cut :
  v_under_var v cut -> Sub.v_shift v n cut = v
with c_shift_too_high c n cut :
  c_under_var c cut -> Sub.c_shift c n cut = c
with h_shift_too_high h n cut :
  h_under_var h cut -> Sub.h_shift h n cut = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ destruct v.
  assert (cut <=? v0 = false) by (apply leb_correct_conv; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
all: destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.

Fixpoint v_negshift_too_high v n cut :
  v_under_var v cut -> Sub.v_negshift v n cut = v
with c_negshift_too_high c n cut :
  c_under_var c cut -> Sub.c_negshift c n cut = c
with h_negshift_too_high h n cut :
  h_under_var h cut -> Sub.h_negshift h n cut = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ destruct v.
  assert (cut <=? v0 = false) by (apply leb_correct_conv; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
all: destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.

Fixpoint v_sub_too_high v i v_s:
  v_under_var v i -> Sub.v_sub v (i, v_s) = v
with c_sub_too_high c i v_s:
  c_under_var c i -> Sub.c_sub c (i, v_s) = c
with h_sub_too_high h i v_s:
  h_under_var h i -> Sub.h_sub h (i, v_s) = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ destruct v.
  assert (v0 =? i = false) by (apply Nat.eqb_neq; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
all: destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.

Fixpoint v_sub_no_var v v' i {struct v}:
  v_no_var v i -> Sub.v_sub v (i, v') = v
with c_sub_no_var c v' i {struct c}:
  c_no_var c i -> Sub.c_sub c (i, v') = c
with h_sub_no_var h v' i {struct h}:
  h_no_var h i -> Sub.h_sub h (i, v') = h.
Proof.
all: revert i.
+ intros i novar. destruct v; simpl in novar; try destruct novar. 
  { destruct v as (x,d). simpl.
    assert (d=?i=false) by (apply Nat.eqb_neq; omega).
    rewrite H. reflexivity.
  }
  all: simpl in *; f_equal; auto.
+ intros i novar. induction c; simpl in *; try destruct novar.
  all: f_equal; auto. all: destruct H0; auto.
+ intros i novar. induction h; simpl in *; try destruct novar.
  all: f_equal; auto.
Qed.


Fixpoint v_under_var_subs v v' i j {struct v}:
  v_under_var v i -> v_under_var v' i -> v_under_var (v_subs v v' j) i
with c_under_var_subs c v' i j {struct c}:
  c_under_var c i -> v_under_var v' i -> c_under_var (c_subs c v' j) i
with h_under_var_subs h v' i j {struct h}:
  h_under_var h i -> v_under_var v' i -> h_under_var (h_subs h v' j) i.
Proof.
all: revert i j.
+ intros. destruct v.
  { destruct v as (x,d). unfold v_subs. simpl. simpl in H.
    destruct (d=?j).
    + rewrite v_negshift_shift, v_shift_0. auto. omega.
    + simpl. destruct (j<=?d); simpl; omega.
  }
  all: simpl in *; auto.
  - apply v_under_var_subs; auto.
  - apply v_under_var_subs; auto.
  - constructor; inv H; apply v_under_var_subs; auto.
  - rewrite v_shift_comm_aux. apply c_under_var_subs. auto.
    apply v_under_var_shift. auto. omega. omega.
  - constructor; inv H.
    * rewrite v_shift_comm_aux. apply c_under_var_subs. auto.
      apply v_under_var_shift. auto. omega. omega.
    * apply h_under_var_subs; auto.
+ intros. induction c; simpl in *; auto.
  all: try constructor; try inv H; auto.
  all: try apply v_under_var_subs; eauto.
  2: constructor; inv H2.
  all: rewrite v_shift_comm_aux; try apply c_under_var_subs; omega || auto.
  all: try apply v_under_var_shift; omega || auto.
  all: assert (S(S i) = 2+i) by omega; rewrite H; apply v_under_var_shift.
  all: omega || auto.
+ intros. induction h; simpl in *; auto.
  constructor; inv H; auto.
  rewrite v_shift_comm_aux; try apply c_under_var_subs; omega || auto.
  assert (S(S i) = 2+i) by omega; rewrite H; apply v_under_var_shift.
  auto. omega.
Qed.

Fixpoint v_no_var_subs v v' i j {struct v}:
  v_no_var v (1+i) -> v_no_var v' i -> j<=i ->
  v_no_var (v_subs v v' j) i
with c_no_var_subs c v' i j {struct c}:
  c_no_var c (1+i) -> v_no_var v' i -> j<=i ->
  c_no_var (c_subs c v' j) i
with h_no_var_subs h v' i j {struct h}:
  h_no_var h (1+i) -> v_no_var v' i -> j<=i ->
  h_no_var (h_subs h v' j) i.
Proof.
all: revert i j.
+ intros. destruct v.
  { 
    destruct v as (x,d). unfold v_subs. simpl. simpl in H.
    destruct (d=?j) eqn:dj.
    + rewrite v_negshift_shift, v_shift_0. auto. omega.
    + simpl. destruct (j<=?d) eqn:jld; simpl; apply Nat.eqb_neq in dj.
      - apply leb_complete in jld. omega.
      - apply leb_complete_conv in jld. omega.
  }
  all: simpl in *; auto.
  - apply v_no_var_subs; auto.
  - apply v_no_var_subs; auto.
  - constructor; inv H; apply v_no_var_subs; auto.
  - rewrite v_shift_comm_aux. apply c_no_var_subs. auto.
    apply v_no_var_shift. auto. all: omega.
  - constructor; inv H.
    * rewrite v_shift_comm_aux. apply c_no_var_subs. auto.
      apply v_no_var_shift. auto. all: omega.
    * apply h_no_var_subs; auto.
+ intros. induction c; simpl in *; auto.
  all: try constructor; try inv H; auto.
  all: try apply v_no_var_subs; eauto.
  2: constructor; inv H3.
  all: rewrite v_shift_comm_aux; try apply c_no_var_subs; omega || auto.
  all: try apply v_no_var_shift; omega || auto.
  all: assert (S(S i) = 2+i) by omega; rewrite H; apply v_no_var_shift.
  all: omega || auto.
+ intros. induction h; simpl in *; auto.
  constructor; inv H; auto.
  rewrite v_shift_comm_aux; try apply c_no_var_subs; omega || auto.
  assert (S(S i) = 2+i) by omega; rewrite H; apply v_no_var_shift.
  auto. omega.
Qed.



Lemma v_shift_subs v v' i j (safe: j <= i): 
  Sub.v_shift (v_subs v v' j) 1 i = 
  (v_subs (Sub.v_shift v 1 (1+i)) (Sub.v_shift v' 1 i) j)
with c_shift_subs c v' i j (safe: j <= i): 
  Sub.c_shift (c_subs c v' j) 1 i = 
  (c_subs (Sub.c_shift c 1 (1+i)) (Sub.v_shift v' 1 i) j)
with h_shift_subs h v' i j (safe: j <= i): 
  Sub.h_shift (h_subs h v' j) 1 i = 
  (h_subs (Sub.h_shift h 1 (1+i)) (Sub.v_shift v' 1 i) j).
Proof.
{
induction v; unfold v_subs; simpl.
{
clear v_shift_subs c_shift_subs h_shift_subs.
destruct v as (x, n). 
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
+ destruct (i=?j) eqn:eqij.
  - apply Nat.eqb_eq in eqij. subst.
    assert (1+j<=?j=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; reflexivity).
    rewrite H0. simpl. 
    rewrite v_negshift_shift. rewrite v_negshift_shift.
    rewrite v_shift_shift. rewrite v_shift_shift. f_equal.
    omega. omega.
  - assert (1+i<=?i=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H. simpl.
    assert (j<=?i=true) by (apply leb_correct;omega).
    rewrite H0. rewrite eqij. simpl. rewrite H0.
    assert (i<=?i-1=false).
    { apply leb_correct_conv. apply Nat.eqb_neq in eqij. 
      apply leb_complete in H0. omega. }
    rewrite H1. reflexivity.
+ destruct (n=?j) eqn:nj.
  ++apply Nat.eqb_eq in nj. subst.
    assert (1+i<=?j=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H.
    simpl. assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0. rewrite v_negshift_shift. rewrite v_negshift_shift. simpl.
    rewrite v_shift_0. rewrite v_shift_0.
    reflexivity. omega. omega.
  ++destruct (i<=?n) eqn:iln; simpl.
    - destruct (j<=?n) eqn:jln; simpl.
      * apply leb_complete in jln. apply leb_complete in iln.
        assert (i<=?n-1=true).
        { apply leb_correct. apply Nat.eqb_neq in ni. omega. }
        rewrite H. simpl. assert (1+i<=?n=true).
        { apply leb_correct. apply leb_complete in H.
          apply Nat.eqb_neq in ni. omega. }
        simpl in H0. rewrite H0. simpl. 
        assert (1+n=?j=false).
        { apply Nat.eqb_neq. omega. }
        simpl in H1. rewrite H1. simpl. assert (j<=? S n=true).
        { apply leb_correct. omega. }
        rewrite H2. simpl.
        f_equal. f_equal. assert (n>0) by (apply Nat.eqb_neq in ni; omega).
        omega.
      * apply leb_complete in iln. apply leb_complete_conv in jln. omega.
    - apply leb_complete_conv in iln.
      assert (1+i<=?n=false) by (apply leb_correct_conv; omega).
      simpl in H. rewrite H. simpl. rewrite nj. simpl.
      destruct (j<=?n) eqn:jln.
      * simpl. assert (i<=?n-1=false).
        { apply leb_correct_conv. omega. }
        rewrite H0. reflexivity.
      * simpl. assert (i<=?n=false) by (apply leb_correct_conv; omega).
        rewrite H0. reflexivity.
}     
all: f_equal; auto.
3: apply h_shift_subs; auto.
all: clear v_shift_subs h_shift_subs; unfold c_subs in c_shift_subs.
all: rewrite v_shift_comm_aux; try omega.
all: rewrite c_shift_subs; clear c_shift_subs; try omega.
all: do 3 f_equal; rewrite (v_shift_comm_aux 1 j); f_equal; try omega.
all: rewrite (v_shift_comm_aux 1 i); f_equal; omega.
}{
destruct c; unfold c_subs; simpl; f_equal;
try apply v_shift_subs; try assumption.
all: clear v_shift_subs h_shift_subs; unfold c_subs in c_shift_subs.
+ rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite (v_shift_comm_aux 1 i), (v_shift_comm_aux 1 (1+i)). 
  do 2 f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 3 f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 3 f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 3 f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite (v_shift_comm_aux 1 i), (v_shift_comm_aux 1 (1+i)). 
  do 2 f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 3 f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 2 f_equal. rewrite (v_shift_comm_aux). reflexivity. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 3 f_equal. rewrite (v_shift_comm_aux 1 j). f_equal.
  rewrite (v_shift_comm_aux 1 i). f_equal. all: omega.
+ rewrite v_shift_comm_aux. rewrite c_shift_subs. clear c_shift_subs.
  do 2 f_equal. rewrite (v_shift_comm_aux). reflexivity. all: omega.
}{
destruct h; unfold h_subs; simpl. auto. f_equal.
+ apply h_shift_subs. assumption.
+ clear v_shift_subs h_shift_subs.
  unfold c_subs in c_shift_subs.
  rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega.
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite (v_shift_comm_aux 1 i), (v_shift_comm_aux 1 (1+i)). 
  do 2 f_equal. all: omega.
}
Qed.


Lemma v_negshift_subs v v' i j (safe: j <= i): 
  v_no_var v (1+i) -> v_no_var v' (i) ->
  Sub.v_negshift (v_subs v v' j) 1 i = 
  (v_subs (Sub.v_negshift v 1 (1+i)) (Sub.v_negshift v' 1 i) j)
with c_negshift_subs c v' i j (safe: j <= i): 
  c_no_var c (1+i) -> v_no_var v' (i) ->
  Sub.c_negshift (c_subs c v' j) 1 i = 
  (c_subs (Sub.c_negshift c 1 (1+i)) (Sub.v_negshift v' 1 i) j)
with h_negshift_subs h v' i j (safe: j <= i): 
  h_no_var h (1+i) -> v_no_var v' (i) ->
  Sub.h_negshift (h_subs h v' j) 1 i = 
  (h_subs (Sub.h_negshift h 1 (1+i)) (Sub.v_negshift v' 1 i) j).
Proof.
{
intros nov nov'. destruct v; unfold v_subs; simpl.
{
  clear v_negshift_subs c_negshift_subs h_negshift_subs.
  destruct v as (x, n).
  destruct (n=?j) eqn:nj.
  apply Nat.eqb_eq in nj. subst.
  destruct (1+i <=? j) eqn:cmpij.
  3 : destruct (1+i <=? n) eqn:Sin.
  all: simpl.
  + apply leb_complete in cmpij.
    assert (j=S i) by omega. subst. omega.
  + simpl in cmpij. rewrite cmpij. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H, v_negshift_shift, v_shift_0, v_negshift_shift, v_shift_0.
    reflexivity. omega. omega.
  + apply leb_complete in Sin as sin. simpl in Sin.
    rewrite Sin. apply Nat.eqb_neq in nj.
    assert (j<=?n=true) by (apply leb_correct; omega). simpl in H.
    rewrite H. simpl. assert (i<=?n-1=true) by (apply leb_correct; omega).
    rewrite H0. assert (n-1=?j=false).
    { apply Nat.eqb_neq. simpl in nov. omega. }
    rewrite H1. simpl. assert (j<=?n-1=true).
    { apply leb_correct. omega. }
    rewrite H2. reflexivity.
  + apply leb_complete_conv in Sin as sin. simpl in Sin. rewrite Sin. simpl.  
    rewrite nj. apply Nat.eqb_neq in nj. simpl.
    destruct (j<=?n) eqn:jln.
    - simpl. assert (i<=?n-1=false).
      { apply leb_correct_conv. omega. }
      rewrite H. reflexivity.
    - simpl. assert (i<=?n=false).
      { apply leb_correct_conv. apply leb_complete_conv in jln. omega. }
      rewrite H. reflexivity. 
}
all: f_equal; simpl in nov.
all: try apply v_negshift_subs; try omega || auto.
5: apply h_negshift_subs; auto; destruct nov; auto.
+ destruct nov. auto.
+ destruct nov. auto.
+ unfold c_subs in c_negshift_subs. rewrite v_shift_comm_aux.
  rewrite (c_negshift_subs c _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ unfold c_subs in c_negshift_subs. rewrite v_shift_comm_aux. destruct nov.
  rewrite (c_negshift_subs c _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
}{
induction c; intros nov nov'; unfold c_subs; simpl in nov |-*; f_equal;
try apply v_negshift_subs; try assumption.
all: clear v_negshift_subs h_negshift_subs.
all: try (destruct nov; assumption).
all: unfold c_subs in c_negshift_subs; inv nov.
+ rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)), c_negshift_subs. clear c_negshift_subs. simpl. do 3 f_equal. rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite v_shift_shift, v_shift_shift, v_shift_negshift_1j. reflexivity. 
  all: omega || auto. apply v_no_var_shift. apply v_no_var_shift.
  auto. omega. omega.
+ rewrite v_shift_comm_aux. inv H0.
  rewrite (c_negshift_subs _ _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm_aux. inv H0.
  rewrite (c_negshift_subs _ _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm_aux.
  rewrite (c_negshift_subs _ _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)), c_negshift_subs. clear c_negshift_subs. simpl. do 3 f_equal. rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite v_shift_shift, v_shift_shift, v_shift_negshift_1j. reflexivity. 
  all: omega || auto. apply v_no_var_shift. apply v_no_var_shift.
  auto. omega. omega.
+ rewrite v_shift_comm_aux.
  rewrite (c_negshift_subs _ _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite c_negshift_subs. clear c_negshift_subs.
  do 3 f_equal. all: omega || auto.
+ rewrite v_shift_comm_aux.
  rewrite (c_negshift_subs _ _ (S i) (S j)). clear c_negshift_subs.
  do 3 f_equal. rewrite v_shift_comm_aux. f_equal.
  rewrite v_shift_negshift_1j. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite c_negshift_subs. clear c_negshift_subs.
  do 3 f_equal. all: omega || auto.
}{
destruct h; unfold h_subs; intros nov nov'; simpl. auto. inv nov. f_equal.
+ apply h_negshift_subs; auto.
+ unfold c_subs in c_negshift_subs. clear v_negshift_subs h_negshift_subs.
  rewrite <-(v_shift_shift 1), (v_shift_comm_aux 1 j). simpl.
  rewrite (v_shift_comm_aux 1 (1+j)), c_negshift_subs. clear c_negshift_subs. simpl. do 3 f_equal. rewrite <-(v_shift_shift 1 1 0), (v_shift_comm_aux 1 j).
  rewrite (v_shift_comm_aux 1 (1+j)). f_equal. 
  rewrite v_shift_shift, v_shift_shift, v_shift_negshift_1j. reflexivity. 
  all: omega || auto. apply v_no_var_shift. apply v_no_var_shift.
  auto. omega. omega.
}
Qed.


Lemma v_sub_subs v i j vi vj:
  j >= i ->
  Sub.v_sub (v_subs v vi i) (j, vj) = 
  (v_subs (Sub.v_sub v (1+j, Sub.v_shift vj 1 i)) (Sub.v_sub vi (j, vj)) i)
with c_sub_subs c i j vi vj: 
  j >= i ->
  Sub.c_sub (c_subs c vi i) (j, vj) = 
  (c_subs (Sub.c_sub c (1+j, Sub.v_shift vj 1 i)) (Sub.v_sub vi (j, vj)) i)
with h_sub_subs h i j vi vj: 
  j >= i ->
  Sub.h_sub (h_subs h vi i) (j, vj) = 
  (h_subs (Sub.h_sub h (1+j, Sub.v_shift vj 1 i)) (Sub.v_sub vi (j, vj)) i).
Proof.
{
intros cmp. induction v; unfold v_subs; simpl.
{
clear v_sub_subs c_sub_subs h_sub_subs.
destruct v as (x, n). 
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
+ assert (i=?S j=false) by (apply Nat.eqb_neq; omega). rewrite H.
  destruct (i=?j) eqn:eqij.
  - apply Nat.eqb_eq in eqij. simpl.
    assert (i=?i=true) by (apply Nat.eqb_eq; omega). rewrite H0.
    rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    reflexivity. omega. omega.
  - simpl. assert (i=?i=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_negshift_shift.
    rewrite v_shift_0, v_shift_0. reflexivity. all: omega.
+ destruct (n=?S j) eqn:nsj.
  - apply Nat.eqb_eq in nsj. subst. simpl.
    assert (i<=?S j=true) by (apply leb_correct; omega).
    rewrite H. simpl. assert (j-0=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_sub_no_var, v_negshift_shift, v_shift_0.
    reflexivity. omega. apply v_shift_makes_no_var.
  - simpl. rewrite ni. simpl. destruct (i<=?n) eqn:cmpin.
    * simpl. assert (n-1=?j=false).
      { apply leb_complete in cmpin. apply Nat.eqb_neq.
        apply Nat.eqb_neq in nsj. apply Nat.eqb_neq in ni. omega. }
      rewrite H. reflexivity.
    * simpl. assert (n=?j=false).
      { apply Nat.eqb_neq. apply leb_complete_conv in cmpin. omega. }
      rewrite H. reflexivity.
}
all: f_equal; auto.
3: apply h_sub_subs; auto.
all: clear v_sub_subs h_sub_subs; unfold c_subs in c_sub_subs.
all: rewrite v_shift_comm_aux, c_sub_subs; clear c_sub_subs; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm_aux; try omega; f_equal.
}{
intros cmp. induction c; unfold c_subs; simpl; f_equal; auto.
all: try apply v_sub_subs; try assumption.
all: clear v_sub_subs h_sub_subs; unfold c_subs in c_sub_subs.
all: try rewrite v_shift_comm_aux, c_sub_subs; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm_aux; try omega; f_equal.
all: rewrite (v_shift_comm_aux _ i); f_equal; try omega.
all: rewrite v_shift_sub; f_equal; omega.
}{
intros cmp. induction h; unfold h_subs; simpl; f_equal; auto.
unfold c_subs in c_sub_subs. rewrite v_shift_comm_aux, c_sub_subs; try omega.
do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm_aux; try omega; f_equal.
rewrite (v_shift_comm_aux _ i); f_equal; try omega.
rewrite v_shift_comm_aux. f_equal. rewrite v_shift_sub. f_equal.
all: omega.
}
Qed.

