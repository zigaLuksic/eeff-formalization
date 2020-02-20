Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
Require Export substitution syntax_lemmas.
Require Import Le.

(* ==================== Effects on getters ==================== *)

Lemma shift_find_None h o i j :
  find_case h o = None <-> find_case (h_shift h i j) o = None.
Proof.
constructor; intro; induction h; auto; simpl in *;
destruct (o==o0) eqn:cmp; try discriminate; auto.
Qed.


Lemma negshift_find_None h o i j :
  find_case h o = None <-> find_case (h_negshift h i j) o = None.
Proof.
constructor; intro; induction h; auto; simpl in *;
destruct (o==o0) eqn:cmp; try discriminate; auto.
Qed.


Lemma sub_find_None h o i v_s :
  find_case h o = None -> 
  find_case (h_sub h (i, v_s)) o = None.
Proof.
intro; induction h; simpl in *. auto.
destruct (o==o0) eqn:cmp. discriminate. auto.
Qed.


Lemma shift_find_Some h o i j c :
  find_case h o = Some c -> 
  find_case (h_shift h i j) o = Some (c_shift c i (2+j)).
Proof.
intro; induction h; simpl in *. discriminate.
destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.


Lemma negshift_find_Some h o i j c :
  find_case h o = Some c -> 
  find_case (h_negshift h i j) o = Some (c_negshift c i (2+j)).
Proof.
intro; induction h; simpl in *. discriminate.
destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.


Lemma sub_find_Some h o i v_s c :
  find_case h o = Some c -> 
    find_case (h_sub h (i, v_s)) o 
  = Some (c_sub c (2+i, v_shift v_s 2 0)).
Proof.
intro; induction h; simpl in *. discriminate.
destruct (o==o0) eqn:cmp. inv H. all: auto.
Qed.

(* ==================== Shift and Sub interactions ==================== *)

Lemma v_shift_0 cut v : v_shift v 0 cut = v
with c_shift_0 cut c  : c_shift c 0 cut = c
with h_shift_0 cut h  : h_shift h 0 cut = h.
Proof.
{ revert cut. induction v; intros cut; simpl; try f_equal; auto.
  destruct (cut <=? v); auto. }
{ revert cut. induction c; intros cut; simpl; f_equal; auto. }
{ revert cut. induction h; intros cut; simpl; f_equal; auto. }
Qed.


Lemma inst_shift_0 cut I : inst_shift I 0 cut = I.
Proof.
  intros. induction I; simpl; f_equal; auto. apply v_shift_0.
Qed.

Lemma v_shift_shift n m cut v :
  v_shift (v_shift v n cut) m cut = (v_shift v (n + m) cut)
with c_shift_shift n m cut c :
  c_shift (c_shift c n cut) m cut = (c_shift c (n + m) cut)
with h_shift_shift n m cut h :
  h_shift (h_shift h n cut) m cut = (h_shift h (n + m) cut).
Proof.
{
revert cut. induction v; intros cut; simpl; f_equal; auto.
destruct (cut <=? v) eqn:cmp; simpl.
- apply (leb_complete _ _) in cmp.
  assert (cut <=? n + v = true) by (apply leb_correct; omega).
  rewrite H. f_equal. omega.
- rewrite cmp. reflexivity. }
{ revert cut. induction c; intros cut; try destruct p; simpl; f_equal; auto. }
{ revert cut. induction h; intros cut; simpl; f_equal; auto. }
Qed.

Lemma inst_shift_shift n m cut (I:instantiation) :
  inst_shift (inst_shift I n cut) m cut = inst_shift I (n+m) cut.
Proof.
intros. induction I; simpl; f_equal; auto. apply v_shift_shift.
Qed.


Fixpoint v_shift_comm n i j d (v:val) {struct v}:
  i >= j ->
  v_shift (v_shift v n i) d j = v_shift (v_shift v d j) n (d+i)

with c_shift_comm n i j d (c:comp) {struct c}:
  i >= j ->
  c_shift (c_shift c n i) d j = c_shift (c_shift c d j) n (d+i)

with h_shift_comm n i j d (h:hcases) {struct h}:
  i >= j ->
  h_shift (h_shift h n i) d j = h_shift (h_shift h d j) n (d+i).
Proof.
{
intros cmp. induction v; simpl.
{ clear v_shift_comm c_shift_comm h_shift_comm.
  rename v into dbi.
  destruct (i<=?dbi) eqn:cmpi; destruct (j<=?dbi) eqn:cmpj; simpl.
  + apply leb_complete in cmpi. apply leb_complete in cmpj.
    assert (j<=?n+dbi=true) by (apply leb_correct; omega).
    assert (d+i<=?d+dbi=true) by (apply leb_correct; omega).
    rewrite H, H0. f_equal. omega.
  + apply leb_complete in cmpi. apply leb_complete_conv in cmpj. omega.
  + apply leb_complete_conv in cmpi. rewrite cmpj. apply leb_complete in cmpj.
    assert (d+i<=?d+dbi=false) by (apply leb_correct_conv; omega).  
    rewrite H. reflexivity.
  + rewrite cmpj. 
    apply leb_complete_conv in cmpi. apply leb_complete_conv in cmpj.
    assert (d+i<=?dbi=false) by (apply leb_correct_conv; omega).
    rewrite H.  reflexivity.
}
clear v_shift_comm h_shift_comm.
all: f_equal; auto.
all: assert (S(d+i)=d+S i) by omega; rewrite H. 
all: eapply c_shift_comm; omega.
}{
intros cmp. induction c; simpl; f_equal; auto; 
clear v_shift_comm h_shift_comm.
all: assert (S(S(d+i))=d+S(S i)) by omega; 
  try (rewrite H; eapply c_shift_comm; omega).
all: assert (S(d+i)=d+S i) by omega; rewrite H0; eapply c_shift_comm; omega.
}{
clear v_shift_comm h_shift_comm.
intros cmp. induction h; simpl.
all: f_equal; auto.
assert (S(S(d+i))=d+S(S i)) by omega; rewrite H; eapply c_shift_comm; omega.
}
Qed.

Lemma inst_shift_comm n i j d (I:instantiation) :
  i>=j ->
  inst_shift (inst_shift I n i) d j = inst_shift (inst_shift I d j) n (d+i).
Proof.
intros. induction I; simpl; f_equal; auto. apply v_shift_comm. omega.
Qed.


Lemma v_negshift_shift n m cut (v:val) :
  (m <= n) ->
  v_negshift (v_shift v n cut) m cut = (v_shift v (n - m) cut)

with c_negshift_shift n m cut (c:comp) :
  (m <= n) ->
  c_negshift (c_shift c n cut) m cut = (c_shift c (n - m) cut)

with h_negshift_shift n m cut (h:hcases) :
  (m <= n) ->  
  h_negshift (h_shift h n cut) m cut = (h_shift h (n - m) cut).
Proof.
{
clear v_negshift_shift.
revert cut. induction v; intros cut m_le_n; simpl; f_equal; auto.
rename v into i. simpl. destruct (cut <=? i) eqn:cmp; simpl.
- apply leb_complete in cmp.
  assert (cut <=? n + i=true) by (apply leb_correct; omega).
  rewrite H. f_equal. omega.
- rewrite cmp. reflexivity.
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


Lemma v_shift_negshift_comm v n i j :
  v_no_var v j -> i <= j ->
    v_shift (v_negshift v 1 j) n i 
  = v_negshift (v_shift v n i) 1 (n+j)

with c_shift_negshift_comm c n i j :
  c_no_var c j -> i <= j ->
    c_shift (c_negshift c 1 j) n i 
  = c_negshift (c_shift c n i) 1 (n+j)

with h_shift_negshift_comm h n i j :
  h_no_var h j -> i <= j ->
    h_shift (h_negshift h 1 j) n i 
  = h_negshift (h_shift h n i) 1 (n+j).
Proof.
{
clear v_shift_negshift_comm.
revert j; induction v; intros j novar cmpij; simpl.
{ 
rename v into d. simpl. destruct (j<=?d) eqn:jd.
+ apply leb_complete in jd. 
  assert (i<=?d=true) by (apply leb_correct; omega).
  rewrite H. simpl. assert (n+j<=?n+d=true) by (apply leb_correct; omega).
  rewrite H0. assert (i<=?d-1=true).
  { apply leb_correct. simpl in novar. omega. }
  rewrite H1. f_equal. simpl in novar. omega.
+ apply leb_complete_conv in jd. simpl.
  destruct (i<=?d) eqn:id; simpl.
  - assert (n+j<=?n+d=false) by (apply leb_correct_conv; omega).
    rewrite H. reflexivity.
  - assert (n+j<=?d=false) by (apply leb_correct_conv; omega).
    rewrite H. reflexivity.
}
all : f_equal; simpl in novar; try destruct novar; auto.
all : assert (S(n+j)=n+(S j)) as snj by omega; rewrite snj.
all : apply c_shift_negshift_comm; omega || auto.
}{
clear h_shift_negshift_comm.
revert j. destruct c; intros j novar cmpij; simpl in *; f_equal; auto.
all : assert (S(S(n+j))=n+(S (S j))) as ssnj by omega; try rewrite ssnj.
all : assert (S(n+j)=n+(S j)) as snj by omega; try rewrite snj.
all: apply v_shift_negshift_comm || apply c_shift_negshift_comm.
all: omega || (try destruct novar; auto).
all: destruct H0; auto.
}{
clear h_shift_negshift_comm v_shift_negshift_comm.
revert j. induction h; intros j novar cmpij; simpl; f_equal. auto.
+ inv novar; auto.
+ assert (S(S(n+j))=n+(S (S j))) as ssnj by omega; try rewrite ssnj.
  apply c_shift_negshift_comm. inv novar. auto. omega.
}
Qed.

Lemma inst_shift_negshift_comm I n i j :
  inst_no_var I j -> i <= j ->
    inst_shift (inst_negshift I 1 j) n i 
  = inst_negshift (inst_shift I n i) 1 (n+j).
Proof.
revert n i j. induction I; intros; simpl; f_equal. auto.
all: simpl in H; destruct H. auto.
apply v_shift_negshift_comm. auto. omega.
Qed.


Lemma v_shift_negshift_comm_alt v i j :
  v_no_var v j -> j < i ->
    v_shift (v_negshift v 1 j) 1 i 
  = v_negshift (v_shift v 1 (1+i)) 1 j

with c_shift_negshift_comm_alt c i j :
  c_no_var c j -> j < i ->
    c_shift (c_negshift c 1 j) 1 i 
  = c_negshift (c_shift c 1 (1+i)) 1 j

with h_shift_negshift_comm_alt h i j :
  h_no_var h j -> j < i ->
    h_shift (h_negshift h 1 j) 1 i 
  = h_negshift (h_shift h 1 (1+i)) 1 j.
Proof.
{
clear v_shift_negshift_comm_alt.
revert j; induction v; intros j novar cmpij.
{ 
assert (1+i=i+1) as hack by omega. rewrite hack.
rename v into d. simpl. destruct (j<=?d) eqn:jd.
+ apply leb_complete in jd. simpl in novar.
  destruct (i+1<=?d) eqn:sid; simpl.
  - assert (j<=? S d=true) by (apply leb_correct; omega).
    rewrite H. destruct d; simpl. omega. apply leb_complete in sid.
    assert (i<=?d-0=true) by (apply leb_correct; omega).
    rewrite H0. f_equal. omega.
  - apply leb_complete_conv in sid. apply leb_correct in jd as jd'.
    rewrite jd'. destruct d. omega. 
    assert (i<=?S d-1=false) by (apply leb_correct_conv; omega). 
    rewrite H. reflexivity.
+ simpl. apply leb_complete_conv in jd as jd'. 
  assert (i<=?d=false) by (apply leb_correct_conv; omega). rewrite H.
  assert (i+1<=?d=false) by (apply leb_correct_conv; omega). rewrite H0.
  simpl. rewrite jd. reflexivity.
}
all : simpl; auto; f_equal; simpl in novar; try destruct novar; auto.
all : apply c_shift_negshift_comm_alt; omega || auto.
}{
clear h_shift_negshift_comm_alt.
revert j. destruct c; intros j novar cmpij; simpl in *; f_equal; auto.
all: apply v_shift_negshift_comm_alt || apply c_shift_negshift_comm_alt; auto.
all: omega || (try destruct novar; auto).
all: destruct H0; auto.
}{
clear v_shift_negshift_comm_alt. 
revert j. induction h; intros j novar cmpij; simpl in *; f_equal. auto.
all: destruct novar; auto. apply c_shift_negshift_comm_alt. auto. omega.
}
Qed.

(* ==================== novar interactions ==================== *)

Lemma v_shift_makes_no_var v j:
  v_no_var (v_shift v 1 j) j
with c_shift_makes_no_var c j:
  c_no_var (c_shift c 1 j) j
with h_shift_makes_no_var h j:
  h_no_var (h_shift h 1 j) j.
Proof.
{clear v_shift_makes_no_var.
revert j; induction v; intros j; simpl; auto.
destruct (j<=?v) eqn:cmp; simpl.
+ apply leb_complete in cmp. omega.
+ apply leb_iff_conv in cmp. omega. }
{revert j; induction c; intros j; try destruct p; simpl; auto. }
{revert j; induction h; intros j; simpl; auto. }
Qed.


Lemma v_no_var_shift (v:val) j n cut:
  v_no_var v j -> (cut <= j) -> v_no_var (v_shift v n cut) (n+j)
with c_no_var_shift (c:comp) j n cut:
  c_no_var c j -> (cut <= j) -> c_no_var (c_shift c n cut) (n+j)
with h_no_var_shift (h:hcases) j n cut:
  h_no_var h j -> (cut <= j) -> h_no_var (h_shift h n cut) (n+j).
Proof.
all: assert (forall j, S(n+j)=n+(S j)) as snj by (intro; omega).
all: assert (forall j, S(S(n+j))=n+(S(S j))) as ssnj by (intro; omega).
{
clear v_no_var_shift.
revert j. induction v; intros j orig cmpjc; simpl; simpl in orig;
try constructor; try inv orig; auto.
{ destruct (cut <=? v) eqn:cmp; simpl; try rewrite leb_iff_conv in cmp; omega. }
all: rewrite snj; apply c_no_var_shift; omega || assumption.
}{
clear c_no_var_shift.
revert j cut. induction c; intros j cut orig cmpjc; simpl; simpl in *.
all: try inv orig; try constructor; try constructor; auto.
all: try rewrite ssnj; try rewrite snj.
all: try apply IHc || apply IHc1 || apply IHc2; omega || auto.
all: inv H0; assumption.
}{
clear h_no_var_shift.
revert j cut. induction h; intros j cut orig cmpjc; simpl;
destruct orig; auto. constructor. auto.
rewrite ssnj. apply c_no_var_shift. assumption. omega.
}
Qed.


Lemma inst_no_var_shift I j n cut:
  inst_no_var I j -> (cut <= j) -> inst_no_var (inst_shift I n cut) (n+j).
Proof.
revert j n cut. induction I; intros; simpl; auto.
simpl in H. destruct H. constructor; eauto.
apply v_no_var_shift. auto. omega.
Qed.


Lemma v_no_var_shift_alt (v:val) j n cut:
  v_no_var v j -> (cut > j) -> v_no_var (v_shift v n cut) j
with c_no_var_shift_alt (c:comp) j n cut:
  c_no_var c j -> (cut > j) -> c_no_var (c_shift c n cut) j
with h_no_var_shift_alt (h:hcases) j n cut:
  h_no_var h j -> (cut > j) -> h_no_var (h_shift h n cut) j.
Proof.
{
clear v_no_var_shift_alt.
revert j. induction v; intros j orig cmpjc; simpl; simpl in orig;
try constructor; try inv orig; auto.
{ destruct (cut <=? v) eqn:cmp; simpl; omega || auto.
  rewrite leb_iff in cmp; omega. }
all: apply c_no_var_shift_alt; omega || assumption.
}{
clear c_no_var_shift_alt.
revert j cut. induction c; intros j cut orig cmpjc; simpl; simpl in *.
all: try inv orig; try constructor; try constructor; auto.
all: try apply IHc || apply IHc1 || apply IHc2; omega || auto.
all: inv H0; assumption.
}{
clear h_no_var_shift_alt.
revert j cut. induction h; intros j cut orig cmpjc; simpl;
destruct orig; auto. constructor. auto. apply c_no_var_shift_alt; omega || auto.
}
Qed.


Lemma v_sub_makes_no_var (v:val) j v_s :
  v_no_var v_s j -> v_no_var (v_sub v (j, v_s)) j
with c_sub_makes_no_var (c:comp) j v_s :
  v_no_var v_s j -> c_no_var (c_sub c (j, v_s)) j
with h_sub_makes_no_var (h:hcases) j v_s :
  v_no_var v_s j -> h_no_var (h_sub h (j, v_s)) j.
Proof.
{
clear v_sub_makes_no_var.
revert j. induction v; intros j v_s_clean; try constructor.
all: try (apply IHv; assumption); auto.
{simpl. destruct (v =? j) eqn:vj; auto. simpl. apply Nat.eqb_neq in vj. omega. }
all: apply c_sub_makes_no_var; apply v_no_var_shift; omega || assumption.
}{
clear c_sub_makes_no_var.
revert j v_s. induction c; intros j v_s v_s_clean; simpl.
all: try constructor; try constructor; auto.
all: try apply IHc || apply IHc1 || apply IHc2; auto.
all: assert (S(S j)=2+j) as ssj by omega; try rewrite ssj.
all: try apply v_no_var_shift; omega || auto.
}{
clear h_sub_makes_no_var.
revert j v_s. induction h; intros j v_s v_s_clean; simpl; auto.
constructor. auto. assert (S(S j)=2+j) as ssj by omega. rewrite ssj.
apply c_sub_makes_no_var. apply v_no_var_shift. assumption. omega.
}
Qed.


Lemma inst_sub_makes_no_var I j v_s :
  v_no_var v_s j -> inst_no_var (inst_sub I (j, v_s)) j.
Proof.
revert j. induction I; intros; simpl. auto. constructor.
+ apply v_sub_makes_no_var. auto.
+ auto.
Qed.


Fixpoint v_under_var_shift v j n cut:
  v_under_var v j -> cut <= j -> v_under_var (v_shift v n cut) (n+j)
with c_under_var_shift c j n cut:
  c_under_var c j -> cut <= j -> c_under_var (c_shift c n cut) (n+j)
with h_under_var_shift h j n cut:
  h_under_var h j -> cut <= j -> h_under_var (h_shift h n cut) (n+j).
Proof.
all: assert (S(n+j)=n+S j) as Snj by omega.
all: assert (S(S(n+j))=n+S(S j)) as SSnj by omega.
{
intros under cmp. destruct v; simpl; simpl in under; auto.
{ destruct (cut <=? v) eqn:ccmp; simpl; omega. }
all: try (destruct under; constructor; auto).
all: rewrite Snj; eapply c_under_var_shift; eauto; omega.
}{
intros under cmp. destruct c; simpl; simpl in under; auto.
all: try (destruct under; constructor; auto).
all: try rewrite SSnj; try rewrite Snj.
2: destruct H0; constructor.
4: destruct H0; constructor.
all: eapply c_under_var_shift; eauto; omega.
}{
intros under cmp. destruct h; simpl; simpl in under. auto.
destruct under. constructor. auto.
rewrite SSnj. eapply c_under_var_shift; eauto; omega.
}
Qed.


Fixpoint v_shift_too_high v n cut :
  v_under_var v cut -> v_shift v n cut = v
with c_shift_too_high c n cut :
  c_under_var c cut -> c_shift c n cut = c
with h_shift_too_high h n cut :
  h_under_var h cut -> h_shift h n cut = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ assert (cut <=? v = false) by (apply leb_correct_conv; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto); destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.


Fixpoint v_negshift_too_high v n cut :
  v_under_var v cut -> v_negshift v n cut = v
with c_negshift_too_high c n cut :
  c_under_var c cut -> c_negshift c n cut = c
with h_negshift_too_high h n cut :
  h_under_var h cut -> h_negshift h n cut = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ assert (cut <=? v = false) by (apply leb_correct_conv; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto); destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.


Fixpoint v_sub_too_high v i v_s:
  v_under_var v i -> v_sub v (i, v_s) = v
with c_sub_too_high c i v_s:
  c_under_var c i -> c_sub c (i, v_s) = c
with h_sub_too_high h i v_s:
  h_under_var h i -> h_sub h (i, v_s) = h.
Proof.
{
intros under. destruct v; simpl; simpl in under.
{ assert (v=?i=false) by (apply Nat.eqb_neq; omega).
  rewrite H. reflexivity. }
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}{
intros under. destruct c; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto); destruct H0; auto.
}{
intros under. destruct h; simpl; simpl in under.
all: try (destruct under; f_equal; auto) || (f_equal; auto).
}
Qed.

Fixpoint v_subs_too_high v i v_s:
v_under_var v i -> v_subs v i v_s = v
with c_subs_too_high c i v_s:
c_under_var c i -> c_subs c i v_s = c
with h_subs_too_high h i v_s:
h_under_var h i -> h_subs h i v_s = h.
Proof.
{
intros under. unfold v_subs. 
rewrite v_sub_too_high, v_negshift_too_high; auto.
}{
intros under. unfold c_subs. 
rewrite c_sub_too_high, c_negshift_too_high; auto.
}{
intros under. unfold h_subs. 
rewrite h_sub_too_high, h_negshift_too_high; auto.
}
Qed.



Fixpoint v_sub_no_var v v' i {struct v}:
  v_no_var v i -> v_sub v (i, v') = v
with c_sub_no_var c v' i {struct c}:
  c_no_var c i -> c_sub c (i, v') = c
with h_sub_no_var h v' i {struct h}:
  h_no_var h i -> h_sub h (i, v') = h.
Proof.
all: revert i.
+ intros i novar. destruct v; simpl in novar. 
  { assert (v=?i=false) by (apply Nat.eqb_neq; omega).
    simpl. rewrite H. reflexivity. }
  all: try destruct novar; simpl in *; f_equal; auto.
+ intros i novar. induction c; simpl in *; try destruct novar.
  all: f_equal; auto. all: destruct H0; auto.
+ intros i novar. induction h; simpl in *; try destruct novar.
  all: f_equal; auto.
Qed.

(* ==================== Sub Interactions ==================== *)

Lemma v_shift_sub v v' i cut j :
  cut <= j ->
    v_shift (v_sub v (j, v')) i cut 
  = v_sub (v_shift v i cut) (i+j, v_shift v' i cut)

with c_shift_sub c v' i cut j :
  cut <= j ->
    c_shift (c_sub c (j, v')) i cut 
  = c_sub (c_shift c i cut) (i+j, v_shift v' i cut)

with h_shift_sub h v' i cut j :
  cut <= j ->
    h_shift (h_sub h (j, v')) i cut
  = h_sub (h_shift h i cut) (i+j, v_shift v' i cut).
Proof.
all : assert (S(i+j)=i+(S j)) as sij by omega.
all : assert (S(S(i+j))=i+(S (S j))) as ssij by omega.
{
revert cut; induction v; intros cut cmpcj; simpl.
{ simpl. destruct (cut<=?v) eqn:cv.
  + destruct (v=?j) eqn:vj.
    * apply Nat.eqb_eq in vj. subst. simpl.
      assert (i+j=?i+j=true) by (apply Nat.eqb_eq; omega).
      rewrite H. reflexivity.
    * simpl. rewrite cv. assert (i+v=?i+j=false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in vj. omega. }
      rewrite H. reflexivity.
  + assert (v=?j=false).
    { apply Nat.eqb_neq. apply leb_complete_conv in cv. omega. }
    rewrite H. simpl. rewrite cv.
    assert (v=?i+j=false).
    { apply Nat.eqb_neq. apply leb_complete_conv in cv. omega. }
    rewrite H0. reflexivity.
}
all : f_equal; auto.
all : rewrite sij, v_shift_comm, c_shift_sub; try omega || f_equal.
}{
clear h_shift_sub.
revert cut; induction c; intros cut cmpcj; simpl; f_equal; auto.
all : try rewrite ssij; try rewrite sij.
all: rewrite v_shift_comm, c_shift_sub; try omega || f_equal.
}{
clear v_shift_sub h_shift_sub.
revert cut; induction h; intros cut cmpcj; simpl; f_equal; auto.
+ rewrite ssij, v_shift_comm, c_shift_sub; try omega || f_equal.
}
Qed.


Lemma inst_shift_sub I v' i cut j :
  cut <= j ->
    inst_shift (inst_sub I (j, v')) i cut 
  = inst_sub (inst_shift I i cut) (i+j, v_shift v' i cut).
Proof.
revert i cut j. induction I; intros; simpl; f_equal; auto.
apply v_shift_sub. omega.
Qed.


Lemma v_negshift_sub v v' cut j :
  cut < j -> v_no_var v cut -> v_no_var v' cut ->
    v_negshift (v_sub v (j, v')) 1 cut 
  = v_sub (v_negshift v 1 cut) (j-1, v_negshift v' 1 cut)

with c_negshift_sub c v' cut j :
  cut < j -> c_no_var c cut -> v_no_var v' cut ->
    c_negshift (c_sub c (j, v')) 1 cut 
  = c_sub (c_negshift c 1 cut) (j-1, v_negshift v' 1 cut)

with h_negshift_sub h v' cut j :
  cut < j -> h_no_var h cut -> v_no_var v' cut ->
    h_negshift (h_sub h (j, v')) 1 cut
  = h_sub (h_negshift h 1 cut) (j-1, v_negshift v' 1 cut).
Proof.
{
revert cut j; induction v; intros cut j cmpcj novar novar'; simpl.
{ 
rename v into d. simpl. simpl in novar.
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
all : simpl in novar; try (destruct novar; auto); f_equal; auto.
all : rewrite c_negshift_sub; try omega || (f_equal; f_equal; omega || auto).
all : clear v_negshift_sub c_negshift_sub h_negshift_sub.
all : try rewrite v_shift_negshift_comm; f_equal || omega || auto.
all : apply v_no_var_shift; omega || auto.
}{
clear h_negshift_sub.
revert cut j; induction c; intros cut j cmpcj novar novar'; simpl.
all : simpl in novar; try destruct novar; f_equal; auto.
all : clear v_negshift_sub.
all : assert (S(S cut)=2+cut) as ssc by omega; try rewrite ssc.
all : assert (S cut=1+cut) as sc by omega; try rewrite sc.
all : try destruct H0.
all : try rewrite c_negshift_sub; (f_equal; f_equal; try omega) || auto.
all : try rewrite v_shift_negshift_comm; f_equal || omega || auto.
all : try apply v_no_var_shift; omega || auto.
}{
clear v_negshift_sub h_negshift_sub.
revert cut j; induction h; intros cut j cmpcj novar novar'.
all : simpl; f_equal; simpl in novar; try destruct novar; auto.
try rewrite c_negshift_sub. f_equal. f_equal. all: omega || auto.
rewrite v_shift_negshift_comm. f_equal. assumption. omega.
assert (S(S cut)=2+cut) as cc by omega; rewrite cc.
apply v_no_var_shift. assumption. omega.
}
Qed.


Lemma v_sub_sub v v1 v2 i j :
  v_no_var v j ->
    v_sub v (i, v_sub v1 (j, v2))
  = v_sub (v_sub v (i, v1)) (j, v2)

with c_sub_sub c v1 v2 i j :
  c_no_var c j ->
    c_sub c (i, v_sub v1 (j, v2))
  = c_sub (c_sub c (i, v1)) (j, v2)

with h_sub_sub h v1 v2 i j :
  h_no_var h j ->
    h_sub h (i, v_sub v1 (j, v2))
  = h_sub (h_sub h (i, v1)) (j, v2).
Proof.
{
revert i j; induction v; intros i j novar; simpl.
{ simpl. destruct (v=?i) eqn:cv. reflexivity.
  simpl in *. assert (v=?j=false) by (apply Nat.eqb_neq; omega).
  rewrite H. reflexivity. }
all : simpl in novar; try destruct novar; f_equal; auto.
all : rewrite v_shift_sub, c_sub_sub; omega || auto.
}{
clear h_sub_sub.
revert i j; induction c; intros i j novar; simpl.
all : f_equal; simpl in novar; try destruct novar; auto.
4: destruct H0; auto.
all : rewrite v_shift_sub, c_sub_sub; omega || auto.
all : destruct H0; auto.
}{
clear v_sub_sub h_sub_sub.
revert i j; induction h; intros i j novar; simpl.
all : simpl in novar; f_equal; try destruct novar; auto.
rewrite v_shift_sub, c_sub_sub; omega || auto.
}
Qed.

(* ==================== Full Subs Properties ==================== *)

Fixpoint v_under_var_subs v v' i j {struct v}:
  v_under_var v (S i) -> v_under_var v' i -> j <= i ->
  v_under_var (v_subs v j v') i
with c_under_var_subs c v' i j {struct c}:
  c_under_var c (S i) -> v_under_var v' i -> j <= i ->
  c_under_var (c_subs c j v') i
with h_under_var_subs h v' i j {struct h}:
  h_under_var h (S i) -> v_under_var v' i -> j <= i ->
  h_under_var (h_subs h j v') i.
Proof.
all: revert i j.
+ intros. destruct v.
  { unfold v_subs. simpl. simpl in H. destruct (v=?j) eqn:vj.
    + rewrite v_negshift_shift, v_shift_0. auto. omega.
    + simpl. destruct (j<=?v) eqn:cmp; simpl; apply Nat.eqb_neq in vj.
      apply leb_complete in cmp. omega.
      apply leb_complete_conv in cmp. omega. }
  all: simpl in *; try inv H; try constructor.
  all: try apply v_under_var_subs || apply h_under_var_subs; auto.
  all: rewrite v_shift_comm; apply c_under_var_subs || omega; omega || auto.
  all: apply v_under_var_shift; omega || assumption.
+ intros. induction c; simpl in *; auto.
  all: try constructor; try constructor; try inv H; auto.
  all: try apply v_under_var_subs; eauto.
  all: try destruct H3; eauto.
  all: rewrite v_shift_comm; try apply c_under_var_subs; omega || auto.
  all: try apply v_under_var_shift; omega || (try destruct H2; auto).
  all: assert (S(S i) = 2+i) as same by omega; rewrite same.
  all: apply v_under_var_shift; omega || assumption.
+ intros. induction h; simpl in *; auto.
  constructor; inv H; auto.
  rewrite v_shift_comm; try apply c_under_var_subs; omega || auto.
  assert (S(S i) = 2+i) by omega; rewrite H; apply v_under_var_shift.
  assumption. omega.
Qed.


Fixpoint v_no_var_subs v v' i j {struct v}:
  v_no_var v (1+i) -> v_no_var v' i -> j<=i ->
  v_no_var (v_subs v j v') i

with c_no_var_subs c v' i j {struct c}:
  c_no_var c (1+i) -> v_no_var v' i -> j<=i ->
  c_no_var (c_subs c j v') i

with h_no_var_subs h v' i j {struct h}:
  h_no_var h (1+i) -> v_no_var v' i -> j<=i ->
  h_no_var (h_subs h j v') i.
Proof.
all: revert i j.
+ intros. destruct v.
  { unfold v_subs. simpl. simpl in H.
    destruct (v=?j) eqn:vj.
    + rewrite v_negshift_shift, v_shift_0. auto. omega.
    + simpl. destruct (j<=?v) eqn:jlv; simpl; apply Nat.eqb_neq in vj.
      - apply leb_complete in jlv. omega.
      - apply leb_complete_conv in jlv. omega. }
  all: simpl in *; try inv H; try constructor.
  all: try apply v_no_var_subs || apply h_no_var_subs; auto.
  all: rewrite v_shift_comm; apply c_no_var_subs || omega; omega || auto.
  all: apply v_no_var_shift; omega || assumption.
+ intros. induction c; simpl in *; try constructor; try constructor.
  all: try inv H; try inv H3; auto.
  all: try apply v_no_var_subs; eauto.
  all: rewrite v_shift_comm; try apply c_no_var_subs; omega || auto.
  all: try apply v_no_var_shift; omega || auto.
  all: assert (S(S i) = 2+i) as same by omega; rewrite same.
  all: apply v_no_var_shift; omega || assumption.
+ intros. induction h; simpl in *; auto. inv H; constructor; auto.
  rewrite v_shift_comm; try apply c_no_var_subs; omega || auto.
  assert (S(S i) = 2+i) by omega; rewrite H; apply v_no_var_shift.
  assumption. omega.
Qed.


Lemma v_shift_subs v v' i j (safe: j <= i): 
    v_shift (v_subs v j v') 1 i
  = (v_subs (v_shift v 1 (1+i)) j (v_shift v' 1 i))

with c_shift_subs c v' i j (safe: j <= i): 
    c_shift (c_subs c j v') 1 i
  = (c_subs (c_shift c 1 (1+i)) j (v_shift v' 1 i))

with h_shift_subs h v' i j (safe: j <= i): 
    h_shift (h_subs h j v') 1 i
  = (h_subs (h_shift h 1 (1+i)) j (v_shift v' 1 i)).
Proof.
{
induction v; unfold v_subs; simpl.
{
clear v_shift_subs c_shift_subs h_shift_subs.
rename v into n.
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
+ destruct (i=?j) eqn:eqij.
  - apply Nat.eqb_eq in eqij. subst.
    assert (1+j<=?j=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; reflexivity).
    rewrite H0. simpl. 
    rewrite v_negshift_shift, v_negshift_shift, v_shift_shift, v_shift_shift. f_equal. omega. omega.
  - assert (1+i<=?i=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H. simpl. apply leb_correct in safe as s.
    rewrite s, eqij. simpl. rewrite s. assert (i<=?i-1=false).
    { apply leb_correct_conv. apply Nat.eqb_neq in eqij. omega. } 
    rewrite H0. reflexivity.
+ destruct (n=?j) eqn:nj.
  * apply Nat.eqb_eq in nj. subst.
    assert (1+i<=?j=false) by (apply leb_correct_conv; omega).
    simpl in H. rewrite H. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    reflexivity. omega. omega.
  * destruct (i<=?n) eqn:iln; simpl.
    - apply leb_complete in iln.
      assert (j<=?n=true) by (apply leb_correct; omega). rewrite H. simpl.
      assert (i<=?n-1=true).
      { apply leb_correct. apply Nat.eqb_neq in ni. omega. }
      rewrite H0. simpl. assert (1+i<=?n=true).
      { apply leb_correct. apply Nat.eqb_neq in ni. omega. }
      simpl in H1. rewrite H1. simpl. 
      assert (1+n=?j=false) by (apply Nat.eqb_neq; omega).
      simpl in H2. rewrite H2. simpl. assert (j<=? S n=true).
      { apply leb_correct. omega. }
      rewrite H3. do 2 f_equal. apply Nat.eqb_neq in ni. omega.
    - apply leb_complete_conv in iln.
      assert (1+i<=?n=false) by (apply leb_correct_conv; omega).
      simpl in H. rewrite H. simpl. rewrite nj. simpl.
      destruct (j<=?n) eqn:jln.
      simpl. assert (i<=?n-1=false) by (apply leb_correct_conv; omega).
      rewrite H0. reflexivity.
      simpl. assert (i<=?n=false) by (apply leb_correct_conv; omega).
      rewrite H0. reflexivity.
}
all: f_equal; auto.
3: apply h_shift_subs; auto.
all: clear v_shift_subs h_shift_subs; unfold c_subs in c_shift_subs.
all: rewrite v_shift_comm; try omega.
all: rewrite c_shift_subs; clear c_shift_subs; try omega.
all: do 3 f_equal; rewrite (v_shift_comm 1 j); f_equal; try omega.
all: rewrite (v_shift_comm 1 i); f_equal; omega.
}{
destruct c; unfold c_subs; simpl; f_equal;
try apply v_shift_subs; try assumption.
all: clear v_shift_subs h_shift_subs; unfold c_subs in c_shift_subs.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j)).
  all: f_equal||omega||auto. 
  rewrite (v_shift_comm 1 i), (v_shift_comm 1 (1+i)). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs. clear c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 j), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs. clear c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 j), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 i). reflexivity. all: omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j)).
  all: f_equal||omega||auto. 
  rewrite (v_shift_comm 1 i), (v_shift_comm 1 (1+i)). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs. clear c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 j), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j)).
  all: f_equal||omega||auto. 
  rewrite (v_shift_comm 1 i), (v_shift_comm 1 (1+i)). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs. clear c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 j), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite v_shift_comm. rewrite c_shift_subs. clear c_shift_subs.
  do 2 f_equal. rewrite (v_shift_comm). reflexivity. all: omega.
+ rewrite v_shift_comm, c_shift_subs. clear c_shift_subs. do 3 f_equal.
  rewrite (v_shift_comm 1 j), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite v_shift_comm. rewrite c_shift_subs. clear c_shift_subs.
  do 2 f_equal. rewrite (v_shift_comm). reflexivity. all: omega.
}{
destruct h; unfold h_subs; simpl. auto. f_equal.
+ apply h_shift_subs. assumption.
+ clear v_shift_subs h_shift_subs. unfold c_subs in c_shift_subs.
  rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs. clear c_shift_subs. simpl.
  do 2 f_equal. all: try omega. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j)).
  all: f_equal||omega||auto. 
  rewrite (v_shift_comm 1 i), (v_shift_comm 1 (1+i)). do 2 f_equal. all: omega.
}
Qed.


Lemma v_shift_subs_alt v v' i j (safe: i <= j): 
    v_shift (v_subs v j v') 1 i
  = (v_subs (v_shift v 1 i) (1+j) (v_shift v' 1 i))

with c_shift_subs_alt c v' i j (safe: i <= j): 
    c_shift (c_subs c j v') 1 i
  = (c_subs (c_shift c 1 i) (1+j) (v_shift v' 1 i))

with h_shift_subs_alt h v' i j (safe: i <= j): 
    h_shift (h_subs h j v') 1 i
  = (h_subs (h_shift h 1 i) (1+j) (v_shift v' 1 i)).
Proof.
{
induction v; unfold v_subs; simpl.
{
clear v_shift_subs_alt c_shift_subs_alt h_shift_subs_alt.
rename v into n.
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
+ destruct (i=?j) eqn:eqij.
  - assert (i<=?i=true) by (apply leb_correct; omega).
    rewrite H. simpl. rewrite eqij.
    rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    reflexivity. omega. omega.
  - assert (i<=?i=true) by (apply leb_correct; omega).
    simpl in H. rewrite H. simpl. apply Nat.eqb_neq in eqij as ijeq. 
    assert (j<=?i=false) by (apply leb_correct_conv; omega).
    rewrite H0, eqij. simpl. rewrite H, H0. reflexivity.
+ destruct (n=?j) eqn:nj.
  * apply Nat.eqb_eq in nj. subst.
    assert (i<=?j=true) by (apply leb_correct; omega).
    simpl in H. rewrite H. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    reflexivity. omega. omega.
  * destruct (i<=?n) eqn:iln; simpl.
    - apply leb_complete in iln.
      rewrite nj. simpl.
      destruct (j<=?n) eqn:jn; simpl. apply Nat.eqb_neq in ni.
      assert (i<=?n-1=true) by (apply leb_correct; omega).
      rewrite H. f_equal. f_equal. omega.
      apply leb_correct in iln. rewrite iln. reflexivity.
    - apply leb_complete_conv in iln.
      assert (j<=?n=false) by (apply leb_correct_conv; omega).
      assert (i<=?n=false) by (apply leb_correct_conv; omega).
      rewrite H. simpl. rewrite H0. simpl.
      assert (n=?S j=false) by (apply Nat.eqb_neq; omega).
      rewrite H1. simpl. 
      assert (S j<=?n=false) by (apply leb_correct_conv; omega).
      simpl in H2. rewrite H2. reflexivity.  
      }
all: f_equal; auto.
3: apply h_shift_subs_alt; auto.
all: clear v_shift_subs_alt h_shift_subs_alt; unfold c_subs in c_shift_subs_alt.
all: rewrite v_shift_comm; try omega.
all: rewrite c_shift_subs_alt; clear c_shift_subs_alt; try omega.
all: do 3 f_equal; rewrite (v_shift_comm 1 (S j)); f_equal; try omega.
all: rewrite (v_shift_comm 1 i); f_equal; omega.
}{
destruct c; unfold c_subs; simpl; f_equal;
try apply v_shift_subs_alt; try assumption.
all: clear v_shift_subs_alt h_shift_subs_alt; unfold c_subs in c_shift_subs_alt.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs_alt. clear c_shift_subs_alt. simpl. do 2 f_equal. all: try omega. f_equal. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 (S j)).
  rewrite (v_shift_comm 1 (1+S j)). all: f_equal||omega||auto. 
  rewrite v_shift_shift, v_shift_shift, (v_shift_comm _ i).
  reflexivity. omega.
+ rewrite v_shift_comm, c_shift_subs_alt. clear c_shift_subs_alt. do 3 f_equal.
  rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite v_shift_comm, c_shift_subs_alt. clear c_shift_subs_alt. do 3 f_equal.
  rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite <-v_shift_comm. rewrite c_shift_subs_alt. clear c_shift_subs_alt.
  do 2 f_equal. rewrite <-v_shift_comm. reflexivity. all: omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs_alt. clear c_shift_subs_alt. simpl. do 2 f_equal. all: try omega. f_equal. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 (S j)).
  rewrite (v_shift_comm 1 (1+S j)). all: f_equal||omega||auto. 
  rewrite v_shift_shift, v_shift_shift, (v_shift_comm _ i).
  reflexivity. omega.
+ rewrite v_shift_comm, c_shift_subs_alt. clear c_shift_subs_alt. do 3 f_equal.
  rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs_alt. clear c_shift_subs_alt. simpl. do 2 f_equal. all: try omega. f_equal. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 (S j)).
  rewrite (v_shift_comm 1 (1+S j)). all: f_equal||omega||auto. 
  rewrite v_shift_shift, v_shift_shift, (v_shift_comm _ i).
  reflexivity. omega.
+ rewrite v_shift_comm, c_shift_subs_alt. clear c_shift_subs_alt. do 3 f_equal.
  rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite <-v_shift_comm. rewrite c_shift_subs_alt. clear c_shift_subs_alt.
  do 2 f_equal. rewrite <-v_shift_comm. reflexivity. all: omega.
+ rewrite v_shift_comm, c_shift_subs_alt. clear c_shift_subs_alt. do 3 f_equal.
  rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i). do 2 f_equal. all: omega.
+ rewrite <-v_shift_comm. rewrite c_shift_subs_alt. clear c_shift_subs_alt.
  do 2 f_equal. rewrite <-v_shift_comm. reflexivity. all: omega.
}{
destruct h; unfold h_subs; simpl. auto. f_equal.
+ apply h_shift_subs_alt. assumption.
+ clear v_shift_subs_alt h_shift_subs_alt. unfold c_subs in c_shift_subs_alt.
  rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_shift_subs_alt. clear c_shift_subs_alt. simpl. do 2 f_equal. all: try omega. f_equal. 
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 (S j)).
  rewrite (v_shift_comm 1 (1+S j)). all: f_equal||omega||auto. 
  rewrite v_shift_shift, v_shift_shift, (v_shift_comm _ i).
  reflexivity. omega.
}
Qed.



Lemma v_negshift_subs v v' i j (safe: j <= i): 
  v_no_var v (1+i) -> v_no_var v' i ->
    v_negshift (v_subs v j v') 1 i
  = (v_subs (v_negshift v 1 (1+i)) j (v_negshift v' 1 i))
  
with c_negshift_subs c v' i j (safe: j <= i): 
  c_no_var c (1+i) -> v_no_var v' (i) ->
    c_negshift (c_subs c j v') 1 i
  = (c_subs (c_negshift c 1 (1+i)) j (v_negshift v' 1 i))
  
with h_negshift_subs h v' i j (safe: j <= i): 
  h_no_var h (1+i) -> v_no_var v' (i) ->
    h_negshift (h_subs h j v') 1 i
  = (h_subs (h_negshift h 1 (1+i)) j (v_negshift v' 1 i)).
Proof.
{
intros nov nov'. destruct v; unfold v_subs; simpl.
{ clear v_negshift_subs c_negshift_subs h_negshift_subs.
  rename v into n. destruct (n=?j) eqn:nj.
  apply Nat.eqb_eq in nj. subst.
  destruct (1+i <=? j) eqn:cmpij.
  3 : destruct (1+i <=? n) eqn:Sin. all: simpl.
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
all: try destruct nov; apply h_negshift_subs || auto; auto.
all: unfold c_subs in c_negshift_subs; rewrite v_shift_comm; try omega.
all: rewrite (c_negshift_subs c _ (S i) (S j)); clear c_negshift_subs.
all: omega || (apply v_no_var_shift; omega || auto) || auto.
all: rewrite v_shift_comm; do 4 f_equal; try rewrite v_shift_negshift_comm.
all: omega || auto.
}{
induction c; intros nov nov'; unfold c_subs; simpl in nov |-*; f_equal;
try apply v_negshift_subs; try assumption.
all: clear v_negshift_subs h_negshift_subs.
all: try (destruct nov; assumption).
all: unfold c_subs in c_negshift_subs; inv nov; try destruct H0.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j); try omega.
  rewrite (v_shift_comm 1 (1+j)), c_negshift_subs; omega || auto. do 3 f_equal.
  rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j));
  try omega || f_equal; rewrite v_shift_shift, v_shift_shift.
  rewrite v_shift_negshift_comm; omega || auto.
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs; omega || auto.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite v_shift_comm. f_equal. rewrite v_shift_negshift_comm. 
  all: omega || auto. rewrite <-(v_shift_shift 1 1). 
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite v_shift_comm. f_equal. rewrite v_shift_negshift_comm. 
  all: omega || auto. rewrite <-(v_shift_shift 1 1). 
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs; omega || auto.
+ rewrite v_shift_comm, c_negshift_subs. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs; omega || auto.
}{
destruct h; unfold h_subs; intros nov nov'; simpl. auto. inv nov. f_equal.
+ apply h_negshift_subs; auto.
+ unfold c_subs in c_negshift_subs. clear v_negshift_subs h_negshift_subs.
  rewrite <-(v_shift_shift 1), (v_shift_comm 1 j).
  rewrite (v_shift_comm 1 (1+j)), c_negshift_subs. clear c_negshift_subs. rewrite <-(v_shift_shift 1 1 0), (v_shift_comm 1 j), (v_shift_comm 1 (1+j)). do 4 f_equal. rewrite v_shift_shift, v_shift_shift, v_shift_negshift_comm.
  all: try (apply v_no_var_shift; omega||apply v_no_var_shift); omega||auto.
}
Qed.



Lemma v_negshift_subs_alt v v' i j (safe: j >= i): 
  v_no_var v i -> v_no_var v' i ->
    v_negshift (v_subs v (1+j) v') 1 i
  = (v_subs (v_negshift v 1 i) j (v_negshift v' 1 i))
  
with c_negshift_subs_alt c v' i j (safe: j >= i): 
  c_no_var c i -> v_no_var v' (i) ->
    c_negshift (c_subs c (1+j) v') 1 i
  = (c_subs (c_negshift c 1 i) j (v_negshift v' 1 i))
  
with h_negshift_subs_alt h v' i j (safe: j >= i): 
  h_no_var h i -> v_no_var v' (i) ->
    h_negshift (h_subs h (1+j) v') 1 i
  = (h_subs (h_negshift h 1 i) j (v_negshift v' 1 i)).
Proof.
{
intros nov nov'. destruct v; unfold v_subs; simpl.
{ clear v_negshift_subs_alt c_negshift_subs_alt h_negshift_subs_alt.
  rename v into n. destruct (n=?S j) eqn:nSj.
  apply Nat.eqb_eq in nSj. subst.
  2 : destruct (i <=? n) eqn:cmpin. all: simpl.
  + assert(i<=?S j=true) by (apply leb_correct; omega).
    rewrite H. simpl.
    assert(j-0=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_shift_0, v_negshift_shift, v_shift_0.
    auto. omega. omega.
  + apply leb_complete in cmpin as ccmpin.
    apply Nat.eqb_neq in nSj as nnSj. simpl in nov.
    assert (n-1=?j=false) by (apply Nat.eqb_neq; omega).
    rewrite H. simpl.
    destruct (j <=? n-1) eqn:jnm1.
    - apply leb_complete in jnm1. 
      assert (S j<=?n=true) by (apply leb_correct; omega).
      simpl in H0. rewrite H0. simpl.
      assert (i<=?n-1=true) by (apply leb_correct; omega).
      rewrite H1. reflexivity.
    - apply leb_complete_conv in jnm1.
      assert (1+j<=?n=false) by (apply leb_correct_conv; omega).
      simpl in H0. rewrite H0. simpl. rewrite cmpin. reflexivity.
  + apply leb_complete_conv in cmpin as ccmpin.
    apply Nat.eqb_neq in nSj as nnSj. simpl in nov.
    assert (n=?j=false) by (apply Nat.eqb_neq; omega).
    rewrite H. simpl.
    assert (j<=?n=false) by (apply leb_correct_conv; omega).
    rewrite H0.
    assert (1+j<=?n=false) by (apply leb_correct_conv; omega).
    simpl in H1. rewrite H1. simpl. rewrite cmpin. reflexivity.
}
all: f_equal; simpl in nov.
all: try apply v_negshift_subs_alt; try omega || auto.
all: try destruct nov; apply h_negshift_subs_alt || auto; auto.
all: unfold c_subs in c_negshift_subs_alt; rewrite v_shift_comm; try omega.
all: rewrite (c_negshift_subs_alt c _ (S i) (S j)); clear c_negshift_subs_alt.
all: omega || (apply v_no_var_shift; omega || auto) || auto.
all: rewrite v_shift_comm; do 4 f_equal; try rewrite v_shift_negshift_comm.
all: omega || auto.
}{
destruct c; intros nov nov'; unfold c_subs; simpl in nov |-*; f_equal;
try apply v_negshift_subs_alt; try assumption.
all: clear v_negshift_subs_alt h_negshift_subs_alt.
all: try (destruct nov; assumption).
all: unfold c_subs in c_negshift_subs_alt; inv nov; try destruct H0.
+ rewrite <-(v_shift_shift 1), (v_shift_comm 1 j); try omega.
  rewrite (v_shift_comm 1 (1+j)), (v_shift_comm 1 (1+(1+j))).
  rewrite (c_negshift_subs_alt _ _). all: omega || auto. do 4 f_equal.
  rewrite (v_shift_shift), v_shift_negshift_comm. all: omega || auto.
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs_alt; omega || auto.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite v_shift_comm. f_equal. rewrite v_shift_negshift_comm. 
  all: omega || auto. rewrite <-(v_shift_shift 1 1). 
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite v_shift_comm. f_equal. rewrite v_shift_negshift_comm. 
  all: omega || auto. rewrite <-(v_shift_shift 1 1). 
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs_alt; omega || auto.
+ rewrite v_shift_comm, c_negshift_subs_alt. do 3 f_equal.
  rewrite <-v_shift_negshift_comm, <-v_shift_comm. all: omega || auto.
  apply v_no_var_shift. auto. omega.
+ apply c_negshift_subs_alt; omega || auto.
}{
destruct h; unfold h_subs; intros nov nov'; simpl. auto. inv nov. f_equal.
+ apply h_negshift_subs_alt; auto.
+ unfold c_subs in c_negshift_subs_alt. clear v_negshift_subs_alt h_negshift_subs_alt.
  rewrite <-(v_shift_shift 1), (v_shift_comm 1 j); try omega.
  rewrite (v_shift_comm 1 (1+j)), (v_shift_comm 1 (1+(1+j))).
  rewrite (c_negshift_subs_alt _ _). all: omega || auto. do 4 f_equal.
  rewrite (v_shift_shift), v_shift_negshift_comm. all: omega || auto.
  apply v_no_var_shift. apply v_no_var_shift. all: omega || auto.
}
Qed.


Lemma v_sub_subs v i j vi vj:
  j >= i ->
    v_sub (v_subs v i vi) (j, vj)
  = (v_subs (v_sub v (1+j, v_shift vj 1 i)) i (v_sub vi (j, vj)))

with c_sub_subs c i j vi vj: 
  j >= i ->
    c_sub (c_subs c i vi) (j, vj)
  = (c_subs (c_sub c (1+j, v_shift vj 1 i)) i (v_sub vi (j, vj)))

with h_sub_subs h i j vi vj: 
  j >= i ->
    h_sub (h_subs h i vi) (j, vj)
  = (h_subs (h_sub h (1+j, v_shift vj 1 i)) i (v_sub vi (j, vj))).
Proof.
{
intros cmp. induction v; unfold v_subs; simpl.
{
clear v_sub_subs c_sub_subs h_sub_subs.
rename v into n.
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
all: rewrite v_shift_comm, c_sub_subs; clear c_sub_subs; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
}{
intros cmp. induction c; unfold c_subs; simpl; f_equal; auto.
all: try apply v_sub_subs; try assumption.
all: clear v_sub_subs h_sub_subs; unfold c_subs in c_sub_subs.
all: try rewrite v_shift_comm, c_sub_subs; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
all: rewrite (v_shift_comm _ i); f_equal; try omega.
all: rewrite v_shift_sub; f_equal; omega.
}{
intros cmp. induction h; unfold h_subs; simpl; f_equal; auto.
unfold c_subs in c_sub_subs. rewrite v_shift_comm, c_sub_subs; try omega.
do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
rewrite (v_shift_comm _ i); f_equal; try omega.
rewrite v_shift_comm. f_equal. rewrite v_shift_sub. f_equal.
all: omega.
}
Qed.


Lemma v_sub_subs_alt v i j vi vj:
  j < i ->
    v_sub (v_subs v i vi) (j, vj)
  = (v_subs (v_sub v (j, v_shift vj 1 i)) i (v_sub vi (j, vj)))

with c_sub_subs_alt c i j vi vj: 
  j < i ->
    c_sub (c_subs c i vi) (j, vj)
  = (c_subs (c_sub c (j, v_shift vj 1 i)) i (v_sub vi (j, vj)))

with h_sub_subs_alt h i j vi vj: 
  j < i ->
    h_sub (h_subs h i vi) (j, vj)
  = (h_subs (h_sub h (j, v_shift vj 1 i)) i (v_sub vi (j, vj))).
Proof.
{
intros cmp. induction v; unfold v_subs; simpl.
{
clear v_sub_subs_alt c_sub_subs_alt h_sub_subs_alt.
rename v into n.
destruct (n=?i) eqn:ni.
apply Nat.eqb_eq in ni. subst.
+ assert (i=?j=false) by (apply Nat.eqb_neq; omega).
  rewrite H. simpl.
  assert (i=?i=true) by (apply Nat.eqb_eq; omega).
  rewrite H0, v_negshift_shift, v_negshift_shift.
  rewrite v_shift_0, v_shift_0. reflexivity. all: omega.
+ destruct (n=?j) eqn:nj.
  - apply Nat.eqb_eq in nj. subst. simpl.
    assert (i<=?j=false) by (apply leb_correct_conv; omega).
    rewrite H. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_sub_no_var, v_negshift_shift, v_shift_0.
    reflexivity. omega. apply v_shift_makes_no_var.
  - simpl. rewrite ni. simpl. destruct (i<=?n) eqn:cmpin.
    * simpl. assert (n-1=?j=false).
      { apply leb_complete in cmpin. apply Nat.eqb_neq.
        apply Nat.eqb_neq in nj. apply Nat.eqb_neq in ni. omega. }
      rewrite H. reflexivity.
    * simpl. rewrite nj. reflexivity. 
}
all: f_equal; auto.
3: apply h_sub_subs_alt; auto.
all: clear v_sub_subs_alt h_sub_subs_alt; unfold c_subs in c_sub_subs_alt.
all: rewrite v_shift_comm, c_sub_subs_alt; clear c_sub_subs_alt; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
}{
intros cmp. induction c; unfold c_subs; simpl; f_equal; auto.
all: try apply v_sub_subs_alt; try assumption.
all: clear v_sub_subs_alt h_sub_subs_alt; unfold c_subs in c_sub_subs_alt.
all: try rewrite v_shift_comm, c_sub_subs_alt; try omega.
all: do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
all: rewrite (v_shift_comm _ i); f_equal; try omega.
all: rewrite v_shift_sub; f_equal; omega.
}{
intros cmp. induction h; unfold h_subs; simpl; f_equal; auto.
unfold c_subs in c_sub_subs_alt. rewrite v_shift_comm, c_sub_subs_alt; try omega.
do 2 f_equal; try rewrite <-v_shift_sub; try omega.
all: try rewrite <-v_shift_comm; try omega; f_equal.
rewrite (v_shift_comm _ i); f_equal; try omega.
rewrite v_shift_comm. f_equal. rewrite v_shift_sub. f_equal.
all: omega.
}
Qed.


Lemma v_subs_subs v i j vi vj:
  j >= i ->
    v_subs (v_subs v i vi) j vj
  = (v_subs (v_subs v (1+j) (v_shift vj 1 i)) i (v_subs vi j vj))

with c_subs_subs c i j vi vj: 
  j >= i ->
    c_subs (c_subs c i vi) j vj
  = (c_subs (c_subs c (1+j) (v_shift vj 1 i)) i (v_subs vi j vj))

with h_subs_subs h i j vi vj: 
  j >= i ->
    h_subs (h_subs h i vi) j vj
  = (h_subs (h_subs h (1+j) (v_shift vj 1 i)) i (v_subs vi j vj)).
Proof.
{
intro cmp.
assert (v_subs v i vi=v_negshift(v_sub v (i, v_shift vi 1 i)) 1 i). reflexivity. unfold v_subs. rewrite <-H.
rewrite v_sub_subs, v_negshift_subs, v_shift_comm.
all: try reflexivity || omega.
all: apply v_sub_makes_no_var. rewrite v_shift_comm. 2: omega. 
all: apply v_shift_makes_no_var. 
}{
intro cmp.
assert (c_subs c i vi=c_negshift(c_sub c (i, v_shift vi 1 i)) 1 i). reflexivity. unfold c_subs. rewrite <-H.
rewrite c_sub_subs, c_negshift_subs, v_shift_comm.
all: try reflexivity || omega.
apply c_sub_makes_no_var. rewrite v_shift_comm. 2: omega. 
2: apply v_sub_makes_no_var. all: apply v_shift_makes_no_var. 
}{
intro cmp.
assert (h_subs h i vi=h_negshift(h_sub h (i, v_shift vi 1 i)) 1 i). reflexivity. unfold h_subs. rewrite <-H.
rewrite h_sub_subs, h_negshift_subs, v_shift_comm.
all: try reflexivity || omega.
apply h_sub_makes_no_var. rewrite v_shift_comm. 2: omega. 
2: apply v_sub_makes_no_var. all: apply v_shift_makes_no_var. 
}
Qed.


Lemma v_subs_subs_alt v i j vi vj:
  j < (1+i) ->
    v_subs (v_subs v (1+i) vi) j vj
  = (v_subs (v_subs v j (v_shift vj 1 i)) i (v_subs vi j vj))

with c_subs_subs_alt c i j vi vj: 
  j < (1+i) ->
    c_subs (c_subs c (1+i) vi) j vj
  = (c_subs (c_subs c j (v_shift vj 1 i)) i (v_subs vi j vj))

with h_subs_subs_alt h i j vi vj: 
  j < (1+i)->
    h_subs (h_subs h (1+i) vi) j vj
  = (h_subs (h_subs h j (v_shift vj 1 i)) i (v_subs vi j vj)).
Proof.
{
intro cmp.
assert (v_subs v (1+i) vi
  =v_negshift(v_sub v (1+i, v_shift vi 1 (1+i))) 1 (1+i)). 
reflexivity. unfold v_subs. rewrite <-H.
rewrite v_sub_subs_alt, v_negshift_subs_alt, <-v_shift_comm.
all: try reflexivity || omega.
all: apply v_sub_makes_no_var. rewrite <-v_shift_comm. 2: omega. 
all: apply v_shift_makes_no_var. 
}{
intro cmp.
assert (c_subs c (1+i) vi
  =c_negshift(c_sub c ((1+i), v_shift vi 1 (1+i))) 1 (1+i)). 
reflexivity. unfold c_subs. rewrite <-H.
rewrite c_sub_subs_alt, c_negshift_subs_alt, <-v_shift_comm.
all: try reflexivity || omega.
apply c_sub_makes_no_var. rewrite <-v_shift_comm. 2: omega. 
2: apply v_sub_makes_no_var. all: apply v_shift_makes_no_var. 
}{
intro cmp.
assert (h_subs h (1+i) vi
  =h_negshift(h_sub h ((1+i), v_shift vi 1 (1+i))) 1 (1+i)). 
reflexivity. unfold h_subs. rewrite <-H.
rewrite h_sub_subs_alt, h_negshift_subs_alt, <-v_shift_comm.
all: try reflexivity || omega.
apply h_sub_makes_no_var. rewrite <-v_shift_comm. 2: omega. 
2: apply v_sub_makes_no_var. all: apply v_shift_makes_no_var. 
}
Qed.

(* ==================== Instantiation ==================== *)

Lemma inst_len_shift I i j :
  inst_len (inst_shift I i j) = inst_len I.
Proof.
revert i j. induction I; intros; simpl; f_equal; auto.
Qed.

Lemma get_inst_val_shift I n d c :
  get_inst_val (inst_shift I d c) n 
  = f_opt (get_inst_val I n) (fun v => Some (v_shift v d c)).
Proof.
revert n d c. induction I; intros; simpl in *. auto. 
destruct n; simpl; auto.
Qed.


Lemma get_inst_val_negshift I n d c :
  get_inst_val (inst_negshift I d c) n 
  = f_opt (get_inst_val I n) (fun v => Some (v_negshift v d c)).
Proof.
revert n d c. induction I; intros; simpl in *. auto. 
destruct n; simpl; auto.
Qed.


Lemma get_inst_val_sub I n i v:
  get_inst_val (inst_sub I (i, v)) n 
  = f_opt (get_inst_val I n) (fun v' => Some (v_sub v' (i, v))).
Proof.
revert n. induction I; intros; simpl in *. auto. 
destruct n; simpl; auto.
Qed.


Fixpoint v_shift_inst I v d cut:
  v_shift (v_inst v I) d cut = v_inst v (inst_shift I d cut)
with c_shift_inst I c d cut:
  c_shift (c_inst c I) d cut = c_inst c (inst_shift I d cut)
with h_shift_inst I h d cut:
  h_shift (h_inst h I) d cut = h_inst h (inst_shift I d cut).
Proof.
{
destruct v; simpl; eauto.
{ rewrite get_inst_val_shift. destruct (get_inst_val I v); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; omega || eauto.
all: apply c_shift_inst; auto.
}{
destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; omega || eauto.
all: apply c_shift_inst; auto.
}{
destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; omega || eauto.
all: apply c_shift_inst; auto.
}
Qed.


Fixpoint v_negshift_inst I v cut:
  inst_no_var I cut ->
  v_negshift (v_inst v I) 1 cut = v_inst v (inst_negshift I 1 cut)
with c_negshift_inst I c cut:
  inst_no_var I cut ->
  c_negshift (c_inst c I) 1 cut = c_inst c (inst_negshift I 1 cut)
with h_negshift_inst I h cut:
  inst_no_var I cut ->
  h_negshift (h_inst h I) 1 cut = h_inst h (inst_negshift I 1 cut).
Proof.
{
intros. destruct v; simpl; eauto.
{ rewrite get_inst_val_negshift. destruct (get_inst_val I v); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; omega || eauto.
all: apply c_negshift_inst; simpl; constructor.
all: omega || apply inst_no_var_shift; omega || eauto.
}{
assert (S(S cut) = 2+cut) as same by omega.
intros. destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; omega || eauto.
all: apply c_negshift_inst; try omega.
all: simpl; constructor; try constructor; try rewrite same.
all: try apply inst_no_var_shift; omega || eauto.
}{
assert (S(S cut) = 2+cut) as same by omega.
intros. destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; omega || eauto.
all: apply c_negshift_inst; try omega.
all: simpl; constructor; try constructor; try rewrite same.
all: try apply inst_no_var_shift; omega || eauto.
}
Qed.

 
Fixpoint v_sub_inst I v i vs:
  v_sub (v_inst v I) (i, vs) = v_inst v (inst_sub I (i, vs))
with c_sub_inst I c i vs:
  c_sub (c_inst c I) (i, vs) = c_inst c (inst_sub I (i, vs))
with h_sub_inst I h i vs:
  h_sub (h_inst h I) (i, vs) = h_inst h (inst_sub I (i, vs)).
Proof.
{
destruct v; simpl; eauto.
{ rewrite get_inst_val_sub. destruct (get_inst_val I v); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; omega || eauto.
all: apply c_sub_inst.
}{
destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; omega || eauto.
all: apply c_sub_inst.
}{
destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; omega || eauto.
all: apply c_sub_inst.
}
Qed.


Lemma inst_subs_unfold I i v_s:
  inst_negshift (inst_sub I (i, v_shift v_s 1 i)) 1 i = inst_subs I i v_s.
Proof.
revert i. induction I; intros; simpl. auto.
rewrite IHI. f_equal.
Qed.


Fixpoint v_subs_inst I v vs i:
  v_subs (v_inst v I) i vs = v_inst v (inst_subs I i vs)
with c_subs_inst I c vs i:
  c_subs (c_inst c I) i vs = c_inst c (inst_subs I i vs)
with h_subs_inst I h vs i:
  h_subs (h_inst h I) i vs = h_inst h (inst_subs I i vs).
Proof.
{
unfold v_subs. 
rewrite v_sub_inst, v_negshift_inst, inst_subs_unfold. all: auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}{
unfold c_subs. 
rewrite c_sub_inst, c_negshift_inst, inst_subs_unfold. all: auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}{
unfold h_subs. 
rewrite h_sub_inst, h_negshift_inst, inst_subs_unfold. all: auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}
Qed.


Fixpoint inst_shift_insert I n v i {struct I}:
  inst_shift (inst_insert I n v) i 0 
  = inst_insert (inst_shift I i 0) n (v_shift v i 0).
Proof.
destruct I; simpl.
+ destruct (n=?0) eqn:n0; simpl; auto.
+ destruct (n=?0); simpl; auto. f_equal. auto.
Qed.


Lemma instU_inst_insert I i vs v:
  InstU (inst_insert I i vs) v = inst_insert (InstU I v) (S i) vs.
Proof.
  simpl. do 2 f_equal. omega.
Qed.


Fixpoint v_inst_no_var_same I vs i v:
  v_no_var v i -> v_under_var v (1+inst_len I) -> i <= inst_len I ->
  v_inst v (inst_insert I i vs) = v_inst (v_negshift v 1 i) I
with c_inst_no_var_same I vs i c:
  c_no_var c i -> c_under_var c (1+inst_len I) -> i <= inst_len I ->
  c_inst c (inst_insert I i vs) = c_inst (c_negshift c 1 i) I
with h_inst_no_var_same I vs i h:
  h_no_var h i -> h_under_var h (1+inst_len I) -> i <= inst_len I ->
  h_inst h (inst_insert I i vs) = h_inst (h_negshift h 1 i) I.
Proof.
{
intros safe under ilen. destruct v; simpl; auto.
{ rename v into dbi. destruct (i<=?dbi) eqn:cmp.
  + apply leb_complete in cmp. simpl in *.
    destruct dbi. omega. 
    rewrite inst_insert_above. simpl.
    assert (dbi-0=dbi) by omega. rewrite H. all: omega || auto.
  + apply leb_complete_conv in cmp. simpl in *.
    rewrite inst_insert_under. simpl. all: omega || auto. }
all: f_equal; simpl in *; try destruct safe; try destruct under; eauto.
all: rewrite inst_shift_insert, instU_inst_insert.
all: apply c_inst_no_var_same; simpl; omega || auto.
all: rewrite inst_len_shift; omega || auto.
}{
intros safe under ilen. destruct c; simpl.
all: f_equal; simpl in *; try destruct safe; try destruct under; eauto.
all: try rewrite inst_shift_insert, instU_inst_insert.
all: try rewrite instU_inst_insert; try apply c_inst_no_var_same; simpl; auto.
all: try rewrite inst_len_shift; omega || auto.
all: try destruct H0; auto; destruct H2; auto.
}{
intros safe under ilen. destruct h; simpl. auto.
f_equal; simpl in *; destruct safe; destruct under. auto.
rewrite inst_shift_insert, instU_inst_insert, instU_inst_insert.
apply c_inst_no_var_same; auto; simpl; rewrite inst_len_shift. auto. omega.
}
Qed.
