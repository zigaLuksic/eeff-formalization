Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
Require Export substitution syntax_lemmas.
Require Import Le Arith.

(* ==================== Effects on getters ==================== *)

Lemma shift_get_case_None h op i cut :
  get_case h op = None <-> get_case (h_shift h i cut) op = None.
Proof.
constructor; intros; induction h; simpl in *; auto.
all: destruct (op==o) eqn:cmp; try discriminate; auto.
Qed.


Lemma negshift_get_case_None h op i cut :
  get_case h op = None <-> get_case (h_negshift h i cut) op = None.
Proof.
constructor; intro; induction h; simpl in *; auto.
all: destruct (op==o) eqn:cmp; try discriminate; auto.
Qed.


Lemma sub_get_case_None h op i vs :
  get_case h op = None <->  get_case (h_sub h (i, vs)) op = None.
Proof.
constructor; intro; induction h; simpl in *; auto.
all: destruct (op==o) eqn:cmp; try discriminate; auto.
Qed.


Lemma inst_get_case_None I h op:
  get_case h op = None -> get_case (h_inst h I) op = None.
Proof.
revert I op. induction h; intros I op orig.
+ simpl. auto.
+ simpl in *. destruct (op==o). discriminate. auto.
Qed.


Lemma shift_get_case_Some h op i cut c :
  get_case h op = Some c -> 
  get_case (h_shift h i cut) op = Some (c_shift c i (2+cut)).
Proof.
intros gets; induction h; simpl in *. discriminate.
destruct (op==o) eqn:cmp. inv gets. all: auto.
Qed.


Lemma negshift_get_case_Some h op i cut c :
  get_case h op = Some c -> 
  get_case (h_negshift h i cut) op = Some (c_negshift c i (2+cut)).
Proof.
intros gets; induction h; simpl in *. discriminate.
destruct (op==o) eqn:cmp. inv gets. all: auto.
Qed.


Lemma sub_get_case_Some h op i vs c :
  get_case h op = Some c -> 
  get_case (h_sub h (i, vs)) op = Some (c_sub c (2+i, v_shift vs 2 0)).
Proof.
intros gets; induction h; simpl in *. discriminate.
destruct (op==o) eqn:cmp. inv gets. all: auto.
Qed.


Fixpoint inst_get_case_Some I I' h op c_op {struct h}:
  get_case h op = Some c_op -> 
  I' = InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0) ->
  get_case (h_inst h I) op = Some (c_inst c_op I').
Proof.
intros finds same. destruct h; subst; simpl in *.
+ discriminate.
+ destruct (op==o). inv finds. auto. apply inst_get_case_Some; auto.
Qed.


(* ==================== Shift Arithmetic ==================== *)

Fixpoint v_shift_0 cut v : v_shift v 0 cut = v
with     c_shift_0 cut c : c_shift c 0 cut = c
with     h_shift_0 cut h : h_shift h 0 cut = h.
Proof.
{ revert cut. induction v; intros cut; simpl; try f_equal; auto.
  destruct (cut <=? n); auto. }
{ revert cut. induction c; intros cut; simpl; f_equal; auto. }
{ revert cut. induction h; intros cut; simpl; f_equal; auto. }
Qed.

Lemma inst_shift_0 cut I : inst_shift I 0 cut = I.
Proof.
induction I; simpl; f_equal; auto. apply v_shift_0.
Qed.


Fixpoint v_shift_shift n m cut v {struct v}:
  v_shift (v_shift v n cut) m cut = (v_shift v (n+m) cut)
with c_shift_shift n m cut c {struct c}:
  c_shift (c_shift c n cut) m cut = (c_shift c (n+m) cut)
with h_shift_shift n m cut h {struct h}:
  h_shift (h_shift h n cut) m cut = (h_shift h (n+m) cut).
Proof.
{ induction v; simpl; f_equal; auto.
  destruct (cut<=?n0) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (cut<=?n+n0=true) by (apply leb_correct; omega).
    rewrite H. f_equal. omega.
  - rewrite cmp. reflexivity. }
{ revert cut. induction c; intros cut; try destruct p; simpl; f_equal; auto. }
{ revert cut. induction h; intros cut; simpl; f_equal; auto. }
Qed.

Lemma inst_shift_shift n m cut I :
  inst_shift (inst_shift I n cut) m cut = inst_shift I (n+m) cut.
Proof.
induction I; simpl; f_equal; auto. apply v_shift_shift.
Qed.


Fixpoint v_negshift_shift n m cut v {struct v}:
  (m <= n) ->
  v_negshift (v_shift v n cut) m cut = (v_shift v (n - m) cut)

with c_negshift_shift n m cut c {struct c}:
  (m <= n) ->
  c_negshift (c_shift c n cut) m cut = (c_shift c (n - m) cut)

with h_negshift_shift n m cut h {struct h}:
  (m <= n) ->  
  h_negshift (h_shift h n cut) m cut = (h_shift h (n - m) cut).

Proof.
all: intros cmp.
{ induction v; simpl; f_equal; auto.
  destruct (cut<=?n0) eqn:cv; simpl.
  - apply leb_complete in cv.
    assert (cut<=?n+n0=true) by (apply leb_correct; omega).
    rewrite H. f_equal. omega.
  - rewrite cv. reflexivity. }
{ induction c; simpl; f_equal; auto. }
{ induction h; simpl; f_equal; auto. }
Qed.

(* ==================== Commutativity (Distributivity) ==================== *)

Fixpoint v_shift_comm n i j d v {struct v}:
  i >= j ->
  v_shift (v_shift v n i) d j = v_shift (v_shift v d j) n (d+i)

with c_shift_comm n i j d c {struct c}:
  i >= j ->
  c_shift (c_shift c n i) d j = c_shift (c_shift c d j) n (d+i)

with h_shift_comm n i j d h {struct h}:
  i >= j ->
  h_shift (h_shift h n i) d j = h_shift (h_shift h d j) n (d+i).

Proof.
{
intros cmp. induction v; simpl.
{ clear v_shift_comm c_shift_comm h_shift_comm.
  destruct (i<=?n0) eqn:cmpi; destruct (j<=?n0) eqn:cmpj; simpl.
  + apply leb_complete in cmpi. apply leb_complete in cmpj.
    assert (j<=?n+n0=true) by (apply leb_correct; omega).
    assert (d+i<=?d+n0=true) by (apply leb_correct; omega).
    rewrite H, H0. f_equal. omega.
  + apply leb_complete in cmpi. apply leb_complete_conv in cmpj. omega.
  + apply leb_complete_conv in cmpi. rewrite cmpj. apply leb_complete in cmpj.
    assert (d+i<=?d+n0=false) by (apply leb_correct_conv; omega).  
    rewrite H. auto.
  + rewrite cmpj. 
    apply leb_complete_conv in cmpi. apply leb_complete_conv in cmpj.
    assert (d+i<=?n0=false) by (apply leb_correct_conv; omega).
    rewrite H. auto. }
all: f_equal; auto.
all: assert (S(d+i)=d+S i) as same by omega; rewrite same. 
all: eapply c_shift_comm; omega.
}{
intros cmp. induction c; simpl; f_equal; eauto. 
all: assert (S(S(d+i))=d+S(S i)) as ssame by omega.
all: assert (S(d+i)=d+S i) as same by omega.
all: try rewrite ssame; try rewrite same; eapply c_shift_comm; omega.
}{
intros cmp. induction h; simpl; f_equal; auto.
assert (S(S(d+i))=d+S(S i)) as ssame by omega. rewrite ssame.
eapply c_shift_comm; omega.
}
Qed.

Lemma inst_shift_comm n i j d I:
  i>=j ->
  inst_shift (inst_shift I n i) d j = inst_shift (inst_shift I d j) n (d+i).
Proof.
intros. induction I; simpl; f_equal; auto. apply v_shift_comm. omega.
Qed.


Fixpoint v_shift_negshift_comm v n i j {struct v}:
  v_no_var v j -> i <= j ->
  v_shift (v_negshift v 1 j) n i = v_negshift (v_shift v n i) 1 (n+j)

with c_shift_negshift_comm c n i j {struct c}:
  c_no_var c j -> i <= j ->
  c_shift (c_negshift c 1 j) n i = c_negshift (c_shift c n i) 1 (n+j)

with h_shift_negshift_comm h n i j {struct h}:
  h_no_var h j -> i <= j ->
  h_shift (h_negshift h 1 j) n i = h_negshift (h_shift h n i) 1 (n+j).

Proof.
all: intros novar cmp.
{
destruct v; simpl in *; auto.
{ destruct (j<=?n0) eqn:jn0.
  + apply leb_complete in jn0. 
    assert (i<=?n0=true) by (apply leb_correct; omega). rewrite H. simpl.
    assert (n+j<=?n+n0=true) by (apply leb_correct; omega). rewrite H0.
    assert (i<=?n0-1=true) by (apply leb_correct; omega). rewrite H1.
    f_equal. aomega.
  + apply leb_complete_conv in jn0. simpl.
    destruct (i<=?n0) eqn:in0; simpl.
    - assert (n+j<=?n+n0=false) by (apply leb_correct_conv; omega).
      rewrite H. auto.
    - assert (n+j<=?n0=false) by (apply leb_correct_conv; omega).
      rewrite H. auto. }
all: f_equal; simpl in novar; try destruct novar; auto.
all: assert (S(n+j)=n+(S j)) as same by omega; rewrite same.
all: apply c_shift_negshift_comm; aomega.
}{
destruct c; simpl in *; f_equal; auto.
all: assert (S(S(n+j))=n+(S (S j))) as ssame by omega; try rewrite ssame.
all: assert (S(n+j)=n+(S j)) as same by omega; try rewrite same.
all: try destruct novar; try destruct H0; auto.
all: apply c_shift_negshift_comm; aomega.
}{
destruct h; simpl in *; f_equal; try destruct novar; auto.
assert (S(S(n+j))=n+(S(S j))) as ssame by omega; try rewrite ssame.
apply c_shift_negshift_comm; aomega.
}
Qed.

Lemma inst_shift_negshift_comm I n i j :
  inst_no_var I j -> i <= j ->
    inst_shift (inst_negshift I 1 j) n i
  = inst_negshift (inst_shift I n i) 1 (n+j).
Proof.
revert n i j. induction I; intros n i j novar cmp; simpl; f_equal. auto.
all: simpl in novar; destruct novar. auto.
apply v_shift_negshift_comm; aomega.
Qed.


Lemma v_shift_negshift_comm_alt v i j:
  v_no_var v j -> j < i ->
  v_shift (v_negshift v 1 j) 1 i = v_negshift (v_shift v 1 (1+i)) 1 j

with c_shift_negshift_comm_alt c i j:
  c_no_var c j -> j < i ->
  c_shift (c_negshift c 1 j) 1 i = c_negshift (c_shift c 1 (1+i)) 1 j

with h_shift_negshift_comm_alt h i j:
  h_no_var h j -> j < i ->
  h_shift (h_negshift h 1 j) 1 i = h_negshift (h_shift h 1 (1+i)) 1 j.

Proof.
all: intros novar cmp.
{
destruct v.
{ assert (1+i=i+1) as hack by omega. rewrite hack. clear hack.
  rename n into d. simpl. destruct (j<=?d) eqn:jd.
  + apply leb_complete in jd. simpl in novar.
    destruct (i+1<=?d) eqn:sid; simpl.
    - assert (j<=? S d=true) by (apply leb_correct; omega).
      rewrite H. destruct d; simpl. omega. apply leb_complete in sid.
      assert (i<=?d-0=true) by (apply leb_correct; omega).
      rewrite H0. f_equal. omega.
    - apply leb_complete_conv in sid. apply leb_correct in jd as jd'.
      rewrite jd'. destruct d. omega.
      assert (i<=?S d-1=false) by (apply leb_correct_conv; omega). 
      rewrite H. auto.
  + simpl. apply leb_complete_conv in jd as jd'. 
    assert (i<=?d=false) by (apply leb_correct_conv; omega). rewrite H.
    assert (i+1<=?d=false) by (apply leb_correct_conv; omega). rewrite H0.
    simpl. rewrite jd. auto. }
all: simpl in *; auto; f_equal; try destruct novar; auto.
all: apply c_shift_negshift_comm_alt; aomega.
}{
destruct c; simpl in *; f_equal; auto.
all: try destruct novar; try destruct H0; auto.
all: apply c_shift_negshift_comm_alt; aomega.
}{
destruct h; simpl in *; f_equal; auto.
all: try destruct novar; auto. apply c_shift_negshift_comm_alt; aomega.
}
Qed.

(* ==================== NoVar Interactions ==================== *)

Lemma v_shift_makes_no_var v j:
  v_no_var (v_shift v 1 j) j
with c_shift_makes_no_var c j:
  c_no_var (c_shift c 1 j) j
with h_shift_makes_no_var h j:
  h_no_var (h_shift h 1 j) j.
Proof.
{ revert j; induction v; intros j; simpl; auto.
  destruct (j<=?n) eqn:cmp; simpl.
  + apply leb_complete in cmp. omega.
  + apply leb_iff_conv in cmp. omega. }
{ revert j; induction c; intros j; try destruct p; simpl; auto. }
{ revert j; induction h; intros j; simpl; auto. }
Qed.


Fixpoint v_no_var_shift v j n cut:
  v_no_var v j -> (cut <= j) -> 
  v_no_var (v_shift v n cut) (n+j)

with c_no_var_shift c j n cut:
  c_no_var c j -> (cut <= j) -> 
  c_no_var (c_shift c n cut) (n+j)

with h_no_var_shift h j n cut:
  h_no_var h j -> (cut <= j) -> 
  h_no_var (h_shift h n cut) (n+j).

Proof.
all: assert (forall j, S(n+j)=n+(S j)) as snj by (intro; omega).
all: assert (forall j, S(S(n+j))=n+(S(S j))) as ssnj by (intro; omega).
all: intros orig cmp.
{
destruct v; simpl in *.
{ destruct (cut <=? n0) eqn:cn; simpl; try rewrite leb_iff_conv in cn; omega. }
all: try constructor; try destruct orig; auto.
all: rewrite snj; apply c_no_var_shift; aomega.
}{
destruct c; simpl in *; auto.
all: try destruct orig; try destruct H0; try constructor; try constructor; auto.
all: try rewrite ssnj; try rewrite snj; apply c_no_var_shift; aomega.
}{
destruct h; simpl in *; auto.
destruct orig. constructor; auto. rewrite ssnj. apply c_no_var_shift; aomega.
}
Qed.


Fixpoint inst_no_var_shift I j n cut {struct I}:
  inst_no_var I j -> (cut <= j) -> 
  inst_no_var (inst_shift I n cut) (n+j).
Proof.
intros orig cmp. destruct I; simpl in *; auto.
destruct orig. constructor; eauto. apply v_no_var_shift; aomega.
Qed.


Fixpoint v_no_var_shift_alt v j n cut:
  v_no_var v j -> (cut > j) ->
  v_no_var (v_shift v n cut) j

with c_no_var_shift_alt c j n cut:
  c_no_var c j -> (cut > j) ->
  c_no_var (c_shift c n cut) j

with h_no_var_shift_alt h j n cut:
  h_no_var h j -> (cut > j) ->
  h_no_var (h_shift h n cut) j.

Proof.
all: intros orig cmp.
{
destruct v; simpl in *.
{ destruct (cut <=? n0) eqn:cn; simpl; try apply leb_complete in cn; omega. }
all: try constructor; try destruct orig; auto.
all: apply c_no_var_shift_alt; aomega.
}{
destruct c; simpl in *; auto.
all: try destruct orig; try destruct H0; try constructor; try constructor; auto.
all: apply c_no_var_shift_alt; aomega.
}{
destruct h; simpl in *; auto.
destruct orig. constructor; auto. apply c_no_var_shift_alt; aomega.
}
Qed.


Fixpoint v_sub_makes_no_var v j vs :
  v_no_var vs j -> v_no_var (v_sub v (j, vs)) j
with c_sub_makes_no_var c j vs :
  v_no_var vs j -> c_no_var (c_sub c (j, vs)) j
with h_sub_makes_no_var h j vs :
  v_no_var vs j -> h_no_var (h_sub h (j, vs)) j.
Proof.
all: intros novar.
{
destruct v; simpl in *; auto.
{ destruct (n=?j) eqn:nj; auto. simpl. apply Nat.eqb_neq in nj. omega. }
all: try aconstructor; apply c_sub_makes_no_var; apply v_no_var_shift; aomega.
}{
destruct c; simpl in *; auto.
all: try constructor; try constructor; auto.
all: assert (S(S j)=2+j) as ssj by omega; try rewrite ssj.
all: apply c_sub_makes_no_var; apply v_no_var_shift; aomega.
}{
destruct h; simpl in *; try constructor; auto.
assert (S(S j)=2+j) as ssj by omega. rewrite ssj.
apply c_sub_makes_no_var; apply v_no_var_shift; aomega.
}
Qed.

Lemma inst_sub_makes_no_var I j v_s :
  v_no_var v_s j -> inst_no_var (inst_sub I (j, v_s)) j.
Proof.
revert j. induction I; intros; simpl. auto. aconstructor.
apply v_sub_makes_no_var. auto.
Qed.


Fixpoint v_under_var_shift v j n cut:
  v_under_var v j -> cut <= j -> 
  v_under_var (v_shift v n cut) (n+j)

with c_under_var_shift c j n cut:
  c_under_var c j -> cut <= j -> 
  c_under_var (c_shift c n cut) (n+j)

with h_under_var_shift h j n cut:
  h_under_var h j -> cut <= j -> 
  h_under_var (h_shift h n cut) (n+j).

Proof.
all: assert (S(n+j)=n+S j) as snj by omega.
all: assert (S(S(n+j))=n+S(S j)) as ssnj by omega.
all: intros under cmp. 
{
destruct v; simpl in *; auto.
{ destruct (cut <=? n0) eqn:ccmp; simpl; omega. }
all: try constructor; try destruct under; auto.
all: rewrite snj; eapply c_under_var_shift; aomega.
}{
destruct c; simpl in *; auto.
all: try destruct under; try destruct H0; try constructor; try constructor.
all: try rewrite ssnj; try rewrite snj; auto.
all: eapply c_under_var_shift; aomega.
}{
destruct h; simpl in *. auto. destruct under. constructor. auto.
rewrite ssnj. eapply c_under_var_shift; aomega.
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
intros under. destruct v; simpl in *.
{ assert (cut<=?n0=false) by (apply leb_correct_conv; omega). rewrite H. auto. }
all: try destruct under; f_equal; auto.
}{
intros under. destruct c; simpl in *.
all: try destruct under; try destruct H0; f_equal; auto.
}{
intros under. destruct h; simpl in *.
all: try destruct under; f_equal; auto.
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
intros under. destruct v; simpl in *.
{ assert (cut<=?n0=false) by (apply leb_correct_conv; omega). rewrite H. auto. }
all: try destruct under; f_equal; auto.
}{
intros under. destruct c; simpl in *.
all: try destruct under; try destruct H0; f_equal; auto.
}{
intros under. destruct h; simpl in *.
all: try destruct under; f_equal; auto.
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
intros under. destruct v; simpl in *.
{ assert (n=?i=false) by (apply Nat.eqb_neq; omega). rewrite H. auto. }
all: try destruct under; f_equal; auto.
}{
intros under. destruct c; simpl in *.
all: try destruct under; try destruct H0; f_equal; auto.
}{
intros under. destruct h; simpl in *.
all: try destruct under; f_equal; auto.
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
intros under. unfold v_subs. rewrite v_sub_too_high, v_negshift_too_high; auto.
}{
intros under. unfold c_subs. rewrite c_sub_too_high, c_negshift_too_high; auto.
}{
intros under. unfold h_subs. rewrite h_sub_too_high, h_negshift_too_high; auto.
}
Qed.


Fixpoint v_sub_no_var_same v v' i {struct v}:
  v_no_var v i -> v_sub v (i, v') = v
with c_sub_no_var_same c v' i {struct c}:
  c_no_var c i -> c_sub c (i, v') = c
with h_sub_no_var_same h v' i {struct h}:
  h_no_var h i -> h_sub h (i, v') = h.
Proof.
all: intros novar.
+ destruct v; simpl in *. 
  { assert (n=?i=false) by (apply Nat.eqb_neq; omega). rewrite H. auto. }
  all: try destruct novar; f_equal; auto.
+ induction c; simpl in *. 
  all: try destruct novar; try destruct H0; f_equal; auto.
+ induction h; simpl in *; try destruct novar; f_equal; auto.
Qed.

(* ==================== Sub Interactions ==================== *)

Fixpoint v_shift_sub v v' i cut j {struct v}:
  cut <= j ->
    v_shift (v_sub v (j, v')) i cut 
  = v_sub (v_shift v i cut) (i+j, v_shift v' i cut)

with c_shift_sub c v' i cut j {struct c}:
  cut <= j ->
    c_shift (c_sub c (j, v')) i cut 
  = c_sub (c_shift c i cut) (i+j, v_shift v' i cut)

with h_shift_sub h v' i cut j {struct h}:
  cut <= j ->
    h_shift (h_sub h (j, v')) i cut
  = h_sub (h_shift h i cut) (i+j, v_shift v' i cut).

Proof.
all: assert (S(i+j)=i+(S j)) as Sij by omega.
all: assert (S(S(i+j))=i+(S(S j))) as SSij by omega.
all: intros cmp.
{ destruct v; simpl in *.
  { simpl. destruct (cut<=?n) eqn:cn.
    + destruct (n=?j) eqn:nj.
      * apply Nat.eqb_eq in nj. subst. simpl.
        assert (i+j=?i+j=true) by (apply Nat.eqb_eq; omega).
        rewrite H. auto.
      * simpl. rewrite cn. assert (i+n=?i+j=false).
        { apply Nat.eqb_neq. apply Nat.eqb_neq in nj. omega. }
        rewrite H. auto.
    + assert (n=?j=false).
      { apply Nat.eqb_neq. apply leb_complete_conv in cn. omega. }
      rewrite H. simpl. rewrite cn.
      assert (n=?i+j=false).
      { apply Nat.eqb_neq. apply leb_complete_conv in cn. omega. }
      rewrite H0. auto. }
all: f_equal; auto.
all: rewrite Sij, v_shift_comm, c_shift_sub; aomega.
}{
destruct c; simpl in *; f_equal; auto.
all : try rewrite SSij; try rewrite Sij.
all: rewrite v_shift_comm, c_shift_sub; aomega.
}{
destruct h; simpl in *; f_equal; auto.
rewrite SSij, v_shift_comm, c_shift_sub; aomega.
}
Qed.

Fixpoint inst_shift_sub I v' i cut j {struct I}:
  cut <= j ->
    inst_shift (inst_sub I (j, v')) i cut 
  = inst_sub (inst_shift I i cut) (i+j, v_shift v' i cut).
Proof.
destruct I; intros; simpl; f_equal; auto.
apply v_shift_sub. omega.
Qed.


Fixpoint v_negshift_sub v v' cut j :
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
all: intros cmp novar novar'.
{
destruct v; simpl in *.
{ destruct (cut<=?n) eqn:cn.
  + destruct (n=?j) eqn:nsj.
    - simpl. apply Nat.eqb_eq in nsj. subst.
      assert (j-1=?j-1=true) by (apply Nat.eqb_eq; omega).
      rewrite H. auto.
    - simpl. rewrite cn. assert (n-1=?j-1=false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in nsj. omega. }
      rewrite H. auto.
  + assert (n=?j=false).
    { apply Nat.eqb_neq. apply leb_complete_conv in cn. omega. }
    rewrite H. simpl. rewrite cn.
    assert (n=?j-1=false).
    { apply Nat.eqb_neq. apply leb_complete_conv in cn. omega. }
    rewrite H0. auto. }
all: try destruct novar; f_equal; auto.
all: rewrite c_negshift_sub; try do 2 f_equal; aomega.
all: try rewrite v_shift_negshift_comm; aomega.
all: apply v_no_var_shift; aomega.
}{
destruct c; simpl in *.
all: try destruct novar; try destruct H0; f_equal; auto.
all: assert (S(S cut)=2+cut) as ssc by omega; try rewrite ssc.
all: assert (S cut=1+cut) as sc by omega; try rewrite sc.
all: rewrite c_negshift_sub; try do 2 f_equal; aomega.
all: try rewrite v_shift_negshift_comm; aomega.
all: try apply v_no_var_shift; aomega.
}{
destruct h; simpl in *. auto.
destruct novar. f_equal. auto.
rewrite c_negshift_sub; try do 2 f_equal; aomega.
rewrite v_shift_negshift_comm. f_equal. all: aomega.
assert (S(S cut)=2+cut) as cc by omega; rewrite cc.
apply v_no_var_shift; aomega.
}
Qed.


Fixpoint v_sub_sub v v1 v2 i j :
  v_no_var v j ->
  v_sub v (i, v_sub v1 (j, v2)) = v_sub (v_sub v (i, v1)) (j, v2)

with c_sub_sub c v1 v2 i j :
  c_no_var c j ->
  c_sub c (i, v_sub v1 (j, v2)) = c_sub (c_sub c (i, v1)) (j, v2)

with h_sub_sub h v1 v2 i j :
  h_no_var h j ->
  h_sub h (i, v_sub v1 (j, v2)) = h_sub (h_sub h (i, v1)) (j, v2).

Proof.
all: intros novar.
{
destruct v; simpl in *; auto.
{ destruct (n=?i) eqn:cn. auto. simpl. assert (n=?j=false) by
  (apply Nat.eqb_neq; omega). rewrite H. auto. }
all: try destruct novar; f_equal; auto.
all: rewrite v_shift_sub, c_sub_sub; aomega.
}{
destruct c; simpl in *.
all: f_equal; try destruct novar; try destruct H0; auto.
all: rewrite v_shift_sub, c_sub_sub; aomega.
}{
destruct h; simpl in *. auto.
f_equal; try destruct novar; auto. rewrite v_shift_sub, c_sub_sub; aomega.
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
all: intros under under' cmp.
+ destruct v; simpl in *.
  { unfold v_subs. simpl. destruct (n=?j) eqn:nj.
  + rewrite v_negshift_shift, v_shift_0; aomega.
  + simpl. destruct (j<=?n) eqn:cmpj; simpl; apply Nat.eqb_neq in nj.
    apply leb_complete in cmpj. omega.
    apply leb_complete_conv in cmpj. omega. }
  all: try destruct under; try constructor; eauto.
  all: rewrite v_shift_comm; eaomega; apply c_under_var_subs; aomega.
  all: apply v_under_var_shift; aomega.
+ destruct c; simpl in *; eauto.
  all: try destruct under; try destruct H0; try constructor; try constructor.
  all: eauto; rewrite v_shift_comm; try apply c_under_var_subs; aomega.
  all: assert (S(S i) = 2+i) as same by omega; try rewrite same.
  all: apply v_under_var_shift; aomega.
+ destruct h; simpl in *; eauto.
  destruct under. constructor. eauto.
  rewrite v_shift_comm; try apply c_under_var_subs; aomega.
  assert (S(S i) = 2+i) as same by omega; try rewrite same.
  apply v_under_var_shift; aomega.
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
all: intros no_var no_var' cmp.
+ destruct v; simpl in *.
  { unfold v_subs. simpl. destruct (n=?j) eqn:nj.
  + rewrite v_negshift_shift, v_shift_0; aomega.
  + simpl. destruct (j<=?n) eqn:cmpj; simpl; apply Nat.eqb_neq in nj.
    apply leb_complete in cmpj. omega.
    apply leb_complete_conv in cmpj. omega. }
  all: try destruct no_var; try constructor; eauto.
  all: rewrite v_shift_comm; eaomega; apply c_no_var_subs; aomega.
  all: apply v_no_var_shift; aomega.
+ destruct c; simpl in *; eauto.
  all: try destruct no_var; try destruct H0; try constructor; try constructor.
  all: eauto; rewrite v_shift_comm; try apply c_no_var_subs; aomega.
  all: assert (S(S i) = 2+i) as same by omega; try rewrite same.
  all: apply v_no_var_shift; aomega.
+ destruct h; simpl in *; eauto.
  destruct no_var. constructor. eauto.
  rewrite v_shift_comm; try apply c_no_var_subs; aomega.
  assert (S(S i) = 2+i) as same by omega; try rewrite same.
  apply v_no_var_shift; aomega.
Qed.


(* ==================== Full Subs Distributivity ==================== *)

Fixpoint v_shift_subs v v' i j (safe: j <= i): 
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
destruct v; unfold v_subs; simpl.
{ destruct (n=?i) eqn:ni.
  apply Nat.eqb_eq in ni. subst.
  + destruct (i=?j) eqn:eqij.
    - apply Nat.eqb_eq in eqij. subst.
      assert (1+j<=?j=false) by (apply leb_correct_conv; omega).
      simpl in H. rewrite H. simpl.
      assert (j=?j=true) by (apply Nat.eqb_eq; auto).
      rewrite H0. simpl. 
      rewrite v_negshift_shift, v_negshift_shift.
      rewrite v_shift_shift, v_shift_shift. f_equal. omega. omega.
    - assert (1+i<=?i=false) by (apply leb_correct_conv; omega).
      simpl in H. rewrite H. simpl. apply leb_correct in safe as s.
      rewrite s, eqij. simpl. rewrite s. assert (i<=?i-1=false).
      { apply leb_correct_conv. apply Nat.eqb_neq in eqij. omega. } 
      rewrite H0. auto.
  + destruct (n=?j) eqn:nj.
    * apply Nat.eqb_eq in nj. subst.
      assert (1+i<=?j=false) by (apply leb_correct_conv; omega).
      simpl in H. rewrite H. simpl.
      assert (j=?j=true) by (apply Nat.eqb_eq; omega).
      rewrite H0, v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
      all: aomega.
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
        destruct (j<=?n) eqn:jln; simpl.
        ++assert (i<=?n-1=false) by (apply leb_correct_conv; omega).
          rewrite H0. auto.
        ++assert (i<=?n=false) by (apply leb_correct_conv; omega).
          rewrite H0. auto. }
all: f_equal; eauto; unfold c_subs in *.
all: rewrite v_shift_comm, (v_shift_comm 1 j), (v_shift_comm 1 i); aomega.
all: rewrite c_shift_subs; aomega.
}{
destruct c; unfold c_subs in *; simpl; f_equal; eauto.
all: rewrite v_shift_comm, c_shift_subs; aomega.
all: do 3 f_equal; rewrite (v_shift_comm 1 j); aomega.
all: f_equal; rewrite (v_shift_comm 1 i); aomega.
}{
destruct h; unfold h_subs; unfold c_subs in *; simpl; f_equal; eauto.
rewrite v_shift_comm, c_shift_subs; aomega.
rewrite (v_shift_comm 1 j), (v_shift_comm 1 i); aomega.
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
{ destruct (n=?i) eqn:ni.
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
        simpl in H2. rewrite H2. reflexivity. }
all: f_equal; eauto; unfold c_subs in *.
all: rewrite v_shift_comm, (v_shift_comm 1 (S j)), (v_shift_comm 1 i); aomega.
all: rewrite c_shift_subs_alt; aomega.
}{
destruct c; unfold c_subs in *; simpl; f_equal; eauto.
all: rewrite v_shift_comm, c_shift_subs_alt; aomega.
all: do 3 f_equal; rewrite (v_shift_comm 1 (S j)); aomega.
all: f_equal; rewrite (v_shift_comm 1 i); aomega.
}{
destruct h; unfold h_subs; unfold c_subs in *; simpl; f_equal; eauto.
rewrite v_shift_comm, c_shift_subs_alt; aomega.
rewrite (v_shift_comm 1 (S j)), (v_shift_comm 1 i); aomega.
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
intros nov nov'. destruct v; unfold v_subs; simpl in *.
{ clear v_negshift_subs c_negshift_subs h_negshift_subs.
  destruct (n=?j) eqn:nj.
  apply Nat.eqb_eq in nj. subst.
  destruct (1+i <=? j) eqn:cmpij.
  3 : destruct (1+i <=? n) eqn:Sin. all: simpl.
  + apply leb_complete in cmpij.
    assert (j=S i) by omega. subst. omega.
  + simpl in cmpij. rewrite cmpij. simpl.
    assert (j=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H, v_negshift_shift, v_shift_0, v_negshift_shift, v_shift_0.
    all: aomega.
  + apply leb_complete in Sin as sin. simpl in Sin.
    rewrite Sin. apply Nat.eqb_neq in nj.
    assert (j<=?n=true) by (apply leb_correct; omega). simpl in H.
    rewrite H. simpl. assert (i<=?n-1=true) by (apply leb_correct; omega).
    rewrite H0. assert (n-1=?j=false).
    { apply Nat.eqb_neq. simpl in nov. omega. }
    rewrite H1. simpl. assert (j<=?n-1=true).
    { apply leb_correct. omega. }
    rewrite H2. auto.
  + apply leb_complete_conv in Sin as sin. simpl in Sin. rewrite Sin. simpl.  
    rewrite nj. apply Nat.eqb_neq in nj. simpl.
    destruct (j<=?n) eqn:jln.
    - simpl. assert (i<=?n-1=false).
      { apply leb_correct_conv. omega. }
      rewrite H. auto.
    - simpl. assert (i<=?n=false).
      { apply leb_correct_conv. apply leb_complete_conv in jln. omega. }
      rewrite H. auto. }
all: f_equal; try destruct nov; eauto.
all: unfold c_subs in *; rewrite v_shift_comm; aomega.
all: rewrite (c_negshift_subs c _ (S i) (S j)); aomega.
all: try (apply v_no_var_shift; aomega).
all: rewrite v_shift_comm; do 4 f_equal; aomega. 
all: rewrite v_shift_negshift_comm; aomega.
}{
intros nov nov'; destruct c; unfold c_subs in *; simpl in *.
all: try destruct nov; try destruct H0; f_equal; eauto.
all: rewrite v_shift_comm; aomega; simpl.
all: assert (S(S i)=2+i) as ssi by (omega).
all: try rewrite (c_negshift_subs _ _ (S i) (S j))
  || rewrite (c_negshift_subs _ _ (S(S i)) (S(S j))); aomega.
all: try rewrite ssi; try (apply v_no_var_shift; aomega).
all: rewrite v_shift_comm; do 4 f_equal; aomega. 
all: rewrite v_shift_negshift_comm; aomega.
}{
intros nov nov'; destruct h; unfold c_subs in *; unfold h_subs in *; simpl in *.
all: try destruct nov; f_equal; eauto.
rewrite v_shift_comm; aomega; simpl.
assert (S(S i)=2+i) as ssi by (omega).
rewrite (c_negshift_subs _ _ (S(S i)) (S(S j))); aomega.
2: rewrite ssi; (apply v_no_var_shift; aomega).
rewrite v_shift_comm; do 4 f_equal; aomega. 
rewrite v_shift_negshift_comm; aomega.
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
  destruct (n=?S j) eqn:nSj.
  apply Nat.eqb_eq in nSj. subst.
  2 : destruct (i <=? n) eqn:cmpin. all: simpl.
  + assert(i<=?S j=true) by (apply leb_correct; omega).
    rewrite H. simpl.
    assert(j-0=?j=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_shift_0, v_negshift_shift, v_shift_0.
    all: aomega.
  + apply leb_complete in cmpin as ccmpin.
    apply Nat.eqb_neq in nSj as nnSj. simpl in nov.
    assert (n-1=?j=false) by (apply Nat.eqb_neq; omega).
    rewrite H. simpl.
    destruct (j <=? n-1) eqn:jnm1.
    - apply leb_complete in jnm1. 
      assert (S j<=?n=true) by (apply leb_correct; omega).
      simpl in H0. rewrite H0. simpl.
      assert (i<=?n-1=true) by (apply leb_correct; omega).
      rewrite H1. auto.
    - apply leb_complete_conv in jnm1.
      assert (1+j<=?n=false) by (apply leb_correct_conv; omega).
      simpl in H0. rewrite H0. simpl. rewrite cmpin. auto.
  + apply leb_complete_conv in cmpin as ccmpin.
    apply Nat.eqb_neq in nSj as nnSj. simpl in nov.
    assert (n=?j=false) by (apply Nat.eqb_neq; omega).
    rewrite H. simpl.
    assert (j<=?n=false) by (apply leb_correct_conv; omega).
    rewrite H0.
    assert (1+j<=?n=false) by (apply leb_correct_conv; omega).
    simpl in H1. rewrite H1. simpl. rewrite cmpin. auto. }
all: f_equal; try destruct nov; eauto.
all: unfold c_subs in *; rewrite v_shift_comm; aomega.
all: rewrite (c_negshift_subs_alt c _ (S i) (S j)); aomega.
all: try (apply v_no_var_shift; aomega).
all: rewrite v_shift_comm; do 4 f_equal; aomega. 
all: rewrite v_shift_negshift_comm; aomega.
}{
intros nov nov'; destruct c; unfold c_subs in *; simpl in *.
all: try destruct nov; try destruct H0; f_equal; eauto.
all: rewrite v_shift_comm; aomega; simpl.
all: assert (S(S i)=2+i) as ssi by (omega).
all: try rewrite (c_negshift_subs_alt _ _ (S i) (S j))
  || rewrite (c_negshift_subs_alt _ _ (S(S i)) (S(S j))); aomega.
all: try rewrite ssi; try (apply v_no_var_shift; aomega).
all: rewrite v_shift_comm; do 4 f_equal; aomega. 
all: rewrite v_shift_negshift_comm; aomega.
}{
intros nov nov'; destruct h; unfold c_subs in *; unfold h_subs in *; simpl in *.
all: try destruct nov; f_equal; eauto.
rewrite v_shift_comm; aomega; simpl.
assert (S(S i)=2+i) as ssi by (omega).
rewrite (c_negshift_subs_alt _ _ (S(S i)) (S(S j))); aomega.
2: rewrite ssi; (apply v_no_var_shift; aomega).
rewrite v_shift_comm; do 4 f_equal; aomega. 
rewrite v_shift_negshift_comm; aomega.
}
Qed.


Fixpoint v_sub_subs v i j vi vj:
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
intros cmp. destruct v; unfold v_subs; simpl in *.
{ destruct (n=?i) eqn:ni.
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
      rewrite H0, v_sub_no_var_same, v_negshift_shift, v_shift_0.
      reflexivity. omega. apply v_shift_makes_no_var.
    - simpl. rewrite ni. simpl. destruct (i<=?n) eqn:cmpin.
      * simpl. assert (n-1=?j=false).
        { apply leb_complete in cmpin. apply Nat.eqb_neq.
          apply Nat.eqb_neq in nsj. apply Nat.eqb_neq in ni. omega. }
        rewrite H. reflexivity.
      * simpl. assert (n=?j=false).
        { apply Nat.eqb_neq. apply leb_complete_conv in cmpin. omega. }
        rewrite H. reflexivity. }
all: f_equal; eauto.
all: unfold c_subs in *; rewrite v_shift_comm, c_sub_subs; aomega.
all: do 2 f_equal; try rewrite <-v_shift_sub; aomega.
all: try rewrite <-v_shift_comm; aomega.
}{
intros cmp. destruct c; unfold c_subs in *; simpl in *; f_equal; eauto.
all: rewrite v_shift_comm, c_sub_subs; aomega.
all: do 2 f_equal; try rewrite <-v_shift_sub; aomega.
all: try rewrite <-v_shift_comm; aomega.
all: assert (S(S i)=2+i) as ssi by (omega); rewrite ssi.
all: try rewrite <-v_shift_comm; aomega.
all: rewrite v_shift_comm; aomega; do 2 f_equal; rewrite v_shift_sub; aomega.
}{
intros cmp. destruct h; unfold h_subs in *; unfold c_subs in *;
simpl in *; f_equal; eauto.
assert (S(S i)=2+i) as ssi by (omega); rewrite ssi.
rewrite v_shift_comm, c_sub_subs; aomega.
do 2 f_equal. rewrite <-v_shift_comm; aomega.
rewrite v_shift_comm; aomega. do 2 f_equal; rewrite v_shift_sub; aomega.
}
Qed.


Fixpoint v_sub_subs_alt v i j vi vj:
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
intros cmp. destruct v; unfold v_subs; simpl.
{ destruct (n=?i) eqn:ni.
  apply Nat.eqb_eq in ni. subst.
  + assert (i=?j=false) by (apply Nat.eqb_neq; omega).
    rewrite H. simpl.
    assert (i=?i=true) by (apply Nat.eqb_eq; omega).
    rewrite H0, v_negshift_shift, v_negshift_shift.
    rewrite v_shift_0, v_shift_0. all: aomega.
  + destruct (n=?j) eqn:nj.
    - apply Nat.eqb_eq in nj. subst. simpl.
      assert (i<=?j=false) by (apply leb_correct_conv; omega).
      rewrite H. simpl.
      assert (j=?j=true) by (apply Nat.eqb_eq; omega).
      rewrite H0, v_sub_no_var_same, v_negshift_shift, v_shift_0; aomega.
      apply v_shift_makes_no_var.
    - simpl. rewrite ni. simpl. destruct (i<=?n) eqn:cmpin.
      * simpl. assert (n-1=?j=false).
        { apply leb_complete in cmpin. apply Nat.eqb_neq.
          apply Nat.eqb_neq in nj. apply Nat.eqb_neq in ni. omega. }
        rewrite H. auto.
      * simpl. rewrite nj. auto. }
all: f_equal; eauto.
all: unfold c_subs in *; rewrite v_shift_comm, c_sub_subs_alt; aomega.
all: do 2 f_equal; try rewrite <-v_shift_sub; aomega.
all: try rewrite <-v_shift_comm; aomega.
}{
intros cmp. destruct c; unfold c_subs in *; simpl in *; f_equal; eauto.
all: rewrite v_shift_comm, c_sub_subs_alt; aomega.
all: do 2 f_equal; try rewrite <-v_shift_sub; aomega.
all: try rewrite <-v_shift_comm; aomega.
all: assert (S(S i)=2+i) as ssi by (omega); rewrite ssi.
all: try rewrite <-v_shift_comm; aomega.
all: rewrite v_shift_comm; aomega; do 2 f_equal; rewrite v_shift_sub; aomega.
}{
intros cmp. destruct h; unfold h_subs in *; unfold c_subs in *;
simpl in *; f_equal; eauto.
assert (S(S i)=2+i) as ssi by (omega); rewrite ssi.
rewrite v_shift_comm, c_sub_subs_alt; aomega.
do 2 f_equal. rewrite <-v_shift_comm; aomega.
rewrite v_shift_comm; aomega. do 2 f_equal; rewrite v_shift_sub; aomega.
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
all: intros cmp.
{
specialize v_sub_subs as vss. specialize v_negshift_subs as vns.
unfold v_subs in *. rewrite vss, vns, v_shift_comm; aomega.
all: apply v_sub_makes_no_var. rewrite v_shift_comm; aomega.
all: apply v_shift_makes_no_var.
}{
specialize c_sub_subs as css. specialize c_negshift_subs as cns.
unfold c_subs in *. rewrite css, cns, v_shift_comm; aomega.
all: apply c_sub_makes_no_var || apply v_sub_makes_no_var.
rewrite v_shift_comm; aomega. all: apply v_shift_makes_no_var.
}{
specialize h_sub_subs as hss. specialize h_negshift_subs as hns.
unfold h_subs in *. rewrite hss, hns, v_shift_comm; aomega.
all: apply h_sub_makes_no_var || apply v_sub_makes_no_var.
rewrite v_shift_comm; aomega. all: apply v_shift_makes_no_var.
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
all: intros cmp.
{
specialize v_sub_subs_alt as vss. specialize v_negshift_subs_alt as vns.
unfold v_subs in *. rewrite vss, vns, <-v_shift_comm; aomega.
all: apply v_sub_makes_no_var. rewrite <-v_shift_comm; aomega.
all: apply v_shift_makes_no_var.
}{
specialize c_sub_subs_alt as css. specialize c_negshift_subs_alt as cns.
unfold c_subs in *. rewrite css, cns, <-v_shift_comm; aomega.
all: apply c_sub_makes_no_var || apply v_sub_makes_no_var.
rewrite <-v_shift_comm; aomega. all: apply v_shift_makes_no_var.
}{
specialize h_sub_subs_alt as hss. specialize h_negshift_subs_alt as hns.
unfold h_subs in *. rewrite hss, hns, <-v_shift_comm; aomega.
all: apply h_sub_makes_no_var || apply v_sub_makes_no_var.
rewrite <-v_shift_comm; aomega. all: apply v_shift_makes_no_var.
}
Qed.

(* ==================== Instantiation ==================== *)

Lemma inst_len_shift I i j :
  inst_len (inst_shift I i j) = inst_len I.
Proof.
revert i j. induction I; intros; simpl; f_equal; auto.
Qed.


Fixpoint get_inst_val_shift I m k c {struct I}:
  get_inst_val (inst_shift I k c) m 
  = f_opt (get_inst_val I m) (fun v => Some (v_shift v k c)).
Proof.
destruct I; simpl. auto. destruct m; simpl; auto.
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
{ rewrite get_inst_val_shift. destruct (get_inst_val I n); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; eaomega.
all: apply c_shift_inst; auto.
}{
destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; eaomega.
all: apply c_shift_inst; auto.
}{
destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_comm; simpl; eaomega.
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
{ rewrite get_inst_val_negshift. destruct (get_inst_val I n); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; eaomega.
all: apply c_negshift_inst; simpl; constructor.
all: try apply inst_no_var_shift; eaomega.
}{
assert (S(S cut) = 2+cut) as same by omega.
intros. destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; eaomega.
all: apply c_negshift_inst; try omega.
all: simpl; constructor; try constructor; try rewrite same.
all: try apply inst_no_var_shift; eaomega.
}{
assert (S(S cut) = 2+cut) as same by omega.
intros. destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_negshift_comm; simpl; eaomega.
all: apply c_negshift_inst; try omega.
all: simpl; constructor; try constructor; try rewrite same.
all: try apply inst_no_var_shift; eaomega.
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
{ rewrite get_inst_val_sub. destruct (get_inst_val I n); simpl; auto. }
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; eaomega.
all: apply c_sub_inst.
}{
destruct c; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; eaomega.
all: apply c_sub_inst.
}{
destruct h; simpl; eauto.
all: f_equal; eauto.
all: rewrite inst_shift_sub; simpl; eaomega.
all: apply c_sub_inst.
}
Qed.


Lemma inst_subs_unfold I i v_s:
  inst_negshift (inst_sub I (i, v_shift v_s 1 i)) 1 i = inst_subs I i v_s.
Proof.
revert i. induction I; intros; simpl. auto. rewrite IHI. auto.
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
rewrite v_sub_inst, v_negshift_inst, inst_subs_unfold; auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}{
unfold c_subs. 
rewrite c_sub_inst, c_negshift_inst, inst_subs_unfold; auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}{
unfold h_subs. 
rewrite h_sub_inst, h_negshift_inst, inst_subs_unfold; auto.
apply inst_sub_makes_no_var. apply v_shift_makes_no_var.
}
Qed.


Fixpoint inst_shift_insert I n v i {struct I}:
    inst_shift (inst_insert I n v) i 0 
  = inst_insert (inst_shift I i 0) n (v_shift v i 0).
Proof.
destruct I; simpl; destruct (n=?0); simpl; auto. f_equal. auto.
Qed.


Lemma inst_insert_extend I i vs v:
  InstU (inst_insert I i vs) v = inst_insert (InstU I v) (S i) vs.
Proof.
  simpl. do 2 f_equal. omega.
Qed.


Fixpoint v_inst_no_var_same I vs i v:
  v_no_var v i -> v_under_var v (1+inst_len I) ->
  i <= inst_len I ->
  v_inst v (inst_insert I i vs) = v_inst (v_negshift v 1 i) I

with c_inst_no_var_same I vs i c:
  c_no_var c i -> c_under_var c (1+inst_len I) -> 
  i <= inst_len I ->
  c_inst c (inst_insert I i vs) = c_inst (c_negshift c 1 i) I

with h_inst_no_var_same I vs i h:
  h_no_var h i -> h_under_var h (1+inst_len I) ->
  i <= inst_len I ->
  h_inst h (inst_insert I i vs) = h_inst (h_negshift h 1 i) I.

Proof.
{
intros safe under ilen. destruct v; simpl; auto.
{ destruct (i<=?n) eqn:cmp.
  + apply leb_complete in cmp. simpl in *.
    destruct n. omega. 
    rewrite inst_insert_above. simpl.
    assert (n-0=n) by omega. rewrite H. all: eaomega.
  + apply leb_complete_conv in cmp. simpl in *.
    rewrite inst_insert_under. simpl. all: eaomega. }
all: f_equal; simpl in *; try destruct safe; try destruct under; eauto.
all: rewrite inst_shift_insert, inst_insert_extend.
all: apply c_inst_no_var_same; simpl; eaomega.
all: rewrite inst_len_shift; eaomega.
}{
intros safe under ilen. destruct c; simpl.
all: f_equal; simpl in *; try destruct safe; try destruct under; eauto.
all: try rewrite inst_shift_insert, inst_insert_extend.
all: try rewrite inst_insert_extend; try apply c_inst_no_var_same; simpl; auto.
all: try rewrite inst_len_shift; eaomega.
all: try destruct H0; auto; destruct H2; auto.
}{
intros safe under ilen. destruct h; simpl. auto.
f_equal; simpl in *; destruct safe; destruct under. auto.
rewrite inst_shift_insert, inst_insert_extend, inst_insert_extend.
apply c_inst_no_var_same; auto; simpl; rewrite inst_len_shift. auto. omega.
}
Qed.
