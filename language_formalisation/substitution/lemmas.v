Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export substitution Arith.
Require Import Le Compare_dec.

Module SubLemma.

(* Auxiliary lemmas *)
Lemma n_plus_minus (n:nat):
  n + 1 - 1 = n.
Proof.
induction n. auto.
simpl.
assert (forall n, n + 1 = S n).
- intro. induction n0. auto. simpl. rewrite IHn0. auto.
- rewrite (H n). auto.
Qed.

Lemma n_le_n_plus_m (n:nat) (m:nat):
  n <= n + m.
Proof.
revert m. induction n; intro m.
- simpl. apply le_0_n.
- simpl. apply le_n_S. specialize (IHn m). assumption.
Qed.

Lemma safe_minus a b c:
  c <= b -> a + b - c = a + (b - c).
Proof.
revert a b.
induction c; intros a b c_le_b.
+ assert (forall n, n - 0 = n).
  { intro n. induction n; simpl; reflexivity. }
  specialize (H b) as Hb.
  specialize (H (a + b)) as Hab.
  rewrite Hb. rewrite Hab. reflexivity.
+ induction b.
  - assert (~ S c <= 0) by apply (le_Sn_0 _ ). destruct H. assumption.
  - simpl. assert (forall n m, n + S m = S (n + m)) by auto.
    specialize (H a b). rewrite H. simpl. apply IHc. apply le_S_n. assumption.
Qed.

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
(* Main lemmas *)
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
  assert (forall n, n - 0 = n).
  intro n. induction n; simpl; try rewrite IHn; reflexivity.
  specialize (H v0).
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
       assert (forall n, n + 1 = S n).
       intro. induction n0. auto. simpl. rewrite IHn0. auto.
       rewrite (H db_i).
       apply (le_n_S _ _) in Heqcmp. apply (le_Sn_le _ _) in Heqcmp.
       assumption.
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       assert (cut <= db_i + n).
       { assert (db_i <= db_i + n) by apply (n_le_n_plus_m _ _).
         apply (le_trans _ _ _ Heqcmp H0). }
       apply (leb_correct _ _) in H0. rewrite H0. simpl.
       rewrite safe_minus. reflexivity. assumption.
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

End SubLemma.