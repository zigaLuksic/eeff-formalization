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

Lemma n_minus_m_le_n (n:nat) (m:nat):
  n - m <= n.
Proof.
revert m. induction n; intro m.
- simpl. apply le_refl.
- induction m.
  + simpl. apply le_refl.
  + simpl. specialize (IHn m).
    assert (n <= S n).
    * assert (S n <= S n) by apply le_refl.
      apply le_Sn_le in H. assumption.
    * apply (le_trans _ _ _ IHn H). 
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
  Sub.c_negshift (Sub.c_shift c n cut) n cut = (Sub.c_shift c (n - m) cut)

with hshifts_cancel (n:nat) (m:nat) (cut:nat) (h:hcases) :
  (m <= n) ->  
  Sub.h_negshift (Sub.h_shift h n cut) n cut = (Sub.h_shift h (n - m) cut).
Proof.
{
clear vshifts_cancel.  
revert n m cut.
induction v; intros n m cut m_leq_n; simpl.
+ (* The only relevant case. *)
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
       assert (n - m <= db_i).
       { assert (n-m <= n) by apply (n_minus_m_le_n _ _).
         apply (le_trans _ _ _ H0 Heqcmp). }
       apply (leb_correct _ _) in H0. rewrite H0. simpl.
       rewrite n_plus_minus.
       assert (m <= db_i + 1) by apply (le_trans _ _ _ m_leq_n H).
       apply (leb_correct _ _) in H1. rewrite H1. simpl.
    
    rewrite H. simpl.
       rewrite (n_plus_minus db_i). reflexivity.
  - simpl. rewrite <-Heqcmp. reflexivity.
+ f_equal. reflexivity.
+ f_equal. 
+ f_equal. specialize (IHv n). assumption.
+ f_equal. specialize (IHv n). assumption.
+ f_equal. specialize (IHv1 n). assumption.
  specialize (IHv2 n). assumption.
+ f_equal. rewrite (cshifts_cancel (n+1) c). reflexivity.
+ f_equal.
Lemma n_minus_m_le_n (n:nat) (m:nat):
  n - m <= n.
Proof.


(* Main lemmas *)
  - rewrite (cshifts_cancel (n+1) c). reflexivity.
  - rewrite (hshifts_cancel n h). reflexivity.
+ f_equal. specialize (IHv n). assumption.
}
{
clear cshifts_cancel.
revert n.
induction c; intro n.
Focus 2. (* First focus on the only one we have problems with. *)
+ destruct p. simpl. f_equal.
  - rewrite (vshifts_cancel n v). reflexivity.
  Focus 2.
  - specialize (IHc (n+2)). assumption. 
all: simpl; f_equal.
+ rewrite (vshifts_cancel n v). reflexivity.
+ rewrite (vshifts_cancel n v). reflexivity.
+ specialize (IHc1 (n+1)). assumption. 
+ specialize (IHc2 (n+1)). assumption. 
+ rewrite (vshifts_cancel n v). reflexivity.
+ rewrite (vshifts_cancel n v0). reflexivity.
+ rewrite (vshifts_cancel n v). reflexivity.
+ specialize (IHc (n+1)). assumption. 
+ specialize (IHc1 (n+2)). assumption. 
+ specialize (IHc2 (n+1)). assumption. 
+ specialize (IHc1 (n)). assumption. 
+ specialize (IHc2 (n+1)). assumption. 
+ rewrite (vshifts_cancel n v). reflexivity.
+ specialize (IHc (n)). assumption.
+ specialize (IHc (n)). assumption.
}
{
clear hshifts_cancel.
revert n.
induction h; intro n.
+ simpl. reflexivity.
+ simpl. f_equal.
  - specialize (IHh n). assumption.
  - rewrite (cshifts_cancel (n+2) c). reflexivity.
}
Qed.

End SubLemma.