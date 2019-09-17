Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Export syntax Arith.
Require Import Le Compare_dec.

Module Sub.

Definition id_up (id : var_id) (cut : nat) :=
  let (id_name, id_n) := id in
  if Nat.leb cut id_n then (id_name, id_n + 1) else id.

Definition id_down (id : var_id) (cut : nat) :=
  let (id_name, id_n) := id in
  if Nat.leb cut id_n then (id_name, id_n - 1) else id.

Definition fits_sub (id : var_id) (db_i : nat) :=
  let (id_name, id_n) := id in Nat.eqb id_n db_i.

Fixpoint v_shift (v : val) (cut : nat) :=
match v with
| Var id => Var (id_up id cut)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_shift v' cut)
| Inr v' => Inr (v_shift v' cut)
| Pair v1 v2 => Pair (v_shift v1 cut) (v_shift v2 cut)
| Fun x c => Fun x (c_shift c (cut+1))
| Handler x c_ret h =>
    Handler x (c_shift c_ret (cut+1)) (h_shift h cut)
| VAnnot v' α => VAnnot (v_shift v' cut) α
end
with c_shift (c : comp) (cut : nat) :=
match c with
| Ret v => Ret (v_shift v cut)
| ΠMatch v (x, y) c =>
    ΠMatch (v_shift v cut) (x, y) (c_shift c (cut+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_shift v cut)
      xl (c_shift cl (cut+1))
      xr (c_shift cr (cut+1))
| App v1 v2 => App (v_shift v1 cut) (v_shift v2 cut)
| Op op v_arg y c =>
    Op op (v_shift v_arg cut) y (c_shift c (cut+1))
| LetRec f x f_ty c1 c2 =>
    LetRec f x f_ty (c_shift c1 (cut+2)) (c_shift c2 (cut+1))
| DoBind x c1 c2 =>
    DoBind x (c_shift c1 cut) (c_shift c2 (cut+1))
| Handle v c' => Handle (v_shift v cut) (c_shift c' cut)
| CAnnot c' C => CAnnot (c_shift c' cut) C
end
with h_shift (h : hcases) (cut : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_shift h cut) op x k (c_shift c (cut+2))
end.

Fixpoint sub_shift (sub : nat * val) (d : nat) :=
  let (db_i, v_s) := sub in
  match d with
  | 0 => sub
  | S d' => sub_shift (db_i+1, v_shift v_s 0) (d')
  end.

Fixpoint v_negshift (v : val) (cut : nat) :=
match v with
| Var id => Var (id_down id cut)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_negshift v' cut)
| Inr v' => Inr (v_negshift v' cut)
| Pair v1 v2 => Pair (v_negshift v1 cut) (v_negshift v2 cut)
| Fun x c => Fun x (c_negshift c (cut+1))
| Handler x c_ret h =>
    Handler x (c_negshift c_ret (cut+1)) (h_negshift h cut)
| VAnnot v' α => VAnnot (v_negshift v' cut) α
end
with c_negshift (c : comp) (cut : nat) :=
match c with
| Ret v => Ret (v_negshift v cut)
| ΠMatch v (x, y) c =>
    ΠMatch (v_negshift v cut) (x, y) (c_negshift c (cut+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_negshift v cut)
      xl (c_negshift cl (cut+1))
      xr (c_negshift cr (cut+1))
| App v1 v2 => App (v_negshift v1 cut) (v_negshift v2 cut)
| Op op v_arg y c =>
    Op op (v_negshift v_arg cut) y (c_negshift c (cut+1))
| LetRec f x f_ty c1 c2 =>
    LetRec f x f_ty (c_negshift c1 (cut+2)) (c_negshift c2 (cut+1))
| DoBind x c1 c2 =>
    DoBind x (c_negshift c1 cut) (c_negshift c2 (cut+1))
| Handle v c' => Handle (v_negshift v cut) (c_negshift c' cut)
| CAnnot c' C => CAnnot (c_negshift c' cut) C
end
with h_negshift (h : hcases) (cut : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_negshift h cut) op x k (c_negshift c (cut+2))
end.

Fixpoint v_sub (v : val) (sub : nat * val) :=
let (db_i, v_s) := sub in
match v with
| Var id => if fits_sub id db_i then v_s else Var id 
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_sub v' sub)
| Inr v' => Inr (v_sub v' sub)
| Pair v1 v2 => Pair (v_sub v1 sub) (v_sub v2 sub)
| Fun x c => Fun x (c_sub c (sub_shift sub 1))
| Handler x c_ret h =>
    Handler x
      (c_sub c_ret (sub_shift sub 1))
      (h_sub h sub)
| VAnnot v' α => VAnnot (v_sub v' sub) α
end
with c_sub (c : comp) (sub : nat * val) :=
match c with
| Ret v => Ret (v_sub v sub)
| ΠMatch v (x, y) c =>
    ΠMatch (v_sub v sub) (x, y)
      (c_sub c (sub_shift sub 2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_sub v sub)
      xl (c_sub cl (sub_shift sub 1))
      xr (c_sub cr (sub_shift sub 1))
| App v1 v2 => App (v_sub v1 sub) (v_sub v2 sub)
| Op op v_arg y c =>
    Op op (v_sub v_arg sub) y (c_sub c (sub_shift sub 1))
| LetRec f x f_ty c1 c2 =>
    LetRec f x f_ty
      (c_sub c1 (sub_shift sub 2))
      (c_sub c2 (sub_shift sub 1))
| DoBind x c1 c2 =>
    DoBind x (c_sub c1 sub) (c_sub c2 (sub_shift sub 1))
| Handle v c' => Handle (v_sub v sub) (c_sub c' sub)
| CAnnot c' C => CAnnot (c_sub c' sub) C
end
with h_sub (h : hcases) (sub : nat * val) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU
      (h_sub h sub)
      op x k
      (c_sub c (sub_shift sub 2))
end
.

End Sub.


Lemma stupid_auxiliary_lemma (n:nat):
  n + 1 - 1 = n.
Proof.
induction n. auto.
simpl.
assert (forall n, n + 1 = S n).
- intro. induction n0. auto. simpl. rewrite IHn0. auto.
- rewrite (H n). auto.
Qed.

Lemma vshifts_cancel (n:nat) (v:val) :
  Sub.v_negshift (Sub.v_shift v n) n = v
with cshifts_cancel (n:nat) (c:comp) :
  Sub.c_negshift (Sub.c_shift c n) n = c
with hshifts_cancel (n:nat) (h:hcases) :
  Sub.h_negshift (Sub.h_shift h n) n = h.
Proof.
{
clear vshifts_cancel.  
revert n.
induction v; intros n; simpl.
+ (* The only relevant case. *)
  destruct v as (name, db_i). simpl.
  f_equal. f_equal.
  remember (n <=? db_i) as cmp.
  induction cmp.
  - simpl. assert (n <= db_i + 1).
    -- apply eq_sym in Heqcmp.
       apply (leb_complete _ _) in Heqcmp.
       assert (forall n, n + 1 = S n).
       intro. induction n0. auto. simpl. rewrite IHn0. auto.
       rewrite (H db_i).
       apply (le_n_S _ _) in Heqcmp. apply (le_Sn_le _ _) in Heqcmp.
       assumption.
    -- apply (leb_correct _ _) in H. rewrite H. simpl.
       rewrite (stupid_auxiliary_lemma db_i). reflexivity.
  - simpl. rewrite <-Heqcmp. reflexivity.
+ f_equal. reflexivity.
+ f_equal. 
+ f_equal. specialize (IHv n). assumption.
+ f_equal. specialize (IHv n). assumption.
+ f_equal. specialize (IHv1 n). assumption.
  specialize (IHv2 n). assumption.
+ f_equal. rewrite (cshifts_cancel (n+1) c). reflexivity.
+ f_equal.
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

Definition vsub_out (v:val) (v_s:val) :=
  Sub.v_negshift (Sub.v_sub v (0, (Sub.v_shift v_s 0))) 0.

Definition csub_out (c:comp) (v_s:val) :=
  Sub.c_negshift (Sub.c_sub c (0, (Sub.v_shift v_s 0))) 0.

Definition hsub_out (h:hcases) (v_s:val) :=
  Sub.h_negshift (Sub.h_sub h (0, (Sub.v_shift v_s 0))) 0.