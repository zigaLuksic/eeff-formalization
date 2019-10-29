Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
Require Export syntax Arith.
Require Import Le Compare_dec.

Module Sub.

Definition id_up (id : var_id) d (cut : nat) :=
  let (id_name, id_n) := id in
  if Nat.leb cut id_n then (id_name, id_n + d) else id.

Definition id_down (id : var_id) d (cut : nat) :=
  let (id_name, id_n) := id in
  if Nat.leb cut id_n then (id_name, id_n - d) else id.

Definition fits_sub (id : var_id) (db_i : nat) :=
  let (id_name, id_n) := id in Nat.eqb id_n db_i.

Fixpoint v_shift (v : val) d (cut : nat) :=
match v with
| Var id => Var (id_up id d cut)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_shift v' d cut)
| Inr v' => Inr (v_shift v' d cut)
| Pair v1 v2 => Pair (v_shift v1 d cut) (v_shift v2 d cut)
| Fun x c => Fun x (c_shift c d (cut+1))
| Handler x c_ret h =>
    Handler x (c_shift c_ret d (cut+1)) (h_shift h d cut)
end
with c_shift (c : comp) d (cut : nat) :=
match c with
| Ret v => Ret (v_shift v d cut)
| Absurd v => Absurd (v_shift v d cut)
| ΠMatch v (x, y) c =>
    ΠMatch (v_shift v d cut) (x, y) (c_shift c d (cut+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_shift v d cut)
      xl (c_shift cl d (cut+1))
      xr (c_shift cr d (cut+1))
| App v1 v2 => App (v_shift v1 d cut) (v_shift v2 d cut)
| Op op v_arg y c =>
    Op op (v_shift v_arg d cut) y (c_shift c d (cut+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_shift c1 d (cut+2)) (c_shift c2 d (cut+1))
| DoBind x c1 c2 =>
    DoBind x (c_shift c1 d cut) (c_shift c2 d (cut+1))
| Handle v c' => Handle (v_shift v d cut) (c_shift c' d cut)
end
with h_shift (h : hcases) d (cut : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_shift h d cut) op x k (c_shift c d (cut+2))
end.

Fixpoint sub_shift (sub : nat * val) (d : nat) :=
  let (db_i, v_s) := sub in
  (db_i + d, v_shift v_s d 0).

Fixpoint v_negshift (v : val) d (cut : nat) :=
match v with
| Var id => Var (id_down id d cut)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_negshift v' d cut)
| Inr v' => Inr (v_negshift v' d cut)
| Pair v1 v2 => Pair (v_negshift v1 d cut) (v_negshift v2 d cut)
| Fun x c => Fun x (c_negshift c d (cut+1))
| Handler x c_ret h =>
    Handler x (c_negshift c_ret d (cut+1)) (h_negshift h d cut)
end
with c_negshift (c : comp) d (cut : nat) :=
match c with
| Ret v => Ret (v_negshift v d cut)
| Absurd v => Absurd (v_negshift v d cut)
| ΠMatch v (x, y) c =>
    ΠMatch (v_negshift v d cut) (x, y) (c_negshift c d (cut+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_negshift v d cut)
      xl (c_negshift cl d (cut+1))
      xr (c_negshift cr d (cut+1))
| App v1 v2 => App (v_negshift v1 d cut) (v_negshift v2 d cut)
| Op op v_arg y c =>
    Op op (v_negshift v_arg d cut) y (c_negshift c d (cut+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_negshift c1 d (cut+2)) (c_negshift c2 d (cut+1))
| DoBind x c1 c2 =>
    DoBind x (c_negshift c1 d cut) (c_negshift c2 d (cut+1))
| Handle v c' => Handle (v_negshift v d cut) (c_negshift c' d cut)
end
with h_negshift (h : hcases) d (cut : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_negshift h d cut) op x k (c_negshift c d (cut+2))
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
end
with c_sub (c : comp) (sub : nat * val) :=
match c with
| Ret v => Ret (v_sub v sub)
| Absurd v => Absurd (v_sub v sub)
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
| LetRec f x c1 c2 =>
    LetRec f x 
      (c_sub c1 (sub_shift sub 2))
      (c_sub c2 (sub_shift sub 1))
| DoBind x c1 c2 =>
    DoBind x (c_sub c1 sub) (c_sub c2 (sub_shift sub 1))
| Handle v c' => Handle (v_sub v sub) (c_sub c' sub)
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

(* Instantiates the outer binder, takes care of all the shifting. *)
Definition v_sub_out (v:val) (v_s:val) :=
  Sub.v_negshift (Sub.v_sub v (0, (Sub.v_shift v_s 1 0))) 1 0.

Definition c_sub_out (c:comp) (v_s:val) :=
  Sub.c_negshift (Sub.c_sub c (0, (Sub.v_shift v_s 1 0))) 1 0.

Definition h_sub_out (h:hcases) (v_s:val) :=
  Sub.h_negshift (Sub.h_sub h (0, (Sub.v_shift v_s 1 0))) 1 0.

Definition c_sub2_out (c:comp) v1 v0 :=
  (* 1 -> v1, 0 -> v0 *)
  c_sub_out (c_sub_out c (Sub.v_shift v0 1 0)) v1.