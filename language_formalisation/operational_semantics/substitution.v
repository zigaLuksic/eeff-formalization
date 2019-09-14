Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Export syntax.

Module Sub.

Definition id_reduce_on_name_match
  (id_to_reduce : var_id) (id_to_match : var_id) : var_id
:=
  let (id_name1, id_n1) := id_to_reduce in
  let (id_name2, id_n2) := id_to_match in
  if id_name1 == id_name2 then (id_name1, id_n1 - 1) else (id_name1, id_n1).

Definition id_increase_on_name_match 
  (id_to_increase : var_id) (id_to_match : var_id) : var_id
:=
  let (id_name1, id_n1) := id_to_increase in
  let (id_name2, id_n2) := id_to_match in
  if id_name1 == id_name2 then (id_name1, id_n1 + 1) else (id_name1, id_n1).


Fixpoint v_open (id : var_id) (v : val) (db_i : nat) :=
match v with
| Var id' => Var (id_increase_on_name_match id' id)
| BoundVar n => if Nat.eqb n db_i then Var id else BoundVar n
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_open id v' db_i)
| Inr v' => Inr (v_open id v' db_i)
| Pair v1 v2 => Pair (v_open id v1 db_i) (v_open id v2 db_i)
| Fun x c => Fun x (c_open id c (db_i+1))
| Handler x c_ret h =>
    Handler x (c_open id c_ret (db_i+1)) (h_open id h db_i)
| VAnnot v' α => VAnnot (v_open id v' db_i) α
end
with c_open (id : var_id) (c : comp) (db_i : nat) :=
match c with
| Ret v => Ret (v_open id v db_i)
| ΠMatch v (x, y) c =>
    ΠMatch (v_open id v db_i) (x, y) (c_open id c (db_i+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_open id v db_i)
      xl (c_open id cl (db_i+1))
      xr (c_open id cr (db_i+1))
| App v1 v2 => App (v_open id v1 db_i) (v_open id v2 db_i)
| Op op v_arg y c =>
    Op op (v_open id v_arg db_i) y (c_open id c (db_i+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_open id c1 (db_i+2)) (c_open id c2 (db_i+1))
| DoBind x c1 c2 =>
    DoBind x (c_open id c1 db_i) (c_open id c2 (db_i+1))
| Handle v c' => Handle (v_open id v db_i) (c_open id c' db_i)
| CAnnot c' C => CAnnot (c_open id c' db_i) C
end
with h_open (id : var_id) (h : hcases) (db_i : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_open id h db_i) op x k (c_open id c (db_i+2))
end.

Fixpoint v_close (id : var_id) (v : val) (db_i : nat) :=
match v with
| Var id' => Var (id_increase_on_name_match id' id)
| BoundVar n => if Nat.eqb n db_i then Var id else BoundVar n
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_close id v' db_i)
| Inr v' => Inr (v_close id v' db_i)
| Pair v1 v2 => Pair (v_close id v1 db_i) (v_close id v2 db_i)
| Fun x c => Fun x (c_close id c (db_i+1))
| Handler x c_ret h =>
    Handler x (c_close id c_ret (db_i+1)) (h_close id h db_i)
| VAnnot v' α => VAnnot (v_close id v' db_i) α
end
with c_close (id : var_id) (c : comp) (db_i : nat) :=
match c with
| Ret v => Ret (v_close id v db_i)
| ΠMatch v (x, y) c =>
    ΠMatch (v_close id v db_i) (x, y) (c_close id c (db_i+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_close id v db_i)
      xl (c_close id cl (db_i+1))
      xr (c_close id cr (db_i+1))
| App v1 v2 => App (v_close id v1 db_i) (v_close id v2 db_i)
| Op op v_arg y c =>
    Op op (v_close id v_arg db_i) y (c_close id c (db_i+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_close id c1 (db_i+2)) (c_close id c2 (db_i+1))
| DoBind x c1 c2 =>
    DoBind x (c_close id c1 db_i) (c_close id c2 (db_i+1))
| Handle v c' => Handle (v_close id v db_i) (c_close id c' db_i)
| CAnnot c' C => CAnnot (c_close id c' db_i) C
end
with h_close (id : var_id) (h : hcases) (db_i : nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (h_close id h db_i) op x k (c_close id c (db_i+2))
end

.

End Sub.



Fixpoint DB_vshift (v : val) (cut : nat) {struct v}:=
match v with
| Var id => Var (id_shift id cut 1)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (DB_vshift v' cut)
| Inr v' => Inr (DB_vshift v' cut)
| Pair v1 v2 => Pair (DB_vshift v1 cut) (DB_vshift v2 cut)
| Fun x c => Fun x (DB_cshift c (cut+1))
| Handler x c_ret h =>
    Handler x (DB_cshift c_ret (cut+1)) (DB_hshift h cut)
| VAnnot v' α => VAnnot (DB_vshift v' cut) α
end
with DB_cshift (c : comp) (cut : nat) {struct c}:=
match c with
| Ret v => Ret (DB_vshift v cut)
| ΠMatch v (x, y) c =>
    ΠMatch (DB_vshift v cut) (x, y) (DB_cshift c (cut+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (DB_vshift v cut) xl (DB_cshift cl (cut+1))
      xr (DB_cshift cr (cut+1))
| App v1 v2 => App (DB_vshift v1 cut) (DB_vshift v2 cut)
| Op op v_arg y c =>
    Op op (DB_vshift v_arg cut) y (DB_cshift c (cut+1))
| LetRec f x c1 c2 =>
    LetRec f x (DB_cshift c1 (cut+2)) (DB_cshift c2 (cut+1))
| DoBind x c1 c2 =>
    DoBind x (DB_cshift c1 cut) (DB_cshift c2 (cut+1))
| Handle v c' => Handle (DB_vshift v cut) (DB_cshift c' cut)
| CAnnot c' C => CAnnot (DB_cshift c' cut) C
end
with DB_hshift (h : hcases) (cut : nat) {struct h}:=
match h with
| CasesØ => CasesØ
| CasesU h op x k c => 
    CasesU (DB_hshift h cut) op x k (DB_cshift c (cut+2))
end
.
