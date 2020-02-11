Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
Require Export syntax.
Require Import Le.

(* ==================== Shifts and Subs ==================== *)

Module Sub.

Fixpoint v_shift v d cut :=
  match v with
  | Var (x, n) => if cut <=? n then Var (x, d + n) else Var (x, n)
  | Unit => Unit
  | Int n => Int n
  | Inl v' => Inl (v_shift v' d cut)
  | Inr v' => Inr (v_shift v' d cut)
  | Pair v1 v2 =>
      Pair (v_shift v1 d cut) (v_shift v2 d cut)
  | ListNil => ListNil
  | ListCons v vs => 
      ListCons (v_shift v d cut) (v_shift vs d cut)
  | Fun x c =>
      Fun x (c_shift c d (1+cut))
  | Handler x c_ret h =>
      Handler x (c_shift c_ret d (1+cut)) (h_shift h d cut)
  end
with c_shift c d cut :=
  match c with
  | Ret v => Ret (v_shift v d cut)
  | Absurd v => Absurd (v_shift v d cut)
  | ΠMatch v x y c => 
      ΠMatch (v_shift v d cut) x y (c_shift c d (2+cut))
  | ΣMatch v x c1 y c2 =>
      ΣMatch (v_shift v d cut) 
        x (c_shift c1 d (1+cut)) y (c_shift c2 d (1+cut))
  | ListMatch v c1 x xs c2 =>
      ListMatch (v_shift v d cut)
        (c_shift c1 d cut) x xs (c_shift c2 d (2+cut))
  | App v1 v2 => 
      App (v_shift v1 d cut) (v_shift v2 d cut)
  | Op op v_arg y c => 
      Op op (v_shift v_arg d cut) y (c_shift c d (1+cut))
  | LetRec f x c1 c2 => 
      LetRec f x (c_shift c1 d (2+cut)) (c_shift c2 d (1+cut))
  | DoBind x c1 c2 => 
      DoBind x (c_shift c1 d cut) (c_shift c2 d (1+cut))
  | Handle v c' => 
      Handle (v_shift v d cut) (c_shift c' d cut)
  end
with h_shift h d cut :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op x k c => 
      CasesU (h_shift h d cut) op x k (c_shift c d (2+cut))
  end.


Definition sub_shift (sub : nat * val) d :=
  let (db_i, v_s) := sub in (d + db_i, v_shift v_s d 0).


Fixpoint v_negshift v d cut :=
  match v with
  | Var (x, n) => 
      if Nat.leb cut n then Var (x, n - d) else Var (x, n)   
  | Unit => Unit
  | Int n => Int n
  | Inl v' => Inl (v_negshift v' d cut)
  | Inr v' => Inr (v_negshift v' d cut)
  | Pair v1 v2 => 
      Pair (v_negshift v1 d cut) (v_negshift v2 d cut)
  | ListNil => ListNil
  | ListCons v vs => 
      ListCons (v_negshift v d cut) (v_negshift vs d cut)
  | Fun x c => 
      Fun x (c_negshift c d (1+cut))
  | Handler x c_ret h =>
      Handler x (c_negshift c_ret d (1+cut)) (h_negshift h d cut)
  end
with c_negshift c d cut :=
  match c with
  | Ret v => Ret (v_negshift v d cut)
  | Absurd v => Absurd (v_negshift v d cut)
  | ΠMatch v x y c => 
      ΠMatch (v_negshift v d cut) x y (c_negshift c d (2+cut))
  | ΣMatch v x c1 y c2 =>
      ΣMatch (v_negshift v d cut)
        x (c_negshift c1 d (1+cut)) y (c_negshift c2 d (1+cut))
  | ListMatch v c1 x xs c2 =>
      ListMatch (v_negshift v d cut)
        (c_negshift c1 d cut) x xs (c_negshift c2 d (2+cut))
  | App v1 v2 => 
      App (v_negshift v1 d cut) (v_negshift v2 d cut)
  | Op op v_arg y c => 
      Op op (v_negshift v_arg d cut) y (c_negshift c d (1+cut))
  | LetRec f x c1 c2 =>
      LetRec f x (c_negshift c1 d (2+cut)) (c_negshift c2 d (1+cut))
  | DoBind x c1 c2 => 
      DoBind x (c_negshift c1 d cut) (c_negshift c2 d (1+cut))
  | Handle v c' => 
      Handle (v_negshift v d cut) (c_negshift c' d cut)
  end
with h_negshift h d cut :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op x k c => 
      CasesU (h_negshift h d cut) op x k (c_negshift c d (2+cut))
  end.


Fixpoint v_sub v (sub : nat * val) :=
let (db_i, v_s) := sub in
  match v with
  | Var (x, n) => if n =? db_i then v_s else Var (x, n) 
  | Unit => Unit
  | Int n => Int n
  | Inl v' => Inl (v_sub v' sub)
  | Inr v' => Inr (v_sub v' sub)
  | Pair v1 v2 => 
      Pair (v_sub v1 sub) (v_sub v2 sub)
  | ListNil => ListNil
  | ListCons v vs => 
      ListCons (v_sub v sub) (v_sub vs sub)
  | Fun x c => 
      Fun x (c_sub c (sub_shift sub 1))
  | Handler x c_ret h =>
      Handler x (c_sub c_ret (sub_shift sub 1)) (h_sub h sub)
  end
with c_sub c (sub : nat * val) :=
  match c with
  | Ret v => Ret (v_sub v sub)
  | Absurd v => Absurd (v_sub v sub)
  | ΠMatch v x y c => 
      ΠMatch (v_sub v sub) x y (c_sub c (sub_shift sub 2))
  | ΣMatch v xl cl xr cr =>
      ΣMatch (v_sub v sub)
        xl (c_sub cl (sub_shift sub 1)) xr (c_sub cr (sub_shift sub 1))
  | ListMatch v c1 x xs c2 =>
      ListMatch (v_sub v sub)
        (c_sub c1 sub) x xs (c_sub c2 (sub_shift sub 2))
  | App v1 v2 => 
      App (v_sub v1 sub) (v_sub v2 sub)
  | Op op v_arg y c => 
      Op op (v_sub v_arg sub) y (c_sub c (sub_shift sub 1))
  | LetRec f x c1 c2 =>
      LetRec f x (c_sub c1 (sub_shift sub 2)) (c_sub c2 (sub_shift sub 1))
  | DoBind x c1 c2 => 
      DoBind x (c_sub c1 sub) (c_sub c2 (sub_shift sub 1))
  | Handle v c' => 
      Handle (v_sub v sub) (c_sub c' sub)
  end
with h_sub h (sub : nat * val) :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op x k c => 
      CasesU (h_sub h sub) op x k (c_sub c (sub_shift sub 2))
  end.

End Sub.

(* ==================== Complete substitution ==================== *)

Definition v_subs (v:val) (v_s:val) i :=
  Sub.v_negshift (Sub.v_sub v (i, (Sub.v_shift v_s 1 i))) 1 i.

Definition c_subs (c:comp) (v_s:val) i :=
  Sub.c_negshift (Sub.c_sub c (i, (Sub.v_shift v_s 1 i))) 1 i.

Definition h_subs (h:hcases) (v_s:val) i :=
  Sub.h_negshift (Sub.h_sub h (i, (Sub.v_shift v_s 1 i))) 1 i.

Definition v_subs_out (v:val) (v_s:val) := v_subs v v_s 0.

Definition c_subs_out (c:comp) (v_s:val) := c_subs c v_s 0.

Definition h_subs_out (h:hcases) (v_s:val) := h_subs h v_s 0.

Definition c_subs2_out (c:comp) v1 v0 :=
  (* 1 -> v1, 0 -> v0 *)
  c_subs_out (c_subs_out c (Sub.v_shift v0 1 0)) v1.