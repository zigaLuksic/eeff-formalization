(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Require Export syntax.

(* ==================== Shifts and Subs ==================== *)

Fixpoint v_shift v d cut :=
  match v with
  | Var n => if cut <=? n then Var (d + n) else Var n
  | Unit => Unit
  | Int n => Int n
  | Left v' => Left (v_shift v' d cut)
  | Right v' => Right (v_shift v' d cut)
  | Pair v1 v2 =>
      Pair (v_shift v1 d cut) (v_shift v2 d cut)
  | Nil => Nil
  | Cons v vs => 
      Cons (v_shift v d cut) (v_shift vs d cut)
  | Fun c =>
      Fun (c_shift c d (1+cut))
  | Handler c_ret h =>
      Handler (c_shift c_ret d (1+cut)) (h_shift h d cut)
  end

with c_shift c d cut :=
  match c with
  | Ret v => Ret (v_shift v d cut)
  | Absurd v => Absurd (v_shift v d cut)
  | ProdMatch v c => 
      ProdMatch (v_shift v d cut) (c_shift c d (2+cut))
  | SumMatch v c1 c2 =>
      SumMatch (v_shift v d cut) 
        (c_shift c1 d (1+cut)) (c_shift c2 d (1+cut))
  | ListMatch v c1 c2 =>
      ListMatch (v_shift v d cut) (c_shift c1 d cut) (c_shift c2 d (2+cut))
  | App v1 v2 => 
      App (v_shift v1 d cut) (v_shift v2 d cut)
  | Op op v c => 
      Op op (v_shift v d cut) (c_shift c d (1+cut))
  | LetRec c1 c2 => 
      LetRec (c_shift c1 d (2+cut)) (c_shift c2 d (1+cut))
  | Do c1 c2 => 
      Do (c_shift c1 d cut) (c_shift c2 d (1+cut))
  | Handle v c' => 
      Handle (v_shift v d cut) (c_shift c' d cut)
  end

with h_shift h d cut :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op c => 
      CasesU (h_shift h d cut) op (c_shift c d (2+cut))
  end.


Fixpoint v_negshift v d cut :=
  match v with
  | Var n => if Nat.leb cut n then Var (n - d) else Var n   
  | Unit => Unit
  | Int n => Int n
  | Left v' => Left (v_negshift v' d cut)
  | Right v' => Right (v_negshift v' d cut)
  | Pair v1 v2 => 
      Pair (v_negshift v1 d cut) (v_negshift v2 d cut)
  | Nil => Nil
  | Cons v vs =>
      Cons (v_negshift v d cut) (v_negshift vs d cut)
  | Fun c =>
      Fun (c_negshift c d (1+cut))
  | Handler c_ret h =>
      Handler (c_negshift c_ret d (1+cut)) (h_negshift h d cut)
  end

with c_negshift c d cut :=
  match c with
  | Ret v => Ret (v_negshift v d cut)
  | Absurd v => Absurd (v_negshift v d cut)
  | ProdMatch v c => 
      ProdMatch (v_negshift v d cut) (c_negshift c d (2+cut))
  | SumMatch v c1 c2 =>
      SumMatch (v_negshift v d cut)
        (c_negshift c1 d (1+cut)) (c_negshift c2 d (1+cut))
  | ListMatch v c1 c2 =>
      ListMatch (v_negshift v d cut)
        (c_negshift c1 d cut) (c_negshift c2 d (2+cut))
  | App v1 v2 => 
      App (v_negshift v1 d cut) (v_negshift v2 d cut)
  | Op op v c => 
      Op op (v_negshift v d cut) (c_negshift c d (1+cut))
  | LetRec c1 c2 =>
      LetRec (c_negshift c1 d (2+cut)) (c_negshift c2 d (1+cut))
  | Do c1 c2 => 
      Do (c_negshift c1 d cut) (c_negshift c2 d (1+cut))
  | Handle v c' => 
      Handle (v_negshift v d cut) (c_negshift c' d cut)
  end

with h_negshift h d cut :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op c => CasesU (h_negshift h d cut) op (c_negshift c d (2+cut))
  end.


Definition sub_shift (sub : nat * val) d :=
  let (db_i, v_s) := sub in (d + db_i, v_shift v_s d 0).


Fixpoint v_sub v (sub : nat * val) :=
let (db_i, v_s) := sub in
  match v with
  | Var n => if n =? db_i then v_s else Var n 
  | Unit => Unit
  | Int n => Int n
  | Left v' => Left (v_sub v' sub)
  | Right v' => Right (v_sub v' sub)
  | Pair v1 v2 => 
      Pair (v_sub v1 sub) (v_sub v2 sub)
  | Nil => Nil
  | Cons v vs => 
      Cons (v_sub v sub) (v_sub vs sub)
  | Fun c => 
      Fun (c_sub c (sub_shift sub 1))
  | Handler c_ret h =>
      Handler (c_sub c_ret (sub_shift sub 1)) (h_sub h sub)
  end

with c_sub c (sub : nat * val) :=
  match c with
  | Ret v => Ret (v_sub v sub)
  | Absurd v => Absurd (v_sub v sub)
  | ProdMatch v c => 
      ProdMatch (v_sub v sub) (c_sub c (sub_shift sub 2))
  | SumMatch v c1 c2 =>
      SumMatch (v_sub v sub)
        (c_sub c1 (sub_shift sub 1)) (c_sub c2 (sub_shift sub 1))
  | ListMatch v c1 c2 =>
      ListMatch (v_sub v sub)
        (c_sub c1 sub) (c_sub c2 (sub_shift sub 2))
  | App v1 v2 => 
      App (v_sub v1 sub) (v_sub v2 sub)
  | Op op v c => 
      Op op (v_sub v sub) (c_sub c (sub_shift sub 1))
  | LetRec c1 c2 =>
      LetRec (c_sub c1 (sub_shift sub 2)) (c_sub c2 (sub_shift sub 1))
  | Do c1 c2 => 
      Do (c_sub c1 sub) (c_sub c2 (sub_shift sub 1))
  | Handle v c' => 
      Handle (v_sub v sub) (c_sub c' sub)
  end

with h_sub h (sub : nat * val) :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op c => 
      CasesU (h_sub h sub) op (c_sub c (sub_shift sub 2))
  end.

(* ==================== Complete Substitution ==================== *)

Definition v_subs v i vs :=
  v_negshift (v_sub v (i, (v_shift vs 1 i))) 1 i.

Definition c_subs c i vs :=
  c_negshift (c_sub c (i, (v_shift vs 1 i))) 1 i.

Definition h_subs h i vs :=
  h_negshift (h_sub h (i, (v_shift vs 1 i))) 1 i.

Definition v_subs_out v vs := v_subs v 0 vs.

Definition c_subs_out c vs := c_subs c 0 vs.

Definition h_subs_out h vs := h_subs h 0 vs.

Definition c_subs2_out c v1 v0 := (* 1 -> v1, 0 -> v0 *)
  c_subs_out (c_subs_out c (v_shift v0 1 0)) v1.


(* ==================== Instantiation ==================== *)

Fixpoint inst_shift I d cut :=
  match I with
  | InstØ => InstØ
  | InstU I' v => InstU (inst_shift I' d cut) (v_shift v d cut)
  end.


Fixpoint inst_negshift I d cut :=
  match I with
  | InstØ => InstØ
  | InstU I' v => InstU (inst_negshift I' d cut) (v_negshift v d cut)
  end.


Fixpoint inst_sub I sub :=
  match I with
  | InstØ => InstØ
  | InstU I' v => InstU (inst_sub I' sub) (v_sub v sub)
  end.


Fixpoint inst_subs I i vs :=
  match I with
  | InstØ => InstØ
  | InstU I' v => InstU (inst_subs I' i vs) (v_subs v i vs)
  end.


Fixpoint v_inst v I:=
  match v with
  | Var n => 
      match get_inst_val I n with
      | Some v' => v'
      | None => Unit (* This is the naughty branch! *)
      end
  | Unit => Unit
  | Int n => Int n
  | Left v' => Left (v_inst v' I)
  | Right v' => Right (v_inst v' I)
  | Pair v1 v2 => 
      Pair (v_inst v1 I) (v_inst v2 I)
  | Nil => Nil
  | Cons v vs => 
      Cons (v_inst v I) (v_inst vs I)
  | Fun c => 
      Fun (c_inst c (InstU (inst_shift I 1 0) (Var 0)))
  | Handler c_ret h =>
      Handler 
        (c_inst c_ret (InstU (inst_shift I 1 0) (Var 0))) 
        (h_inst h I)
  end

with c_inst c I :=
  match c with
  | Ret v => Ret (v_inst v I)
  | Absurd v => Absurd (v_inst v I)
  | ProdMatch v c => 
      ProdMatch (v_inst v I)
        (c_inst c (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
  | SumMatch v c1 c2 =>
      SumMatch (v_inst v I)
        (c_inst c1 (InstU (inst_shift I 1 0) (Var 0))) 
        (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
  | ListMatch v c1 c2 =>
      ListMatch (v_inst v I)
        (c_inst c1 I) 
        (c_inst c2 
          (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
  | App v1 v2 => 
      App (v_inst v1 I) (v_inst v2 I)
  | Op op v c => 
      Op op (v_inst v I) 
        (c_inst c (InstU (inst_shift I 1 0) (Var 0)))
  | LetRec c1 c2 =>
      LetRec
        (c_inst c1 
          (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0))) 
        (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
  | Do c1 c2 => 
      Do (c_inst c1 I) 
        (c_inst c2 (InstU (inst_shift I 1 0) (Var 0)))
  | Handle v c' => 
      Handle (v_inst v I) (c_inst c' I)
  end

with h_inst h I :=
  match h with
  | CasesØ => CasesØ
  | CasesU h op c => 
      CasesU (h_inst h I) op
        (c_inst c (InstU (InstU (inst_shift I 2 0) (Var 1)) (Var 0)))
  end.


Set Implicit Arguments.
(* Useful for stating certain lemmas *)
Function f_opt (A B:Type) (opt : option A) (f : A -> option B) := 
  match opt with
  | Some x => f x
  | None => None
  end.
