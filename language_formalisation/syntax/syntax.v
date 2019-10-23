Require Export Bool ZArith Int String.

(* Variable Type Definitions *)
Definition var_name := string.
Definition var_n := nat.
Definition var_id := prod var_name var_n.

Definition op_id := string.
Notation "x == y" := (string_dec x y) (at level 75, no associativity).

Definition int := Z.t.

(* Syntax Definitions *)
Inductive val : Type :=
| Var : var_id -> val
| Unit : val
| Int : Z.t -> val
| Inl : val -> val
| Inr : val -> val
| Pair : val -> val -> val
| Fun : var_name -> comp -> val
| Handler : var_name -> comp -> hcases -> val

with comp : Type :=
| Ret : val -> comp
| ΠMatch : val -> var_name * var_name -> comp -> comp (* x~1 y~0 *)
| ΣMatch : val -> var_name -> comp -> var_name -> comp -> comp
| App : val -> val -> comp
| Op : op_id -> val -> var_name -> comp -> comp (* x~1 k~0 *)
| LetRec : var_name -> var_name -> comp -> comp -> comp (* f~0 x~1 *)
| DoBind : var_name -> comp -> comp -> comp
| Handle : val -> comp -> comp

with hcases : Type :=
| CasesØ : hcases
| CasesU : hcases -> op_id -> var_name -> var_name -> comp -> hcases

with vtype : Type :=
| TyUnit : vtype
| TyInt : vtype
| TyØ : vtype
| TyΣ : vtype -> vtype -> vtype
| TyΠ : vtype -> vtype -> vtype
| TyFun : vtype -> ctype -> vtype
| TyHandler : ctype -> ctype -> vtype

with ctype : Type :=
| CTy : vtype -> sig -> eqs -> ctype

with sig : Type :=
| SigØ : sig
| SigU : sig -> op_id -> vtype -> vtype -> sig

with ctx : Type :=
| CtxØ : ctx
| CtxU : ctx -> vtype -> ctx

with tctx : Type :=
| TCtxØ : tctx
| TCtxU : tctx -> vtype -> tctx

with tmpl : Type :=
| TApp : var_id -> val -> tmpl
| TΠMatch : val -> var_name -> var_name -> tmpl -> tmpl
| TΣMatch : val -> var_name -> tmpl -> var_name -> tmpl -> tmpl
| TOp : op_id -> val -> var_name -> tmpl -> tmpl

with eqs : Type := 
| EqsØ : eqs
| EqsU : eqs -> ctx -> tctx -> tmpl -> tmpl -> eqs
.


(* Auxiliary Function Definitions *)

Fixpoint get_vtype (Γ : ctx) (i:nat) : option vtype :=
  match Γ, i with
  | CtxØ , _=> None
  | CtxU Γ' A, 0 => Some A
  | CtxU Γ' A, S i' =>  get_vtype Γ' i'
  end.

Fixpoint get_ttype (Z : tctx) (i:nat) : option vtype :=
  match Z, i with
  | TCtxØ , _=> None
  | TCtxU Z' A, 0 => Some A
  | TCtxU Z' A, S i' =>  get_ttype Z' i'
  end.


Fixpoint get_op_type (Σ : sig) (op : op_id) : option (vtype * vtype) :=
  match Σ with
  | SigØ => None
  | SigU Σ' op' A B =>
      if op == op' then Some (A, B)
      else get_op_type Σ' op
  end.


Fixpoint find_op_case (h : hcases) (op : op_id) 
  : option (var_name * var_name * comp) :=
  match h with
  | CasesØ => None
  | CasesU h_others op' x_op k_op c_op =>
      if op == op' then Some (x_op, k_op, c_op)
      else find_op_case h_others op
  end.


Fixpoint eqs_contain_eq E Γ Z T1 T2 :=
  match E with
  | EqsØ => False
  | EqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ eqs_contain_eq E' Γ Z T1 T2
  end.


Fixpoint v_no_var_j (v:val) (j:nat) :=
match v with
| Var (name, num) => not (j = num)
| Unit => True
| Int j => True
| Inl v' => v_no_var_j v' j
| Inr v' => v_no_var_j v' j
| Pair v1 v2 => (v_no_var_j v1 j) /\ (v_no_var_j v2 j)
| Fun x c => c_no_var_j c (j+1)
| Handler x c_ret h => (c_no_var_j c_ret (j+1)) /\ (h_no_var_j h j)
end
with c_no_var_j (c:comp) (j:nat) :=
match c with
| Ret v => v_no_var_j v j
| ΠMatch v (x, y) c => 
    (v_no_var_j v j) /\ c_no_var_j c (j+2)
| ΣMatch v xl cl xr cr =>
    (v_no_var_j v j) /\ (c_no_var_j cl (j+1)) /\ (c_no_var_j cr (j+1))
| App v1 v2 => (v_no_var_j v1 j) /\ (v_no_var_j v2 j)
| Op op v_arg y c => (v_no_var_j v_arg j) /\ (c_no_var_j c (j+1))
| LetRec f x c1 c2 => (c_no_var_j c1 (j+2)) /\ (c_no_var_j c2 (j+1))
| DoBind x c1 c2 => (c_no_var_j c1 j) /\ (c_no_var_j c2 (j+1))
| Handle v c' => (v_no_var_j v j) /\ (c_no_var_j c' j)
end
with h_no_var_j (h:hcases) (j:nat) :=
match h with
| CasesØ => True
| CasesU h op x k c => (h_no_var_j h j) /\ (c_no_var_j c (j+2))
end.


Fixpoint v_switch_vars (v:val) (i:nat) (j:nat) :=
match v with
| Var (name, num) =>
    if num =? i then Var (name, j)
    else if num =? j then Var (name, i)
    else Var (name, num)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_switch_vars v' i j)
| Inr v' => Inr (v_switch_vars v' i j)
| Pair v1 v2 => Pair (v_switch_vars v1 i j) (v_switch_vars v2 i j)
| Fun x c => Fun x (c_switch_vars c (i+1) (j+1))
| Handler x c_ret h =>
    Handler x (c_switch_vars c_ret (i+1) (j+1)) (h_switch_vars h i j)
end
with c_switch_vars (c:comp) (i:nat) (j:nat) :=
match c with
| Ret v => Ret (v_switch_vars v i j)
| ΠMatch v (x, y) c =>
    ΠMatch (v_switch_vars v i j) (x,y) (c_switch_vars c (i+2) (j+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_switch_vars v i j) xl (c_switch_vars cl (i+1) (j+1)) 
      xr (c_switch_vars cr (i+1) (j+1))
| App v1 v2 => App (v_switch_vars v1 i j) (v_switch_vars v2 i j)
| Op op v_arg y c => 
    Op op (v_switch_vars v_arg i j) y (c_switch_vars c (i+1) (j+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_switch_vars c1 (i+2) (j+2)) (c_switch_vars c2 (i+1) (j+1))
| DoBind x c1 c2 => 
    DoBind x (c_switch_vars c1 i j) (c_switch_vars c2 (i+1) (j+1))
| Handle v c' => Handle (v_switch_vars v i j) (c_switch_vars c' i j)
end
with h_switch_vars (h:hcases) (i:nat) (j:nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c =>
    CasesU (h_switch_vars h i j) op x k (c_switch_vars c (i+2) (j+2))
end.


Fixpoint ctx_change_var (Γ:ctx) (i:nat) (A:vtype) :=
  match Γ, i with
  | CtxØ, _ => CtxØ
  | CtxU Γ' A', 0 => CtxU Γ' A
  | CtxU Γ' A', S i' => CtxU (ctx_change_var Γ' i' A) A'
  end.


Definition ctx_switch_vars (Γ : ctx) (i:nat) (j:nat) (A:vtype) (B:vtype)
  (proof_i : get_vtype Γ i = Some A) (proof_j: get_vtype Γ j = Some B) : ctx
:=
  ctx_change_var (ctx_change_var Γ i B) j A.


Fixpoint ctx_remove_var (Γ:ctx) (i:nat) :=
  match Γ, i with
  | CtxØ, _ => CtxØ
  | CtxU Γ' A', 0 => Γ'
  | CtxU Γ' A', S i' => CtxU (ctx_remove_var Γ' i') A'
  end.


Fixpoint ctx_insert_var (Γ:ctx) A (i:nat) :=
  match Γ, i with
  | Γ', 0 => CtxU Γ' A
  | CtxØ, _ => CtxØ
  | CtxU Γ' A', S i' => CtxU (ctx_insert_var Γ' A i') A'
  end.
