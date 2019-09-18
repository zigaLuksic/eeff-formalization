Require Export Bool ZArith Int String.

(* Variable Type Definitions *)
Definition var_name := string.
Definition var_n := nat.
Definition var_id := prod var_name var_n.

Definition op_id := string.

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
| VAnnot : val -> vtype -> val

with comp : Type :=
| Ret : val -> comp
| ΠMatch : val -> var_name * var_name -> comp -> comp (* x~1 y~0 *)
| ΣMatch : val -> var_name -> comp -> var_name -> comp -> comp
| App : val -> val -> comp
| Op : op_id -> val -> var_name -> comp -> comp (* x~1 k~0 *)
| LetRec : var_name -> var_name -> vtype -> comp -> comp -> comp (* f~0 x~1 *)
| DoBind : var_name -> comp -> comp -> comp
| Handle : val -> comp -> comp
| CAnnot : comp -> ctype -> comp

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

with tmpl_ctx : Type :=
| TctxØ : tmpl_ctx
| TctxU : tmpl_ctx -> vtype -> tmpl_ctx

with tmpl : Type :=
| TApp : var_name -> val -> tmpl
| TΠmatch : val -> var_name -> var_name -> tmpl -> tmpl
| TΣmatch : val -> var_name -> tmpl -> var_name -> tmpl -> tmpl
| TOp : op_id -> val -> var_name -> tmpl -> tmpl

with eqs : Type := 
| EqsØ : eqs
| EqsU : eqs -> ctx -> tmpl_ctx -> tmpl -> tmpl -> eqs
.

(* ID Functions *)
Definition id_eq (id1 : var_id) (id2 : var_id) : bool :=
  let (id_name1, id_n1) := id1 in
  let (id_name2, id_n2) := id2 in
  Nat.eqb id_n1 id_n2.

Definition id_match_ctx (id : var_id) : bool:=
  let (id_name, id_n) := id in
  Nat.eqb id_n 0.

Definition id_n_reduce (id : var_id) : var_id :=
  let (id_name, id_n) := id in (id_name, id_n - 1).  

Notation "x == y" := (string_dec x y) (at level 75, no associativity).

(* Auxiliary Function Definitions *)
Fixpoint get_vtype (Γ : ctx) (id : var_id) : option vtype :=
  match Γ with
  | CtxØ => None
  | CtxU Γ' α =>
      if id_match_ctx id then Some α
      else get_vtype Γ' (id_n_reduce id)
  end.

Fixpoint get_op_type (Σ : sig) (op : op_id) : option (vtype * vtype) :=
  match Σ with
  | SigØ => None
  | SigU Σ' op' α β =>
      if op == op' then Some (α, β)
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
| VAnnot v' α => v_no_var_j v' j
end
with c_no_var_j (c:comp) (j:nat) :=
match c with
| Ret v => v_no_var_j v j
| ΠMatch v (x, y) c => c_no_var_j c (j+2)
| ΣMatch v xl cl xr cr => (c_no_var_j cl (j+1)) /\ (c_no_var_j cr (j+1))
| App v1 v2 => (v_no_var_j v1 j) /\ (v_no_var_j v2 j)
| Op op v_arg y c => (v_no_var_j v_arg j) /\ (c_no_var_j c (j+1))
| LetRec f x f_ty c1 c2 => (c_no_var_j c1 (j+2)) /\ (c_no_var_j c2 (j+1))
| DoBind x c1 c2 => (c_no_var_j c1 j) /\ (c_no_var_j c2 (j+1))
| Handle v c' => (v_no_var_j v j) /\ (c_no_var_j c' j)
| CAnnot c' C => (c_no_var_j c' j)
end
with h_no_var_j (h:hcases) (j:nat) :=
match h with
| CasesØ => True
| CasesU h op x k c => (h_no_var_j h j) /\ (c_no_var_j c (j+2))
end.