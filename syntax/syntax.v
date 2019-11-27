Require Export Bool ZArith String.

(* ==================== Variable Type Definitions ==================== *)

Definition var_name := string.
Definition var_n := nat.
Definition var_id := prod var_name var_n.

Definition op_id := string.
Notation "x == y" := (string_dec x y) (at level 75, no associativity).

Definition int := Z.t.

(* ==================== Syntax Definitions ==================== *)

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
| Absurd : val -> comp
| ΠMatch : val -> var_name -> var_name -> comp -> comp (* x~1 y~0 *)
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
| TAbsurd : val -> tmpl
| TΠMatch : val -> var_name -> var_name -> tmpl -> tmpl
| TΣMatch : val -> var_name -> tmpl -> var_name -> tmpl -> tmpl
| TOp : op_id -> val -> var_name -> tmpl -> tmpl

with eqs : Type := 
| EqsØ : eqs
| EqsU : eqs -> ctx -> tctx -> tmpl -> tmpl -> eqs
.

(* ==================== Getters and Ctx Modification ==================== *)

Fixpoint get_vtype Γ i :=
  match Γ, i with
  | CtxØ , _=> None
  | CtxU Γ' A, 0 => Some A
  | CtxU Γ' A, S i' =>  get_vtype Γ' i'
  end.


Fixpoint get_ttype Z i :=
  match Z, i with
  | TCtxØ , _=> None
  | TCtxU Z' A, 0 => Some A
  | TCtxU Z' A, S i' =>  get_ttype Z' i'
  end.


Fixpoint get_op_type Σ op :=
  match Σ with
  | SigØ => None
  | SigU Σ' op' A B =>
      if op == op' then Some (A, B) else get_op_type Σ' op
  end.


Fixpoint find_case h op : option (var_name * var_name * comp) :=
  match h with
  | CasesØ => None
  | CasesU h' op' x_op k_op c_op =>
      if op == op' then Some (x_op, k_op, c_op) else find_case h' op
  end.


Fixpoint has_eq E Γ Z T1 T2 :=
  match E with
  | EqsØ => False
  | EqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ has_eq E' Γ Z T1 T2
  end.


Fixpoint ctx_remove (Γ:ctx) (i:nat) :=
  match i, Γ with
  | _, CtxØ => CtxØ
  | 0, CtxU Γ' A' => Γ'
  | S i', CtxU Γ' A' => CtxU (ctx_remove Γ' i') A'
  end.


Fixpoint ctx_insert (Γ:ctx) A (i:nat) :=
  match i, Γ with
  | 0, Γ' => CtxU Γ' A
  | _, CtxØ => CtxØ
  | S i', CtxU Γ' A' => CtxU (ctx_insert Γ' A i') A'
  end.


Fixpoint ctx_len Γ :=
  match Γ with
  | CtxØ => 0
  | CtxU Γ _ => 1 + (ctx_len Γ)
  end.


Fixpoint tctx_len Z :=
  match Z with
  | TCtxØ => 0
  | TCtxU Z _ => 1 + (tctx_len Z)
  end.


Fixpoint join_ctxs Γ1 Γ2 :=
  match Γ2 with
  | CtxØ => Γ1
  | CtxU Γ2' A => CtxU (join_ctxs Γ1 Γ2') A
  end.


Fixpoint join_ctx_tctx Γ Z D :=
  match Z with
  | TCtxØ => Γ
  | TCtxU Z A => CtxU (join_ctx_tctx Γ Z D) (TyFun A D)
  end.

(* ==================== Term Properties ==================== *)

Fixpoint v_no_var (v:val) (j:nat) :=
  match v with
  | Var (name, num) => not (j = num)
  | Unit => True
  | Int j => True
  | Inl v' => v_no_var v' j
  | Inr v' => v_no_var v' j
  | Pair v1 v2 => (v_no_var v1 j) /\ (v_no_var v2 j)
  | Fun x c => c_no_var c (1+j)
  | Handler x c_ret h => (c_no_var c_ret (1+j)) /\ (h_no_var h j)
  end

with c_no_var (c:comp) (j:nat) :=
  match c with
  | Ret v => v_no_var v j
  | Absurd v => v_no_var v j 
  | ΠMatch v x y c => (v_no_var v j) /\ c_no_var c (2+j)
  | ΣMatch v xl cl xr cr =>
      (v_no_var v j) /\ (c_no_var cl (1+j)) /\ (c_no_var cr (1+j))
  | App v1 v2 => (v_no_var v1 j) /\ (v_no_var v2 j)
  | Op op v_arg y c => (v_no_var v_arg j) /\ (c_no_var c (1+j))
  | LetRec f x c1 c2 => (c_no_var c1 (2+j)) /\ (c_no_var c2 (1+j))
  | DoBind x c1 c2 => (c_no_var c1 j) /\ (c_no_var c2 (1+j))
  | Handle v c' => (v_no_var v j) /\ (c_no_var c' j)
  end

with h_no_var (h:hcases) (j:nat) :=
  match h with
  | CasesØ => True
  | CasesU h op x k c => (h_no_var h j) /\ (c_no_var c (2+j))
  end.


Fixpoint v_under_var (v:val) (j:nat) :=
  match v with
  | Var (name, num) => num < j
  | Unit => True
  | Int j => True
  | Inl v' => v_under_var v' j
  | Inr v' => v_under_var v' j
  | Pair v1 v2 => (v_under_var v1 j) /\ (v_under_var v2 j)
  | Fun x c => c_under_var c (1+j)
  | Handler x c_ret h => (c_under_var c_ret (1+j)) /\ (h_under_var h j)
  end

with c_under_var (c:comp) (j:nat) :=
  match c with
  | Ret v => v_under_var v j
  | Absurd v => v_under_var v j 
  | ΠMatch v x y c => (v_under_var v j) /\ c_under_var c (2+j)
  | ΣMatch v xl cl xr cr =>
      (v_under_var v j) /\ (c_under_var cl (1+j)) /\ (c_under_var cr (1+j))
  | App v1 v2 => (v_under_var v1 j) /\ (v_under_var v2 j)
  | Op op v_arg y c => (v_under_var v_arg j) /\ (c_under_var c (1+j))
  | LetRec f x c1 c2 => (c_under_var c1 (2+j)) /\ (c_under_var c2 (1+j))
  | DoBind x c1 c2 => (c_under_var c1 j) /\ (c_under_var c2 (1+j))
  | Handle v c' => (v_under_var v j) /\ (c_under_var c' j)
  end

with h_under_var h j :=
  match h with
  | CasesØ => True
  | CasesU h op x k c => (h_under_var h j) /\ (c_under_var c (2+j))
  end.


Fixpoint t_under_var T j :=
  match T with
  | TApp (name, num) v => v_under_var v j
  | TAbsurd v => v_under_var v j
  | TΠMatch v x y T => v_under_var v j /\ t_under_var T (2+j)
  | TΣMatch v xl Tl xr Tr =>
      (v_under_var v j) /\ (t_under_var Tl (1+j)) 
      /\ (t_under_var Tr (1+j))
  | TOp op v_arg y T => (v_under_var v_arg j) /\ (t_under_var T (1+j))
  end.


Fixpoint t_under_tvar T j :=
  match T with
  | TApp (name, num) v => num < j
  | TAbsurd v => True
  | TΠMatch v x y T => t_under_tvar T j
  | TΣMatch v xl Tl xr Tr => 
      (t_under_tvar Tl j) /\ (t_under_tvar Tr j)
  | TOp op v_arg y T => (t_under_tvar T j)
  end.
