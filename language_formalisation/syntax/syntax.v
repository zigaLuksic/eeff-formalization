Require Export Bool ZArith Int String List.

Import ListNotations.

Definition var_id :=prod string nat.
Definition id_correct (id : var_id) :=
  let (idname, idnum) := id in
  Nat.eqb idnum 0.
Definition id_reduce (id : var_id) :=
  let (idname, idnum) := id in
  (idname, idnum - 1).
Definition id_shift (id : var_id) d c :=
  let (idname, idnum) := id in
  if Nat.ltb idnum c then id else (idname, idnum + d).
Definition id_same (id1 : var_id) (id2 : var_id) :=
  let (idname1, idnum1) := id1 in
  let (idname2, idnum2) := id2 in
  Nat.eqb idnum1 idnum2.
Definition int := Z.t.
Definition op_id := string.
Definition eq_op_id := string_dec.
Notation "x == y" := (eq_op_id x y) (at level 75, no associativity).
Check "" == "".

Inductive val : Type :=
| Var : var_id -> val
| Unit : val
| Int : Z.t -> val
| Inl : val -> val
| Inr : val -> val
| Pair : val -> val -> val
| Fun : var_id -> comp -> val
| Handler : var_id -> comp -> hcases -> val
| VAnnot : val -> vtype -> val

with comp : Type :=
| Ret : val -> comp
| ΠMatch : val -> comp -> comp
| ΣMatch : val -> var_id -> comp -> var_id -> comp -> comp
| App : val -> val -> comp
| Op : op_id -> val -> var_id -> comp -> comp
| LetRec : var_id -> var_id -> comp -> comp -> comp
| DoBind : var_id -> comp -> comp -> comp
| Handle : val -> comp -> comp
| CAnnot : comp -> ctype -> comp

with hcases : Type :=
| CasesØ : hcases
| CasesU : hcases -> op_id -> var_id -> var_id -> comp -> hcases

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
| TApp : var_id -> val -> tmpl
| TΠmatch : val -> var_id -> var_id -> tmpl -> tmpl
| TΣmatch : val -> var_id -> tmpl -> var_id -> tmpl -> tmpl
| TOp : op_id -> val -> var_id -> tmpl -> tmpl

with eqs : Type := 
| EqsØ : eqs
| EqsU : eqs -> ctx -> tmpl_ctx -> tmpl -> tmpl -> eqs
.

Fixpoint get_vtype (Γ : ctx) (id : var_id) : option vtype :=
  match Γ with
  | CtxØ => None
  | CtxU Γ' α =>
      if id_correct id then Some α
      else get_vtype Γ' (id_reduce id)
  end.

Fixpoint get_op_type (Σ : sig) (op : op_id) : option (vtype * vtype) :=
  match Σ with
  | SigØ => None
  | SigU Σ' op' α β =>
      if op == op' then Some (α, β)
      else get_op_type Σ' op
  end.

Fixpoint find_op_case (h : hcases) (op : op_id) 
  : option (var_id * var_id * comp) :=
  match h with
  | CasesØ => None
  | CasesU h_others op' x_op k_op c_op =>
      if op == op' then Some (x_op, k_op, c_op)
      else find_op_case h_others op
  end.

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
