Require Export Bool ZArith Int String.

Definition var_id := string.
Definition op_id := string.
Definition int := Z.t.
Definition eq_id := string_dec.
Notation "x == y" := (eq_id x y) (at level 75, no associativity).
Check "" == "".

Inductive val : Type :=
| Var : string -> val
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
| ΠMatch : val -> var_id * var_id -> comp -> comp
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
| SigU : op_id -> vtype -> vtype -> sig -> sig
with ctx : Type :=
| CtxØ : ctx
| CtxU : var_id -> vtype -> ctx -> ctx
with tmpl_ctx : Type :=
| TctxØ : tmpl_ctx
| TctxU : var_id -> vtype -> tmpl_ctx -> tmpl_ctx
with tmpl : Type :=
| TApp : var_id -> val -> tmpl
| TΠmatch : val -> var_id -> var_id -> tmpl -> tmpl
| TΣmatch : val -> var_id -> tmpl -> var_id -> tmpl -> tmpl
| TOp : op_id -> val -> var_id -> tmpl -> tmpl
with eqs : Type :=
| EqsØ : eqs
| EqsU : ctx -> tmpl_ctx -> tmpl -> tmpl -> eqs
.

Fixpoint get_vtype (Γ : ctx) (id : var_id) : option vtype :=
  match Γ with
  | CtxØ => None
  | CtxU id' α Γ' =>
      if id == id' then Some α
      else get_vtype Γ' id
  end.

Fixpoint get_op_type (Σ : sig) (op : op_id) : option (vtype * vtype) :=
  match Σ with
  | SigØ => None
  | SigU op' α β Σ' =>
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

(* NOT CAPTURE AVOIDING!!! *)
Fixpoint vsubst (σ : var_id * val) (v : val) :=
  (* v [id |-> sv] *)
  let (s_id, s_v) := σ in
  match v with
  | Var id => if id == s_id then s_v else v
  | Unit => v
  | Int n => v
  | Inl v' => Inl (vsubst σ v')
  | Inr v' => Inr (vsubst σ v')
  | Pair v1 v2 => Pair (vsubst σ v1) (vsubst σ v2)
  | Fun id c => if id == s_id then v else Fun id (csubst σ c) 
  | Handler ret_id c h => 
      if ret_id == s_id then Handler ret_id c (hsubst σ h)
      else Handler ret_id (csubst σ c) (hsubst σ h)
  | VAnnot v ty =>  VAnnot (vsubst σ v) ty
  end
with csubst (σ : var_id * val) (c : comp) :=
  (* c [id |-> sv] *)
  let (s_id, s_v) := σ in
  match c with
  | Ret v => Ret (vsubst σ v)
  | ΠMatch v (id1, id2) c' => 
      if id1 == s_id then c
      else if id2 == s_id then c
      else ΠMatch (vsubst σ v) (id1, id2) (csubst σ c')
  | ΣMatch v idl cl idr cr =>
      let cl' := if idl == s_id then cl else csubst σ cl in
      let cr' := if idr == s_id then cr else csubst σ cr in
      ΣMatch (vsubst σ v) idl cl' idr cr'
  | App vf vx => App (vsubst σ vf) (vsubst σ vx)
  | Op op_id v_arg id k =>
      let k' := if id == s_id then k else csubst σ k in
      Op op_id (vsubst σ v_arg) id k'
  | LetRec f_id x_id c1 c2 =>
      if f_id == s_id then c
      else if x_id == s_id then c
      else LetRec f_id x_id (csubst σ c1) (csubst σ c2)
  | DoBind x_id c1 c2 =>
      if x_id == s_id then DoBind x_id (csubst σ c1) c2
      else DoBind x_id (csubst σ c1) (csubst σ c2)
  | Handle v c' => Handle (vsubst σ v) (csubst σ c')
  | CAnnot c ty => CAnnot (csubst σ c) ty
  end
with hsubst (σ : var_id * val) (h : hcases) :=
  (* c [id |-> sv] *)
  let (s_id, s_v) := σ in
  match h with
  | CasesØ => h
  | CasesU h' op_id x_id k_id c_op =>
      let c_op' := 
        if x_id == s_id then c_op
        else if k_id == s_id then c_op
      else csubst σ c_op in
      CasesU (hsubst σ h') op_id x_id k_id c_op'
  end.
