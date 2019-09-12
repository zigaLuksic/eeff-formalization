Require Import Bool ZArith Int String.

Definition var_id := string.
Definition op_id := string.
Definition int := Z.t.
Definition eq_id := string_dec.

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
| PMatch : val -> var_id * var_id -> comp -> comp
| SMatch : val -> var_id -> comp -> var_id -> comp -> comp
| App : val -> val -> comp
| Op : op_id -> val -> var_id -> comp -> comp
| LetRec : var_id -> var_id -> comp -> comp -> comp
| DoBind : var_id -> comp -> comp -> comp
| Handle : val -> comp -> comp
| CAnnot : comp -> ctype -> comp
with hcases : Type :=
| NoCases : hcases
| OpCases : hcases -> op_id -> var_id -> var_id -> comp -> hcases
with vtype : Type :=
| TyUnit : vtype
| TyInt : vtype
| TyEmpty : vtype
| TySum : vtype -> vtype -> vtype
| TyProd : vtype -> vtype -> vtype
| TyFun : vtype -> ctype -> vtype
| TyHandler : ctype -> ctype -> vtype
with ctype : Type :=
| CTy : vtype -> sig -> eqs -> ctype
with sig : Type :=
| SigNil : sig
| SigCons : op_id -> vtype -> vtype -> sig -> sig
with ctx : Type :=
| CtxNil : ctx
| CtxCons : var_id -> vtype -> ctx -> ctx
with tmpl_ctx : Type :=
| TctxNil : tmpl_ctx
| TctxCons : var_id -> vtype -> tmpl_ctx -> tmpl_ctx
with tmpl : Type :=
| Tapp : var_id -> val -> tmpl
| Tpmatch : val -> var_id -> var_id -> tmpl -> tmpl
| Tsmatch : val -> var_id -> tmpl -> var_id -> tmpl -> tmpl
| Top : op_id -> val -> var_id -> tmpl -> tmpl
with eqs : Type :=
| EqsNil : eqs
| EqsCons : ctx -> tmpl_ctx -> tmpl -> tmpl -> eqs
.

Fixpoint get_vtype (ctx : ctx) (id : var_id) : option vtype :=
  match ctx with
  | CtxNil => None
  | CtxCons id' tyA ctx' =>
      if eq_id id id' then Some tyA
      else get_vtype ctx' id
  end.

Fixpoint get_op_type (sig : sig) (id : op_id) : option (vtype * vtype) :=
  match sig with
  | SigNil => None
  | SigCons id' tyA tyB sig' =>
      if eq_id id id' then Some (tyA, tyB)
      else get_op_type sig' id
  end.

Fixpoint find_op_case (h : hcases) (op_id : op_id) 
  : option (var_id * var_id * comp) :=
  match h with
  | NoCases => None
  | OpCases h_others op_id' x_op k_op c_op =>
      if eq_id op_id op_id' then Some (x_op, k_op, c_op)
      else find_op_case h_others op_id
  end.

(* NOT CAPTURE AVOIDING!!! *)
Fixpoint vsubst (sub : var_id * val) (v : val) :=
  (* v [id |-> sv] *)
  let (s_id, s_v) := sub in
  match v with
  | Var id => if eq_id id s_id then s_v else v
  | Unit => v
  | Int n => v
  | Inl v' => vsubst sub v'
  | Inr v' => vsubst sub v'
  | Pair v1 v2 => Pair (vsubst sub v1) (vsubst sub v2)
  | Fun id c => if eq_id id s_id then v else Fun id (csubst sub c) 
  | Handler ret_id c h => 
      if eq_id ret_id s_id then Handler ret_id c (hsubst sub h)
      else Handler ret_id (csubst sub c) (hsubst sub h)
  | VAnnot v ty =>  VAnnot (vsubst sub v) ty
  end
with csubst (sub : var_id * val) (c : comp) :=
  (* c [id |-> sv] *)
  let (s_id, s_v) := sub in
  match c with
  | Ret v => Ret (vsubst sub v)
  | PMatch v (id1, id2) c' => 
      if eq_id id1 s_id then c
      else if eq_id id2 s_id then c
      else PMatch (vsubst sub v) (id1, id2) (csubst sub c')
  | SMatch v idl cl idr cr =>
      let cl' := if eq_id idl s_id then cl else csubst sub cl in
      let cr' := if eq_id idr s_id then cr else csubst sub cr in
      SMatch (vsubst sub v) idl cl' idr cr'
  | App vf vx => App (vsubst sub vf) (vsubst sub vx)
  | Op op_id v_arg id k =>
      let k' := if eq_id id s_id then k else csubst sub k in
      Op op_id (vsubst sub v_arg) id k'
  | LetRec f_id x_id c1 c2 =>
      if eq_id f_id s_id then c
      else if eq_id x_id s_id then c
      else LetRec f_id x_id (csubst sub c1) (csubst sub c2)
  | DoBind x_id c1 c2 =>
      if eq_id x_id s_id then DoBind x_id (csubst sub c1) c2
      else DoBind x_id (csubst sub c1) (csubst sub c2)
  | Handle v c' => Handle (vsubst sub v) (csubst sub c')
  | CAnnot c ty => CAnnot (csubst sub c) ty
  end
with hsubst (sub : var_id * val) (h : hcases) :=
  (* c [id |-> sv] *)
  let (s_id, s_v) := sub in
  match h with
  | NoCases => h
  | OpCases h' op_id x_id k_id c_op =>
      let c_op' := 
        if eq_id x_id s_id then c_op
        else if eq_id k_id s_id then c_op
      else csubst sub c_op in
      OpCases (hsubst sub h') op_id x_id k_id c_op'
  end.