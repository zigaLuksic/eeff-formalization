Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import term_syntax.

Inductive vtype : Type :=
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