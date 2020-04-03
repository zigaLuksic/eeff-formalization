Require Export Bool ZArith String.

(* ==================== Custom Tactics ==================== *)

Ltac inv H := inversion H; clear H; subst.
Ltac aomega := (omega || auto).
Ltac eaomega := (omega || eauto).
Ltac aconstructor := constructor; auto.

(* ==================== Variable Type Definitions ==================== *)

Definition op_id := string.
Notation "x == y" := (string_dec x y) (at level 75, no associativity).

Definition int := Z.t.

(* ==================== Syntax Definitions ==================== *)

Inductive val : Type :=
| Var : nat -> val
| Unit : val
| Int : Z.t -> val
| Inl : val -> val
| Inr : val -> val
| Pair : val -> val -> val
| ListNil : val
| ListCons : val -> val -> val
| Fun : comp -> val
| Handler : comp -> hcases -> val

with comp : Type :=
| Ret : val -> comp
| Absurd : val -> comp
| ΠMatch : val -> comp -> comp (* x~1 y~0 *)
| ΣMatch : val -> comp -> comp -> comp
| ListMatch : val -> comp -> comp -> comp (* x~1 xs~0 *)
| App : val -> val -> comp
| Op : op_id -> val -> comp -> comp (* x~1 k~0 *)
| LetRec : comp -> comp -> comp (* f~0 x~1 *)
| DoBind : comp -> comp -> comp
| Handle : val -> comp -> comp

with hcases : Type :=
| CasesØ : hcases
| CasesU : hcases -> op_id -> comp -> hcases (* x~1 k~0 *).

Inductive vtype : Type :=
| TyUnit : vtype
| TyInt : vtype
| TyØ : vtype
| TyΣ : vtype -> vtype -> vtype
| TyΠ : vtype -> vtype -> vtype
| TyList : vtype -> vtype
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
| TApp : nat -> val -> tmpl
| TAbsurd : val -> tmpl
| TΠMatch : val -> tmpl -> tmpl
| TΣMatch : val -> tmpl -> tmpl -> tmpl
| TListMatch : val -> tmpl -> tmpl -> tmpl
| TLetBind : comp -> tmpl -> tmpl
| TOp : op_id -> val -> tmpl -> tmpl

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


Fixpoint get_case h op : option comp :=
  match h with
  | CasesØ => None
  | CasesU h' op' c_op =>
      if op == op' then Some c_op else get_case h' op
  end.


Fixpoint has_eq E Γ Z T1 T2 :=
  match E with
  | EqsØ => False
  | EqsU E' Γ' Z' T1' T2' =>
      (Γ = Γ' /\ Z = Z' /\ T1 = T1' /\ T2 = T2') \/ has_eq E' Γ Z T1 T2
  end.


Fixpoint ctx_insert Γ i A :=
  match i, Γ with
  | 0, Γ' => CtxU Γ' A
  | _, CtxØ => CtxØ
  | S i', CtxU Γ' A' => CtxU (ctx_insert Γ' i' A) A'
  end.


Fixpoint tctx_to_ctx Z D :=
  match Z with
  | TCtxØ => CtxØ
  | TCtxU Z A => CtxU (tctx_to_ctx Z D) (TyFun A D)
  end.


Fixpoint join_ctxs Γ1 Γ2 :=
  match Γ2 with
  | CtxØ => Γ1
  | CtxU Γ2' A => CtxU (join_ctxs Γ1 Γ2') A
  end.

(* ==================== Judgements and Hypotheses ==================== *)

Inductive formula : Type :=
  | Veq : vtype -> val -> val -> formula
  | Ceq : ctype -> comp -> comp -> formula
  | Heq : sig -> ctype -> hcases -> hcases -> formula
  | Truth : formula
  | Falsity : formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Implies : formula -> formula -> formula
  | Forall : vtype -> formula -> formula
  | Exists : vtype -> formula -> formula.

Inductive hypotheses : Type :=
  | HypØ : hypotheses
  | HypU : hypotheses -> formula -> hypotheses.

Fixpoint has_hypothesis Ψ φ :=
  match Ψ with
  | HypØ => False
  | HypU Ψ' φ' => φ = φ' \/ has_hypothesis Ψ' φ
  end.

(* ==================== Instantiation ==================== *)

Inductive instantiation : Type :=
| InstØ : instantiation
| InstU : instantiation -> val -> instantiation.


Fixpoint get_inst_val I i :=
  match I, i with
  | InstØ , _=> None
  | InstU I' v, 0 => Some v
  | InstU I' v, S i' =>  get_inst_val I' i'
  end.


Fixpoint inst_insert I n v :=
  if n =? 0 then InstU I v else
  match I with
  | InstØ => InstØ
  | InstU I' v' => InstU (inst_insert I' (n-1) v) v'
  end.

(* ==================== Lengths ==================== *)

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


Fixpoint inst_len I :=
  match I with
  | InstØ => 0
  | InstU I' _ => 1 + (inst_len I')
  end.

(* ==================== Term Properties ==================== *)

Fixpoint v_no_var v j :=
  match v with
  | Var dbi => not (j = dbi)
  | Unit => True
  | Int j => True
  | Inl v' => v_no_var v' j
  | Inr v' => v_no_var v' j
  | Pair v1 v2 =>
      (v_no_var v1 j) /\ (v_no_var v2 j)
  | ListNil => True
  | ListCons v vs =>
      (v_no_var v j) /\ (v_no_var vs j)
  | Fun c => 
      c_no_var c (1+j)
  | Handler c_ret h =>
      (c_no_var c_ret (1+j)) /\ (h_no_var h j)
  end

with c_no_var c j :=
  match c with
  | Ret v => v_no_var v j
  | Absurd v => v_no_var v j 
  | ΠMatch v c => 
      (v_no_var v j) /\ c_no_var c (2+j)
  | ΣMatch v c1 c2 =>
      (v_no_var v j) /\ (c_no_var c1 (1+j)) /\ (c_no_var c2 (1+j))
  | ListMatch v c1 c2 =>
      (v_no_var v j) /\ (c_no_var c1 j) /\ (c_no_var c2 (2+j))
  | App v1 v2 => 
      (v_no_var v1 j) /\ (v_no_var v2 j)
  | Op op v_arg c =>
      (v_no_var v_arg j) /\ (c_no_var c (1+j))
  | LetRec c1 c2 =>
      (c_no_var c1 (2+j)) /\ (c_no_var c2 (1+j))
  | DoBind c1 c2 =>
      (c_no_var c1 j) /\ (c_no_var c2 (1+j))
  | Handle v c' =>
      (v_no_var v j) /\ (c_no_var c' j)
  end

with h_no_var h j :=
  match h with
  | CasesØ => True
  | CasesU h op c =>
      (h_no_var h j) /\ (c_no_var c (2+j))
  end.


Fixpoint v_under_var v j :=
  match v with
  | Var dbi => dbi < j
  | Unit => True
  | Int j => True
  | Inl v' => v_under_var v' j
  | Inr v' => v_under_var v' j
  | Pair v1 v2 =>
      (v_under_var v1 j) /\ (v_under_var v2 j)
  | ListNil => True
  | ListCons v vs =>
      (v_under_var v j) /\ (v_under_var vs j)
  | Fun c =>
      c_under_var c (1+j)
  | Handler c_ret h =>
      (c_under_var c_ret (1+j)) /\ (h_under_var h j)
  end

with c_under_var c j :=
  match c with
  | Ret v => v_under_var v j
  | Absurd v => v_under_var v j 
  | ΠMatch v c => 
      (v_under_var v j) /\ c_under_var c (2+j)
  | ΣMatch v c1 c2 =>
      (v_under_var v j) /\ (c_under_var c1 (1+j)) /\ (c_under_var c2 (1+j))
  | ListMatch v c1 c2 =>
      (v_under_var v j) /\ (c_under_var c1 j) /\ (c_under_var c2 (2+j))
  | App v1 v2 =>
      (v_under_var v1 j) /\ (v_under_var v2 j)
  | Op op v c =>
      (v_under_var v j) /\ (c_under_var c (1+j))
  | LetRec c1 c2 =>
      (c_under_var c1 (2+j)) /\ (c_under_var c2 (1+j))
  | DoBind c1 c2 =>
      (c_under_var c1 j) /\ (c_under_var c2 (1+j))
  | Handle v c' =>
      (v_under_var v j) /\ (c_under_var c' j)
  end

with h_under_var h j :=
  match h with
  | CasesØ => True
  | CasesU h op c =>
      (h_under_var h j) /\ (c_under_var c (2+j))
  end.


Fixpoint t_under_var T j :=
  match T with
  | TApp zi v => v_under_var v j
  | TAbsurd v => v_under_var v j
  | TΠMatch v T =>
      v_under_var v j /\ t_under_var T (2+j)
  | TΣMatch v T1 T2 =>
      (v_under_var v j) /\ (t_under_var T1 (1+j)) /\ (t_under_var T2 (1+j))
  | TListMatch v T1 T2 =>
      (v_under_var v j) /\ (t_under_var T1 j) /\ (t_under_var T2 (2+j))
  | TLetBind c T =>
      (c_under_var c j) /\ (t_under_var T (1+j))
  | TOp op v T =>
      (v_under_var v j) /\ (t_under_var T (1+j))
  end.


Fixpoint t_under_tvar T j :=
  match T with
  | TApp zi v => zi < j
  | TAbsurd v => True
  | TΠMatch v T => t_under_tvar T j
  | TΣMatch v T1 T2 =>
      (t_under_tvar T1 j) /\ (t_under_tvar T2 j)
  | TListMatch v T1 T2 =>
      (t_under_tvar T1 j) /\ (t_under_tvar T2 j)
  | TLetBind c T =>
      (t_under_tvar T j)
  | TOp op v T =>
      t_under_tvar T j
  end.


Fixpoint inst_no_var I i :=
  match I with
  | InstØ => True
  | InstU I' v => v_no_var v i /\ inst_no_var I' i
  end.


Fixpoint inst_under_var I i :=
  match I with
  | InstØ => True
  | InstU I' v => v_no_var v i /\ inst_under_var I' i
  end.

Fixpoint form_under_var φ i :=
  match φ with
  | Veq A v1 v2 => v_under_var v1 i /\ v_under_var v2 i
  | Ceq C c1 c2 => c_under_var c1 i /\ c_under_var c2 i
  | Heq Σ D h1 h2 => h_under_var h1 i /\ h_under_var h2 i
  | Truth => True
  | Falsity => True
  | And φ1 φ2 => form_under_var φ1 i /\ form_under_var φ2 i
  | Or φ1 φ2 => form_under_var φ1 i /\ form_under_var φ2 i
  | Implies φ1 φ2 => form_under_var φ1 i /\ form_under_var φ2 i
  | Forall A φ => form_under_var φ (1+i)
  | Exists A φ => form_under_var φ (1+i)
  end.