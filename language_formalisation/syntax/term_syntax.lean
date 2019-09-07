universe u

namespace term_syntax

def var_id : Type := string
def op_id : Type := string

mutual inductive val, comp, handler_cases
with val : Type u
| var : var_id → val
| unit : val
| int : int → val
| inl : val → val
| inr : val → val
| pair : val → val → val
| lambda : var_id → comp → val
| handler : handler_cases → val
with comp : Type u
| return : val → comp
| prod_match : val → var_id × var_id → comp → comp
| sum_match : val → var_id × comp → var_id × comp → comp
| application : val → val → comp
| operation : op_id → val → var_id × comp → comp
| letrec : var_id → var_id → comp → comp → comp
| dobind : var_id × comp → comp → comp
| handle : val → comp → comp
with handler_cases : Type u
| return_case : var_id → comp → handler_cases
| operation_case :
    op_id → var_id → var_id → comp → handler_cases → handler_cases

def term := val ⊕ comp
def full_def := (psum val (psum comp handler_cases))

mutual def vdepth, cdepth, hdepth
with vdepth : val → ℕ
| (val.var x) := 1
| (val.unit) := 1
| (val.int n) := 1
| (val.inl vl) := 1 + (vdepth vl) 
| (val.inr vr) := 1 + (vdepth vr)
| (val.pair v1 v2) := 1 + max (vdepth v1) (vdepth v2)
| (val.lambda x c) := 1 + (cdepth c)
| (val.handler h) := 1 + (hdepth h)
with cdepth : comp → ℕ
| (comp.return v_ret) := 1 + (vdepth v_ret) 
| (comp.prod_match v_pair (x, y) c) := 
    1 + max (vdepth v_pair) (cdepth c)
| (comp.sum_match v_sum (x, c_l) (y, c_r)) :=
    1 + max (vdepth v_sum) (max (cdepth c_l) (cdepth c_r))
| (comp.application v_fun v_arg) :=
    1 + max (vdepth v_fun) (vdepth v_arg)
| (comp.operation op_id v_arg (k, c_cont)) :=
    1 +  max (vdepth v_arg) (cdepth c_cont)
| (comp.letrec f x c1 c2) :=
    1 + max (cdepth c1) (cdepth c2)
| (comp.dobind (x, c1) c2) := 
    1 + max (cdepth c1) (cdepth c2)
| (comp.handle v c) := 1 + max (vdepth h) (cdepth c)
with hdepth : handler_cases → ℕ
| (handler_cases.return_case x c_ret) :=
    1 +  cdepth c_ret
| (handler_cases.operation_case op x k c_op hcases) := 
    1 + max (cdepth c_op) (hdepth hcases)


-- this aint capture avoiding yet!
section
variable (id : var_id)
variable (v : val)

mutual def vsubs, csubs, hsubs
with vsubs : val → val
| (val.var x) := if id = x then v else val.var x
| (val.unit) := val.unit
| (val.int n) := val.int n
| (val.inl vl) := val.inl (vsubs vl) 
| (val.inr vr) := val.inr (vsubs vr)
| (val.pair v1 v2) := val.pair (vsubs v1) (vsubs v2)
| (val.lambda x c) :=
    if id = x then val.lambda x c
    else val.lambda x (csubs c)
| (val.handler h) := val.handler (hsubs h)
with csubs : comp → comp
| (comp.return v_ret) := comp.return (vsubs v_ret) 
| (comp.prod_match v_pair (x, y) c) :=
    if id = x ∨ id = y then comp.prod_match v_pair (x, y) c
    else comp.prod_match v_pair (x, y) (csubs c)
| (comp.sum_match v_sum (x, c_l) (y, c_r)) :=
    let c_l' := if id = x then c_l else csubs c_l in
    let c_r' := if id = y then c_r else csubs c_r in
    comp.sum_match v_sum (x, c_l') (y, c_r')
| (comp.application v_fun v_arg) :=
    comp.application (vsubs v_fun) (vsubs v_arg)
| (comp.operation op_id v_arg (k, c_cont)) :=
    let c_cont' := if id = k then c_cont else csubs c_cont in
    comp.operation op_id (vsubs v_arg) (k, c_cont')
| (comp.letrec f x c1 c2) :=
    let c1' := if id = f ∨ id = x then c1 else csubs c1 in
    let c2' := if id = f ∨ id = x then c2 else csubs c2 in
    comp.letrec f x c1' c2'
| (comp.dobind (x, c1) c2) := 
    let c1' := if id = x then c1 else csubs c1 in
    let c2' := if id = x then c2 else csubs c2 in
    comp.dobind (x, c1') c2'
| (comp.handle h c) := comp.handle (vsubs h) (csubs c)
with hsubs : handler_cases → handler_cases
| (handler_cases.return_case x c_ret) :=
    let c_ret' := if id = x then c_ret else csubs c_ret in
    handler_cases.return_case x c_ret'
| (handler_cases.operation_case op x k c_op hcases) := 
    let c_op' := if id = x ∨ id = k then c_op else csubs c_op in
    handler_cases.operation_case op x k c_op' (hsubs hcases)
end

end term_syntax
