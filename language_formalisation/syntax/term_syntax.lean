universe u

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
| application : val → val → comp
| sum_match : val → var_id → comp → var_id → comp → comp
| prod_match : val → var_id → var_id → comp
| operation : op_id → val → var_id → comp → comp
| letrec : var_id → var_id → comp → comp → comp
| dobind : var_id → comp → comp → comp
| handle : val → comp → comp
with handler_cases : Type u
| return_case : var_id → comp → handler_cases
| operation_case :
    op_id → var_id → var_id → comp → handler_cases → handler_cases