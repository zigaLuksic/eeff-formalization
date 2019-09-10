universe u

namespace term_syntax

def var_id : Type := string
def op_id : Type := string

inductive is : Type u
| val : is
| comp : is
| hcases : is

inductive term : is → Type u
| var : var_id → term is.val
| unit : term is.val
| lambda : var_id → term is.comp → term is.val
| handler : term is.hcases → term is.val
| return : term is.val → term is.comp
| application : term is.val → term is.val → term is.comp
| operation : op_id → term is.val → var_id × term is.comp → term is.comp
| handle : term is.val → term is.comp → term is.comp
| return_case : var_id → term is.comp → term is.hcases


def depth {k : is} (t : term k) : ℕ :=
match k with
| is.val := match t with
    | (term.var x) := 1
    | (term.unit) := 1
    | (term.lambda : var_id → term → term
    | (term.handler : term → term
    end

-- | (return : term → term
-- | (prod_match : term → var_id × var_id → term → term
-- | (sum_match :
--     term → var_id × term → var_id × term → term
-- | (application : term → term → term
-- | (operation : op_id → term → var_id × term → term
-- | (letrec : var_id → var_id → term → term → term
-- | (dobind : var_id × term → term → term
-- | (handle : term → term → term
-- | (return_case : var_id → term → term
-- | (operation_case :
--     op_id → var_id → var_id → term → term → term
end

end term_syntax
