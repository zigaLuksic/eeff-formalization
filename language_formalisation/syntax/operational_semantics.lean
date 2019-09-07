import .term_syntax
open term_syntax

universe u

inductive smallstep : (comp : Type u) → (comp : Type u) → Type u
| β_pair_match (v1 v2 : val) (x y : var_id) (c : comp): 
    smallstep
      (comp.prod_match (val.pair v1 v2) x y c)
      (comp.return val.unit)



