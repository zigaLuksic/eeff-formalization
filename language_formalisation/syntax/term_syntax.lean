universe u

namespace term_syntax

def var_id : Type := string
def op_id : Type := string

mutual inductive val, comp, hcases
with val : Type u
| var : var_id → val
| unit : val
| lambda : var_id → comp → val
| handler : hcases → val
with comp : Type u
| return : val → comp
| application : val → val → comp
| operation : op_id → val → var_id × comp → comp
| handle : val → comp → comp
with hcases : Type u
| return_case : var_id → comp → hcases

def term := val ⊕ comp
def full_def := psum val (psum comp hcases)

def size : full_def → ℕ
| (psum.inl v) := val.sizeof v
| (psum.inr (psum.inl c)) := comp.sizeof c
| (psum.inr (psum.inr h)) := hcases.sizeof h

def size_lt : full_def → full_def → Prop
| t1 t2 := size t1 < size t2

def wf_size := measure_wf size

#check measure_wf
#check wf_size

set_option trace.app_builder true

mutual def vdepth, cdepth, hdepth
with vdepth : val → ℕ
| (val.var x) := 1
| (val.unit) := 1
| (val.lambda x c) :=
    have val.sizeof (val.lambda x c) > comp.sizeof c, from sorry,
    1 + (cdepth c)
| (val.handler h) := 1 + (hdepth h)
with cdepth : comp → ℕ
| (comp.return v_ret) := 1 + (vdepth v_ret) 
| (comp.application v_fun v_arg) :=
    1 + max (vdepth v_fun) (vdepth v_arg)
| (comp.operation op_id v_arg (k, c_cont)) :=
    1 +  max (vdepth v_arg) (cdepth c_cont)
| (comp.handle v c) := 1 + max (vdepth v) (cdepth c)
with hdepth : hcases → ℕ
| (hcases.return_case x c_ret) :=
    1 +  cdepth c_ret
using_well_founded {rel_tac := λ _ _, `[exact ⟨size_lt, wf_size⟩]}

end term_syntax
