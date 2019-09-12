Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import term_syntax.

Inductive small_step : comp -> comp -> Type :=
| Step_pmatch v1 v2 x y c: 
    small_step 
      (PMatch (Pair v1 v2) (x, y) c)
      (csubst (x, v1) (csubst (y, v2) c))
| Step_smatch_l v xl cl xr cr:
    small_step 
      (SMatch (Inl v) xl cl xr cr)
      (csubst (xl, v) cl)
| Step_smatch_r v xl cl xr cr:
    small_step 
      (SMatch (Inr v) xl cl xr cr)
      (csubst (xr, v) cr)
| Step_apply x c v:
    small_step (App (Fun x c) v) (csubst (x, v) c)
| Step_dobind_step x c1 c1' c2:
    small_step c1 c1' ->
    small_step (DoBind x c1 c2) (DoBind x c1' c2)
| Step_dobind_ret x v c:
    small_step (DoBind x (Ret v) c) (csubst (x, v) c)
| Step_dobind_op x op_id v_arg y c1 c2:
    small_step
      (DoBind x (Op op_id v_arg y c1) c2)
      (Op op_id v_arg y (DoBind x c1 c2))
| Step_handle_step v c c' :
    small_step c c' ->
    small_step (Handle v c) (Handle v c')
| Step_handle_ret x c_r h v :
    small_step
      (Handle (Handler x c_r h) (Ret v))
      (csubst (x, v) c_r)
| Step_handle_op x c_r h op_id v_arg y c_k x_op k_op c_op :
    find_op_case h op_id = Some (x_op, k_op, c_op) ->
    small_step
      (Handle (Handler x c_r h) (Op op_id v_arg y c_k))
      (csubst (x_op, v_arg)
        (csubst 
          (k_op, (Fun y (Handle (Handler x c_r h) c_k)))
          c_op ) )
.