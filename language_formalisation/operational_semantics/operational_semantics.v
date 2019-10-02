Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
Require Export syntax substitution.

Inductive small_step : comp -> comp -> Type :=
| Step_pmatch v1 v2 x y c: 
    small_step 
      (ΠMatch (Pair v1 v2) (x, y) c)
      (c_sub2_out c v1 v2)
| Step_smatch_l v xl cl xr cr:
    small_step 
      (ΣMatch (Inl v) xl cl xr cr)
      (c_sub_out cl v)
| Step_smatch_r v xl cl xr cr:
    small_step 
      (ΣMatch (Inr v) xl cl xr cr)
      (c_sub_out cr v)
| Step_apply x c v:
    small_step (App (Fun x c) v) (c_sub_out c v)
| Step_dobind_step x c1 c1' c2:
    small_step c1 c1' ->
    small_step (DoBind x c1 c2) (DoBind x c1' c2)
| Step_letrec f x f_ty c1 c2:
    small_step
      (LetRec f x f_ty c1 c2)
      (c_sub_out c2 (Fun x (LetRec f x f_ty (Sub.c_shift c1 1 2) c1)))
| Step_dobind_ret x v c:
    small_step (DoBind x (Ret v) c) (c_sub_out c v)
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
      (c_sub_out c_r v)
| Step_handle_op x c_r h op_id v_arg y c_k x_op k_op c_op :
    find_op_case h op_id = Some (x_op, k_op, c_op) ->
    small_step
      (Handle (Handler x c_r h) (Op op_id v_arg y c_k))
      (c_sub2_out c_op
        (Fun y (Handle (Sub.v_shift (Handler x c_r h) 1 0) c_k))
        v_arg )
.