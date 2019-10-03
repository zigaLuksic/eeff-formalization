Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
Require Export syntax substitution.

Inductive step : comp -> comp -> Prop :=
| Step_ΠMatch v1 v2 x y c: 
    step 
      (ΠMatch (Pair v1 v2) (x, y) c)
      (c_sub2_out c v1 v2)
| Step_ΣMatch_Inl v xl cl xr cr:
    step 
      (ΣMatch (Inl v) xl cl xr cr)
      (c_sub_out cl v)
| Step_ΣMatch_Inr v xl cl xr cr:
    step 
      (ΣMatch (Inr v) xl cl xr cr)
      (c_sub_out cr v)
| Step_App x c v:
    step (App (Fun x c) v) (c_sub_out c v)
| Step_LetRec f x c1 c2:
    step
      (LetRec f x c1 c2)
      (c_sub_out c2 (Fun x (LetRec f x (Sub.c_shift c1 1 2) c1)))
| Step_DoBind_step x c1 c1' c2:
    step c1 c1' ->
    step (DoBind x c1 c2) (DoBind x c1' c2)
| Step_DoBind_Ret x v c:
    step (DoBind x (Ret v) c) (c_sub_out c v)
| Step_DoBind_Op x op_id v_arg y c1 c2:
    step
      (DoBind x (Op op_id v_arg y c1) c2)
      (Op op_id v_arg y (DoBind x c1 c2))
| Step_Handle_Step v c c' :
    step c c' ->
    step (Handle v c) (Handle v c')
| Step_Handle_Ret x c_r h v :
    step
      (Handle (Handler x c_r h) (Ret v))
      (c_sub_out c_r v)
| Step_Handle_Op x c_r h op_id v_arg y c_k x_op k_op c_op :
    find_op_case h op_id = Some (x_op, k_op, c_op) ->
    step
      (Handle (Handler x c_r h) (Op op_id v_arg y c_k))
      (c_sub2_out c_op
        (Fun y (Handle (Sub.v_shift (Handler x c_r h) 1 0) c_k))
        v_arg )
.