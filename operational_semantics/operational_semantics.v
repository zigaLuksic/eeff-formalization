(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add Rec LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add Rec LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export syntax substitution.

Inductive step : comp -> comp -> Prop :=
| Step_ΠMatch v1 v2 c: 
    step 
      (ΠMatch (Pair v1 v2) c)
      (c_subs2_out c v1 v2)
| Step_ΣMatch_Inl v c1 c2:
    step 
      (ΣMatch (Inl v) c1 c2)
      (c_subs_out c1 v)
| Step_ΣMatch_Inr v c1 c2:
    step 
      (ΣMatch (Inr v) c1 c2)
      (c_subs_out c2 v)
| Step_ListMatch_Nil c1 c2:
    step 
      (ListMatch ListNil c1 c2)
      c1
| Step_ListMatch_Cons v vs c1 c2:
    step 
      (ListMatch (ListCons v vs) c1 c2)
      (c_subs2_out c2 v vs)
| Step_App c v:
    step (App (Fun c) v) (c_subs_out c v)
| Step_LetRec c1 c2:
    step
      (LetRec c1 c2)
      (c_subs_out c2 (Fun (LetRec (c_shift c1 1 2) c1)))
| Step_DoBind_step c1 c1' c2:
    step c1 c1' ->
    step (DoBind c1 c2) (DoBind c1' c2)
| Step_DoBind_Ret v c:
    step (DoBind (Ret v) c) (c_subs_out c v)
| Step_DoBind_Op op v c1 c2:
    step
      (DoBind (Op op v c1) c2)
      (Op op v (DoBind c1 (c_shift c2 1 1)))
| Step_Handle_Step v c c' :
    step c c' ->
    step (Handle v c) (Handle v c')
| Step_Handle_Ret c_r h v :
    step
      (Handle (Handler c_r h) (Ret v))
      (c_subs_out c_r v)
| Step_Handle_Op c_r h op v c_k c_op :
    get_case h op = Some c_op ->
    step
      (Handle (Handler c_r h) (Op op v c_k))
      (c_subs2_out c_op v
        (Fun (Handle (v_shift (Handler c_r h) 1 0) c_k)) )
.