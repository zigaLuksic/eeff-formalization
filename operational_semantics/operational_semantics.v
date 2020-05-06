(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add Rec LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add Rec LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Require Export syntax substitution.

Inductive step : comp -> comp -> Prop :=
| Step_MatchPair v1 v2 c: 
    step 
      (ProdMatch (Pair v1 v2) c)
      (c_subs2_out c v1 v2)
| Step_MatchLeft v c1 c2:
    step 
      (SumMatch (Left v) c1 c2)
      (c_subs_out c1 v)
| Step_MatchRight v c1 c2:
    step 
      (SumMatch (Right v) c1 c2)
      (c_subs_out c2 v)
| Step_MatchNil c1 c2:
    step 
      (ListMatch Nil c1 c2)
      c1
| Step_MatchCons v vs c1 c2:
    step 
      (ListMatch (Cons v vs) c1 c2)
      (c_subs2_out c2 v vs)
| Step_AppFun c v:
    step (App (Fun c) v) (c_subs_out c v)
| Step_LetRecStep c1 c2:
    step
      (LetRec c1 c2)
      (c_subs_out c2 (Fun (LetRec (c_shift c1 1 2) c1)))
| Step_DoStep c1 c1' c2:
    step c1 c1' ->
    step (Do c1 c2) (Do c1' c2)
| Step_DoRet v c:
    step (Do (Ret v) c) (c_subs_out c v)
| Step_DoOp op A B v c1 c2:
    step
      (Do (Op op A B v c1) c2)
      (Op op A B v (Do c1 (c_shift c2 1 1)))
| Step_HandleStep v c c' :
    step c c' ->
    step (Handle v c) (Handle v c')
| Step_HandleRet c_r h v :
    step
      (Handle (Handler c_r h) (Ret v))
      (c_subs_out c_r v)
| Step_HandleOp c_r h op A B v c_k c_op :
    get_case h op = Some c_op ->
    step
      (Handle (Handler c_r h) (Op op A B v c_k))
      (c_subs2_out c_op v
        (Fun (Handle (v_shift (Handler c_r h) 1 0) c_k)) )
.