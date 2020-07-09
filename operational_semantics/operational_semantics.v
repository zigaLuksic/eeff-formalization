Add Rec LoadPath "???\syntax".
Add Rec LoadPath "???\substitution".
Require Export syntax substitution.

Inductive step : comp -> comp -> Prop :=
| Step_MatchPair v1 v2 c: 
    step 
      (ProdMatch (Pair v1 v2) c)
      (c_subs2_out c v1 v2)
| Step_MatchLeft A B v c1 c2:
    step 
      (SumMatch (Left A B v) c1 c2)
      (c_subs_out c1 v)
| Step_MatchRight A B v c1 c2:
    step 
      (SumMatch (Right A B v) c1 c2)
      (c_subs_out c2 v)
| Step_MatchNil A c1 c2:
    step 
      (ListMatch (Nil A) c1 c2)
      c1
| Step_MatchCons v vs c1 c2:
    step 
      (ListMatch (Cons v vs) c1 c2)
      (c_subs2_out c2 v vs)
| Step_AppFun A c v:
    step (App (Fun A c) v) (c_subs_out c v)
| Step_LetRecStep A C c1 c2:
    step
      (LetRec A C c1 c2)
      (c_subs_out c2 (Fun A (LetRec A C (c_shift c1 1 2) c1)))
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
| Step_HandleRet A c_r h v :
    step
      (Handle (Handler A c_r h) (Ret v))
      (c_subs_out c_r v)
| Step_HandleOp A c_r h op Aop Bop v c_k c_op :
    get_case h op = Some c_op ->
    step
      (Handle (Handler A c_r h) (Op op Aop Bop v c_k))
      (c_subs2_out c_op v
        (Fun Bop (Handle (v_shift (Handler A c_r h) 1 0) c_k)) )
.