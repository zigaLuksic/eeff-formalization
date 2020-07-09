
(* DISCLAIMER: This example will be fully outlined and cleaned up soon. *)

Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".
Add LoadPath "???\operational_semantics".
Add LoadPath "???\logic".
Add LoadPath "???\examples".

Require Export type_lemmas logic_lemmas logic_tactics.
Open Scope string_scope.


(* ========================================================================== *)

Definition TyA := TyInt. (* Need some wellformed type for `obvious` tactic *)

Definition TyState := TyList TyA. (* Need some wellformed type for `obvious` *)

Definition TyOption A := TySum TyUnit A.

Definition None := Left Unit.

Definition Some a := Right a.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Example state_sig := (SigU (SigU (SigØ) 
    ("get") TyUnit TyState)
    ("set") TyState TyUnit).

Lemma wf_sig_state_sig:
  wf_sig state_sig.
Proof.
unfold state_sig. obvious.
Qed.

Example next_sig := (SigU (SigØ) 
    ("next") TyUnit (TyOption TyA)).

Lemma wf_sig_next_sig:
  wf_sig next_sig.
Proof.
unfold next_sig. obvious.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Example eq_set_get := (EqsU (EqsØ)
  (CtxU (CtxØ) TyState)
  (TCtxU (TCtxØ) TyState)
    (TOp "set" (Var 0) (TOp "get" Unit (TApp 0 (Var 0))))
    (TOp "set" (Var 0) (TApp 0 (Var 1))) ).

Example eq_weak_state := (EqsU eq_set_get
  CtxØ
  (TCtxU (TCtxØ) TyState)
    (TOp "get" Unit (TOp "set" (Var 0) (TApp 0 (Var 1))))
    (TOp "get" Unit (TApp 0 (Var 0))) ).

Lemma wf_eq_set_get:
  wf_eqs eq_set_get state_sig.
Proof.
unfold eq_set_get. unfold state_sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.

Lemma wf_eq_weak_state:
  wf_eqs eq_weak_state state_sig.
Proof.
unfold eq_weak_state. unfold state_sig.
apply WfEqsU; obvious.
+ apply wf_eq_set_get.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Example eq_none_repeats := (EqsU (EqsØ)
  CtxØ (TCtxU (TCtxØ) (TyOption TyA))
    (TOp "next" Unit 
      (TSumMatch (Var 0) 
        (TApp 0 None)
        (TOp "next" Unit (TApp 0 (Var 0))) ))
    (* ~ *)
    (TOp "next" Unit (TOp "next" Unit (TApp 0 (Var 0))) )
).

Lemma wf_eq_none_repeats:
  wf_eqs eq_none_repeats next_sig.
Proof.
unfold eq_none_repeats. unfold next_sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. obvious_vtype.
  wft_step. instantiate (1:=TyA). obvious_vtype.
  wft_step. 2: simpl; reflexivity. obvious_vtype.
  wft_step. simpl. reflexivity. obvious_vtype.
  wft_step. 2: simpl; reflexivity. obvious_vtype.
+ wft_step. simpl. reflexivity. obvious_vtype.
  wft_step. simpl. reflexivity. obvious_vtype.
  wft_step. 2: simpl; reflexivity. obvious_vtype.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Example generator_cases := CasesU (CasesØ)
  ("next") TyUnit (TyOption TyA) (* () k -> *)
    (Op "get" Unit 
      (ListMatch (Var 0)
        (* [] *) (App (Var 1) None)
        (* x::xs *) (Op "set" (Var 0)
          (App (Var 4) (Some (Var 2))))
      )
    ).

Lemma cases_types A E :
  wf_vtype A -> wf_eqs E state_sig ->
  has_htype CtxØ generator_cases next_sig (CTy A state_sig E).
Proof.
intros wfa wfe.
unfold generator_cases. apply TypeH; obvious.
apply TypeCasesU.
{ apply TypeH; obvious. apply TypeCasesØ. }
ctype_step. eapply TypeOp. simpl. reflexivity. obvious_vtype.
ctype_step. instantiate (1:=TyA). obvious_vtype. 
ctype_step. instantiate (1:=TyOption TyA). obvious_vtype. obvious_vtype.
ctype_step. eapply TypeOp. simpl. reflexivity.  obvious_vtype.
ctype_step. instantiate (1:=TyOption TyA). obvious_vtype.
all: obvious_vtype.
Qed.

(* ========================================================================== *)


Example generator_respects A:
  wf_vtype A ->
  respects
    CtxØ generator_cases
    next_sig (CTy A state_sig eq_weak_state) eq_none_repeats.
Proof.
intros wfa.
specialize wf_eq_weak_state as wfe1.
specialize wf_eq_none_repeats as wfe2.
specialize wf_sig_state_sig as wfsig1.
specialize wf_sig_next_sig as wfsig2.
specialize WfHypØ as wfhyp.
apply Respects; obvious. apply RespectEqsU.
{ apply Respects; obvious. apply RespectEqsØ. }
simpl. simpl_c_subs.

(* cleanup phase L *)
eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqOp.
simpl. reflexivity. apply veq_refl. obvious_vtype. obvious.

eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqListMatch.
simpl. apply veq_refl. admit. obvious. 
{ eapply WfJudg; obvious. admit. apply βApp. }
{ eapply WfJudg. instantiate (1:=TyA). all: obvious. admit. eapply CeqOp.
  simpl. reflexivity. simpl. apply veq_refl. admit. auto.
  apply WfJudg; obvious. admit. apply βApp. }

simpl_c_subs. eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqListMatch.
simpl. apply veq_refl. admit. obvious. 
{ eapply WfJudg; obvious. admit. eapply CeqSumMatch.
  apply veq_refl. admit. obvious. apply ceq_refl. admit. obvious.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious.
  apply WfJudg; obvious. admit. eapply CeqListMatch.
  + apply veq_refl. admit. obvious.
  + apply WfJudg; obvious. admit. apply βApp.
  + instantiate (2:=TyA). apply WfJudg; obvious. admit. eapply CeqOp.
    simpl. reflexivity. apply veq_refl. admit. obvious. 
    apply WfJudg; obvious. admit. apply βApp. }
{ apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit.
  eapply CeqSumMatch. instantiate (2:=TyA). apply veq_refl. admit. obvious.
  apply ceq_refl. admit. obvious.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit.
  eapply CeqListMatch; simpl. instantiate (2:=TyA).
  apply veq_refl. admit. obvious.
  apply WfJudg; obvious. admit. apply βApp.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit. apply βApp. }

simpl_c_subs. apply WfJudg; obvious. admit. eapply CeqListMatch.
instantiate (2:=TyA).
{ apply veq_refl. admit. obvious. }
{ apply WfJudg; obvious. admit. apply βMatchLeft. }
{ apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. 
  apply WfJudg; obvious. admit. apply βMatchRight. }

simpl_c_subs. apply ceq_sym.

(* cleanup phase R *)
eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqOp.
simpl. reflexivity. apply veq_refl. obvious_vtype. obvious.

eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqListMatch.
simpl. apply veq_refl. admit. obvious. 
{ eapply WfJudg; obvious. admit. apply βApp. }
{ eapply WfJudg. instantiate (1:=TyA). all: obvious. admit. eapply CeqOp.
  simpl. reflexivity. simpl. apply veq_refl. admit. auto.
  apply WfJudg; obvious. admit. apply βApp. }

simpl_c_subs. eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqListMatch.
simpl. apply veq_refl. admit. obvious.
{ apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit.
  eapply CeqListMatch. instantiate (2:=TyA). apply veq_refl. admit. obvious.
  apply WfJudg; obvious. admit. apply βApp.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit. apply βApp. }
{ eapply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit.
  eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit.
  eapply CeqListMatch. instantiate (2:=TyA). apply veq_refl. admit. obvious.
  apply WfJudg; obvious. admit. apply βApp.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. reflexivity.
  apply veq_refl. admit. obvious. apply WfJudg; obvious. admit. apply βApp. }

simpl_c_subs. apply ceq_refl. admit. obvious.

(* OOTB get set weak on left side *)

assert ( judg 
  (CtxU CtxØ (TyFun (TyOption TyA) (CTy A state_sig eq_weak_state))) HypØ
  (Ceq (CTy A state_sig eq_weak_state)
    (Op "get" Unit
      (Op "set" (Var 0)
      (App (Fun
        (ListMatch (Var 0)
          (Op "get" Unit
              (ListMatch (Var 0) (App (Var 4) (Left Unit))
                (Op "set" (Var 0) (App (Var 7) (Right (Var 2))))))
          (Op "set" (Var 0)
              (Op "get" Unit
                (ListMatch (Var 0) (App (Var 7) (Left Unit))
                    (Op "set" (Var 0) (App (Var 10) (Right (Var 2)))))))))
        (Var 1))))
    (Op "get" Unit
      (App (Fun
        (ListMatch (Var 0)
          (Op "get" Unit
              (ListMatch (Var 0) (App (Var 3) (Left Unit))
                (Op "set" (Var 0) (App (Var 6) (Right (Var 2))))))
          (Op "set" (Var 0)
              (Op "get" Unit
                (ListMatch (Var 0) (App (Var 6) (Left Unit))
                    (Op "set" (Var 0) (App (Var 9) (Right (Var 2)))))))))
        (Var 0))) ) ).
{ apply WfJudg; obvious. admit.
  eapply OOTB. simpl. left. eauto.
  instantiate (1:= InstU InstØ
  (Fun
    (ListMatch (Var 0)
      (Op "get" Unit
          (ListMatch (Var 0) (App (Var 2) (Left Unit))
            (Op "set" (Var 0) (App (Var 5) (Right (Var 2))))))
      (Op "set" (Var 0)
          (Op "get" Unit
            (ListMatch (Var 0) (App (Var 5) (Left Unit))
                (Op "set" (Var 0) (App (Var 8) (Right (Var 2)))))))))).
  admit. simpl. reflexivity. simpl. reflexivity. }

(* OOTB cleanup *)
eapply ceq_trans in H.
Focus 2.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious. apply ceq_sym.
  apply WfJudg; obvious. admit. apply βApp.

apply ceq_sym in H. eapply ceq_trans in H.
Focus 2.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious. apply ceq_sym.
  apply WfJudg; obvious. admit. apply βApp.

(* use OOTB *)
unfold c_subs_out, c_subs in H. simpl in H. eapply ceq_trans. exact H. clear H.


(* continue *)

eapply ceq_trans. apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto. apply veq_refl. obvious_vtype. obvious.

eapply ceq_trans. eapply Op_ListMatch.

all: try reflexivity. instantiate (1:=(Var 0)).
simpl. all: obvious. instantiate (1:=TyA). obvious_vtype.
obvious_vtype. admit. admit. simpl_c_subs.

apply WfJudg; obvious. admit. eapply CeqListMatch.
instantiate (2:=TyA). apply veq_refl. obvious_vtype. auto.
2: apply ceq_refl; admit.

(* OOTB set get *)

assert ( judg
  (CtxU (CtxU CtxØ (TyFun (TyOption TyA) (CTy A state_sig eq_weak_state)))
    TyState) HypØ
  (Ceq (CTy A state_sig eq_weak_state)
    (Op "set" (Var 0)
        (Op "get" Unit
          (App(Fun
           (ListMatch (Var 0) (App (Var 4) (Left Unit))
              (Op "set" (Var 0) (App (Var 7) (Right (Var 2)))))) (Var 0))))
    (Op "set" (Var 0)
      (App (Fun
       (ListMatch (Var 0) (App (Var 3) (Left Unit))
          (Op "set" (Var 0) (App (Var 6) (Right (Var 2)))))) (Var 1)) )
  ) ).
{ apply WfJudg; obvious. admit.
  eapply OOTB. simpl. right. left. eauto.
  instantiate (1:= InstU (InstU InstØ 
  (* First list template vars *)
  (Fun
    (ListMatch (Var 0) (App (Var 2) (Left Unit))
      (Op "set" (Var 0) (App (Var 5) (Right (Var 2))))))
  )
  (* Then regular ones from context *)
  (Var 0)).
  admit. simpl. reflexivity. simpl. reflexivity. }

(* cleanup OOTB *)
eapply ceq_trans in H.
Focus 2.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious. apply ceq_sym.
  apply WfJudg; obvious. admit. apply βApp.

apply ceq_sym in H. eapply ceq_trans in H.
Focus 2.
  apply WfJudg; obvious. admit. eapply CeqOp. simpl. eauto.
  apply veq_refl. obvious_vtype. obvious. apply ceq_sym.
  apply WfJudg; obvious. admit. apply βApp.

unfold c_subs_out, c_subs in H. simpl in H. apply ceq_sym in H.

(* use OOTB *)
exact H.

(* continue *)










Qed.
