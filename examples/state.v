Add LoadPath "???\syntax".
Add LoadPath "???\type_system".
Add LoadPath "???\substitution".
Add LoadPath "???\operational_semantics".
Add LoadPath "???\logic".

Require Export type_lemmas logic_lemmas logic_tactics.
Open Scope string_scope.

(* ==================== Lemmas for easier work with Do ==================== *)

Lemma letbind_ctype A c1 c2 Γ D:
  has_ctype Γ c1 (CTy A SigØ EqsØ) -> has_ctype (CtxU Γ A) c2 D ->
  has_ctype Γ (Do c1 c2) D.
Proof.
intros tys1 tys2. 
assert (wf_ctx Γ) by (inv tys1; auto). assert (wf_ctype D) by (inv tys2; auto).
assert (wf_vtype A) by (inv tys1; inv H2; auto). destruct D as [B Σ E]. inv H0.
ctype_step. instantiate (1:=A). 2: auto.
ctype_step. eapply TypeCSubsume; eauto.
apply STyCTy. apply vsubtype_refl. auto. apply STySigØ. apply STyEqsØ.
Qed.


Lemma letbind_reduce A c1 c1' c2 Γ D:
  ceq (CTy A SigØ EqsØ) Γ c1 c1' -> has_ctype (CtxU Γ A) c2 D ->
  ceq D Γ (Do c1 c2) (Do c1' c2).
Proof.
intros step tys. destruct D as [B Σ E].
assert (wf_ctx Γ) as wfctx by (inv step; inv H; auto).
apply Ceq; obvious.
+ apply (letbind_ctype A). inv step. auto. auto.
+ apply (letbind_ctype A). inv step. auto. auto.
+ eapply CeqDo. instantiate (1:=A). 2: apply ceq_refl; eauto.
  eapply ceq_subtype. eauto. 
  - inv tys. inv H0. inv H. obvious.
  - apply STyCTy. apply vsubtype_refl. inv tys. inv H. auto. 
    apply STySigØ. apply STyEqsØ.
Qed.

(* ========================================================================== *)

Definition TyState := TyInt. (* Need some wellformed type for `obvious` *)

Example sig := (SigU (SigU (SigØ) 
    ("get") TyUnit TyState)
    ("set") TyState TyUnit).


Lemma wf_sig_sig:
  wf_sig sig.
Proof.
unfold sig. obvious.
Qed.


(* ==================== Define Theory ==================== *)

Example eq_set_set := (EqsU (EqsØ)
  (CtxU (CtxU (CtxØ) TyState) TyState)
  (TCtxU (TCtxØ) TyUnit)
    (TOp "set" TyState TyUnit 
      (Var 0) (TOp "set" TyState TyUnit (Var 2) (TApp 0 Unit)))
    (TOp "set" TyState TyUnit 
      (Var 1) (TApp 0 Unit)) ).

Example eq_get_get := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) (TyProd TyState TyState))
    (TOp "get" TyUnit TyState 
      Unit (TOp "get" TyUnit TyState Unit (TApp 0 (Pair (Var 0) (Var 1)))))
    (TOp "get" TyUnit TyState 
      Unit (TApp 0 (Pair (Var 0) (Var 0)))) ).

Example eq_set_get := (EqsU (EqsØ)
  (CtxU (CtxØ) TyState)
  (TCtxU (TCtxØ) TyState)
    (TOp "set" TyState TyUnit 
      (Var 0) (TOp "get" TyUnit TyState Unit (TApp 0 (Var 0))))
    (TOp "set" TyState TyUnit 
      (Var 0) (TApp 0 (Var 1))) ).

Example eq_get_set := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) TyUnit)
    (TOp "get" TyUnit TyState 
      Unit (TOp "set" TyState TyUnit (Var 0) (TApp 0 Unit)))
    (TApp 0 Unit) ).

Example eq_get_set_weak := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) TyState)
    (TOp "get" TyUnit TyState 
      Unit (TOp "set" TyState TyUnit (Var 0) (TApp 0 (Var 1))))
    (TOp "get" TyUnit TyState 
      Unit (TApp 0 (Var 0))) ).

Lemma wf_eq_set_set:
  wf_eqs eq_set_set sig.
Proof.
unfold eq_set_set. unfold sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step; obvious_vtype.
+ wft_step. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step; obvious_vtype.
Qed.


Lemma wf_eq_get_get:
  wf_eqs eq_get_get sig.
Proof.
unfold eq_get_get. unfold sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=(TyProd TyState TyState)).
  all: obvious_vtype.
+ wft_step. simpl. reflexivity.
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=(TyProd TyState TyState)).
  all: obvious_vtype.
Qed.


Lemma wf_eq_set_get:
  wf_eqs eq_set_get sig.
Proof.
unfold eq_set_get. unfold sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=TyState). all: obvious_vtype.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=TyState). all: obvious_vtype.
Qed.


Lemma wf_eq_get_set:
  wf_eqs eq_get_set sig.
Proof.
unfold eq_get_set. unfold sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step; obvious_vtype.
+ wft_step; obvious_vtype.
Qed.


Lemma wf_eq_get_set_weak:
  wf_eqs eq_get_set_weak sig.
Proof.
unfold eq_get_set_weak. unfold sig.
apply WfEqsU; obvious.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=TyState). all: obvious_vtype.
+ wft_step. simpl. reflexivity. 
  { apply vsubtype_refl. obvious. }
  { apply vsubtype_refl. obvious. }
  obvious_vtype. wft_step. instantiate (1:=TyState). all: obvious_vtype.
Qed.


(* ==================== Operation cases ==================== *)


Example state_cases D := (CasesU (CasesU 
  (CasesØ (CTy (TyFun TyState D) SigØ EqsØ))
  ("get") TyUnit TyState
    (Ret(Fun TyState (
      Do (App (Var 1) (Var 0))
        (App (Var 0) (Var 1)))) ))
  ("set") TyState TyUnit
    (Ret(Fun TyState (
      Do (App (Var 1) Unit)
        (App (Var 0) (Var 3)))) )).

  
Lemma has_htype_state_cases D :
  wf_ctype D ->
  has_htype CtxØ (state_cases D) sig (CTy (TyFun TyState D) SigØ EqsØ).
Proof.
intros wfd.
assert (wf_sig sig). apply wf_sig_sig. 
unfold sig in *. unfold state_cases.
apply TypeH; obvious. apply TypeCasesU; obvious.
apply TypeH; obvious. apply TypeCasesU; obvious.
+ apply TypeH; obvious. apply TypeCasesØ.
+ ctype_step. vtype_step. eapply letbind_ctype.
  instantiate (1:=(TyFun TyState D)).
  ctype_step. instantiate (1:=TyState). vtype_step. obvious_vtype.
  ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
+ ctype_step. vtype_step.
  eapply letbind_ctype. instantiate (1:=(TyFun TyState D)).
  ctype_step. instantiate (1:=TyUnit). obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
Qed.


(* ==================== SET SET ==================== *)
(* The proof is written out in full for SetSet and outlined for others. *)

Lemma respects_set_set A:
  wf_vtype A ->
  respects
    CtxØ (state_cases (CTy A SigØ EqsØ))
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_set_set.
Proof.
intros wfa. unfold state_cases. unfold sig. unfold eq_set_set.
(* Dispatch side conditions *)
apply Respects; obvious. apply wf_eq_set_set. 
apply has_htype_state_cases. obvious.
apply RespectEqsU. apply Respects; obvious.
apply has_htype_state_cases. obvious.
apply RespectEqsØ.

(* CeqRet *)
simpl. simpl_c_subs. apply Ceq; obvious. 3: apply CeqRet.

{ ctype_step. vtype_step. 
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step; obvious_vtype. ctype_step. vtype_step.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. vtype_step.
  ctype_step. instantiate (1:= TyState). vtype_step. vtype_step. }
{ ctype_step. vtype_step. 
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step. instantiate (1:=TyState).
  all: obvious_vtype. }

(* VeqFun *)
apply Veq; obvious. 3: apply VeqFun.

{ vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step; obvious_vtype. ctype_step. vtype_step.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. vtype_step.
  ctype_step. instantiate (1:= TyState). vtype_step. vtype_step. }
{ vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step. instantiate (1:=TyState).
  all: obvious_vtype. }

(* CeqDo and βApp *)
eapply ceq_trans. eapply (letbind_reduce (TyFun TyState (CTy A SigØ EqsØ))).
apply Ceq; obvious. 3: apply βApp.

{ obvious_ctype. ctype_step. vtype_step. 
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))). obvious_ctype.
  obvious_ctype. ctype_step. instantiate (1:=TyState). all: obvious_vtype. }
{ simpl_c_subs. ctype_step. vtype_step.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))). obvious_ctype.
  obvious_ctype. ctype_step. instantiate (1:=TyState). all: obvious_vtype. } 
{ ctype_step. instantiate (1:=TyState). all: obvious_vtype. }

(* βDoRet *)
simpl_c_subs. eapply ceq_trans. apply Ceq; obvious. 3: apply βDoRet.

{ eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step; obvious_vtype.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. vtype_step.
  ctype_step. instantiate (1:= TyState). vtype_step. vtype_step. }
{ simpl_c_subs. ctype_step. instantiate (1:= TyState). vtype_step.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. vtype_step. obvious_vtype. }

(* βApp *)
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp. all: simpl_c_subs.

{ simpl_c_subs. ctype_step. instantiate (1:= TyState). vtype_step.
  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. vtype_step. obvious_vtype. }
{ eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. obvious_vtype. }

(* reflexivity *)
apply ceq_refl.
{ eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  obvious_ctype. obvious_ctype. ctype_step.
  instantiate (1:= TyState). vtype_step. obvious_vtype. }

Qed.


(* ==================== Get Get ==================== *)

Lemma respects_get_get A:
  wf_vtype A ->
  respects 
    CtxØ (state_cases (CTy A SigØ EqsØ))
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_get.
Proof.
intros wfa.
(* Dispatch side conditions *)
apply Respects; obvious. apply wf_eq_get_get. 
apply has_htype_state_cases. obvious.
apply RespectEqsU. apply Respects; obvious.
apply has_htype_state_cases. obvious.
apply RespectEqsØ.
simpl. simpl_c_subs. apply Ceq; obvious.
{ admit. }
{ admit. }
apply CeqRet. apply Veq; obvious.
{ admit. }
{ admit. }
apply VeqFun. eapply ceq_trans. apply Ceq. 3: eapply CeqDo.
{ admit. }
{ admit. }
2: apply ceq_refl; admit. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βDoRet.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply Ceq. 3: eapply CeqDo. 
3: instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
{ admit. }
{ admit. }
2: apply ceq_refl; admit.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply ceq_sym.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_refl. admit.
Admitted.



(* ==================== SET GET ==================== *)

Lemma respects_set_get A:
  wf_vtype A ->
  respects 
    CtxØ (state_cases (CTy A SigØ EqsØ)) 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_set_get.
Proof.
intros wfa.
(* Dispatch side conditions *)
apply Respects; obvious. apply wf_eq_set_get. 
apply has_htype_state_cases. obvious.
apply RespectEqsU. apply Respects; obvious.
apply has_htype_state_cases. obvious.
apply RespectEqsØ.
simpl. simpl_c_subs.
apply Ceq; obvious.
{ admit. }
{ admit. }
apply CeqRet. apply Veq; obvious.
{ admit. }
{ admit. }
apply VeqFun. eapply ceq_trans. apply Ceq. 3: eapply CeqDo.
{ admit. }
{ admit. }
2: apply ceq_refl; admit. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βDoRet.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply Ceq. 3: eapply CeqDo. 
3: instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
{ admit. }
{ admit. }
2: apply ceq_refl; admit.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply ceq_sym.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_refl. admit.
Admitted.



(* ==================== GET SET ==================== *)
(* This one does not hold! *)

Lemma respects_get_set A:
  wf_vtype A ->
  respects 
    CtxØ (state_cases (CTy A SigØ EqsØ)) 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_set.
Proof.
intros wfa.
(* Dispatch side conditions *)
apply Respects; obvious. apply wf_eq_get_set. 
apply has_htype_state_cases. obvious.
apply RespectEqsU. apply Respects; obvious.
apply has_htype_state_cases. obvious.
apply RespectEqsØ.
simpl. simpl_c_subs.
admit.
Admitted.


(* ==================== Weak GET SET ==================== *)

Lemma respects_get_set_weak A:
  wf_vtype A ->
  respects 
    CtxØ (state_cases (CTy A SigØ EqsØ)) 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_set_weak.
Proof.
intros wfa.
(* Dispatch side conditions *)
apply Respects; obvious. apply wf_eq_get_set_weak. 
apply has_htype_state_cases. obvious.
apply RespectEqsU. apply Respects; obvious.
apply has_htype_state_cases. obvious.
apply RespectEqsØ.
simpl. simpl_c_subs.
apply Ceq; obvious.
{ admit. }
{ admit. }
apply CeqRet. apply Veq; obvious.
{ admit. }
{ admit. }
apply VeqFun. eapply ceq_trans. apply Ceq. 3: eapply CeqDo.
{ admit. }
{ admit. }
2: apply ceq_refl; admit. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βDoRet.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply Ceq. 3: eapply CeqDo. 
3: instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
{ admit. }
{ admit. }
2: apply ceq_refl; admit.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. apply ceq_sym.
eapply ceq_trans. apply Ceq. 3: eapply βApp.
{ admit. }
{ admit. }
simpl_c_subs. eapply ceq_refl. admit.
Admitted.