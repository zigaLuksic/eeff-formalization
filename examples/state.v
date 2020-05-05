(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\examples". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\examples".

Require Export type_lemmas logic_lemmas logic_tactics.
Open Scope string_scope.

Lemma letbind_ctype A c1 c2 Γ D:
  has_ctype Γ c1 (CTy A SigØ EqsØ) -> has_ctype (CtxU Γ A) c2 D ->
  has_ctype Γ (Do c1 c2) D.
Proof.
intros tys1 tys2.
apply TypeC. inv tys1. auto. inv tys2. auto.
destruct D as [B Σ E]. eapply TypeDo; eauto.
apply TypeC. inv tys1. auto.
+ apply WfCTy. inv tys1. inv H0. auto.
  all: inv tys2; inv H0; auto.
+ eapply TypeCSubsume; eauto. apply STyCTy.
  apply vsubtype_refl. inv tys1. inv H0. auto.
  apply STySigØ. apply STyEqsØ.
Qed.


Lemma letbind_reduce A c1 c1' c2 Γ D:
  ceq (CTy A SigØ EqsØ) Γ c1 c1' -> has_ctype (CtxU Γ A) c2 D ->
  ceq D Γ (Do c1 c2) (Do c1' c2).
Proof.
intros step tys. destruct D as [B Σ E].
assert (wf_ctx Γ) as wfctx by (inv step; inv H; auto).
apply Ceq; obvious.
+ apply TypeC. auto. inv tys. auto.
  eapply TypeDo; eauto. inv step.
  apply TypeC. auto. apply WfCTy. inv H. inv H3. auto.
  3: eapply TypeCSubsume; eauto. all: inv tys; inv H3; auto.
  apply STyCTy. apply vsubtype_refl. inv H2. auto.
  apply STySigØ. apply STyEqsØ.
+ apply TypeC. auto. inv tys. auto.
  eapply TypeDo; eauto. inv step.
  apply TypeC. auto. apply WfCTy. inv H. inv H3. auto.
  3: eapply TypeCSubsume; eauto. all: inv tys; inv H3; auto.
  apply STyCTy. apply vsubtype_refl. inv H2. auto.
  apply STySigØ. apply STyEqsØ.
+ eapply CeqDo. 2: apply ceq_refl; eauto.
  eapply ceq_subtype. eauto. apply WfCTy; inv tys; inv H; inv H0; auto.
  apply STyCTy. apply vsubtype_refl. inv tys. inv H. auto. 
  apply STySigØ. apply STyEqsØ.
Qed.

(* ========================================================================== *)

Definition TyState := TyInt. (* Need some wellformed type *)

Example sig := (SigU (SigU (SigØ) 
    ("get") TyUnit TyState)
    ("set") TyState TyUnit).


Lemma wf_sig_sig:
  wf_sig sig.
Proof.
unfold sig. obvious.
Qed.


Example state_cases := (CasesU (CasesU (CasesØ)
  ("get") 
    (Ret(Fun (
      Do (App (Var 2) (Var 0))
        (App (Var 0) (Var 1)))) ))
  ("set") 
    (Ret(Fun (
      Do (App (Var 2) Unit)
        (App (Var 0) (Var 2)))) )).

  
Lemma has_htype_state_cases D :
  wf_ctype D ->
  has_htype CtxØ state_cases sig (CTy (TyFun TyState D) SigØ EqsØ).
Proof.
intros wfd.
assert (wf_sig sig). apply wf_sig_sig. 
unfold sig in *. unfold state_cases.
apply TypeH; obvious. apply TypeCasesU; obvious.
apply TypeH; obvious. apply TypeCasesU; obvious.
+ apply TypeH; obvious. apply TypeCasesØ.
+ ctype_step. vtype_step.
  eapply letbind_ctype. instantiate (1:=(TyFun TyState D)).
  ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
+ ctype_step. vtype_step.
  eapply letbind_ctype. instantiate (1:=(TyFun TyState D)).
  ctype_step. instantiate (1:=TyUnit). obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Example eq_set_set := (EqsU (EqsØ)
  (CtxU (CtxU (CtxØ) TyState) TyState)
  (TCtxU (TCtxØ) TyUnit)
    (TOp "set" (Var 0) (TOp "set" (Var 2) (TApp 0 Unit)))
    (TOp "set" (Var 1) (TApp 0 Unit)) ).

Example eq_get_get := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) (TyProd TyState TyState))
    (TOp "get" Unit (TOp "get" Unit (TApp 0 (Pair (Var 0) (Var 1)))))
    (TOp "get" Unit (TApp 0 (Pair (Var 0) (Var 0)))) ).

Example eq_set_get := (EqsU (EqsØ)
  (CtxU (CtxØ) TyState)
  (TCtxU (TCtxØ) TyState)
    (TOp "set" (Var 0) (TOp "get" Unit (TApp 0 (Var 0))))
    (TOp "set" (Var 0) (TApp 0 (Var 1))) ).

Example eq_get_set := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) TyUnit)
    (TOp "get" Unit (TOp "set" (Var 0) (TApp 0 Unit)))
    (TApp 0 Unit) ).

Example eq_get_set_weak := (EqsU (EqsØ)
  CtxØ
  (TCtxU (TCtxØ) TyState)
    (TOp "get" Unit (TOp "set" (Var 0) (TApp 0 (Var 1))))
    (TOp "get" Unit (TApp 0 (Var 0))) ).

Lemma wf_eq_set_set:
  wf_eqs eq_set_set sig.
Proof.
unfold eq_set_set. unfold sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. obvious_vtype. simpl. auto.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. obvious_vtype. simpl. auto.
Qed.

Lemma wf_eq_get_get:
  wf_eqs eq_get_get sig.
Proof.
unfold eq_get_get. unfold sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.

Lemma wf_eq_set_get:
  wf_eqs eq_set_get sig.
Proof.
unfold eq_set_get. unfold sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.


Lemma wf_eq_get_set:
  wf_eqs eq_get_set sig.
Proof.
unfold eq_get_set. unfold sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.


Lemma wf_eq_get_set_weak:
  wf_eqs eq_get_set_weak sig.
Proof.
unfold eq_get_set_weak. unfold sig.
apply WfEqsU; obvious.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
+ eapply WfTOp. simpl. reflexivity. obvious_vtype.
  eapply WfTApp. 2: simpl; reflexivity. obvious_vtype.
Qed.

(* ========================================================================== *)

Lemma respects_set_set A:
  wf_vtype A ->
  respects
    CtxØ state_cases
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_set_set.
Proof.
intros wfa.
unfold state_cases. unfold sig. unfold eq_set_set.
apply Respects; obvious. apply wf_eq_set_set.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
simpl. simpl_c_subs. apply Ceq; obvious.

{ ctype_step. vtype_step. eapply letbind_ctype.
  instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
  Focus 2. apply TypeC; obvious. eapply TypeApp.
    instantiate (1:=TyState). obvious_vtype. obvious_vtype.
  ctype_step. 2: obvious_vtype. vtype_step. ctype_step. vtype_step.
  eapply letbind_ctype. instantiate (1:= (TyFun TyState (CTy A SigØ EqsØ))).
  + ctype_step. 2:obvious_vtype. vtype_step. obvious_ctype.
  + ctype_step. instantiate (1:=TyState). all: obvious_vtype. }
{ ctype_step. vtype_step. eapply letbind_ctype.
  instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
  Focus 2. ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
  ctype_step. 2: obvious_vtype. vtype_step. obvious_ctype. }

apply CeqRet. apply Veq; obvious.

{ vtype_step. eapply letbind_ctype.
  instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
  Focus 2. apply TypeC; obvious. eapply TypeApp.
    instantiate (1:=TyState). obvious_vtype. obvious_vtype.
  ctype_step. 2: obvious_vtype. vtype_step. ctype_step. vtype_step.
  eapply letbind_ctype. instantiate (1:= (TyFun TyState (CTy A SigØ EqsØ))).
  + ctype_step. 2:obvious_vtype. vtype_step. obvious_ctype.
  + ctype_step. instantiate (1:=TyState). all: obvious_vtype. }
{ vtype_step. eapply letbind_ctype.
  instantiate (1:=(TyFun TyState (CTy A SigØ EqsØ))).
  Focus 2. ctype_step. instantiate (1:=TyState). obvious_vtype. obvious_vtype.
  ctype_step. 2: obvious_vtype. vtype_step. obvious_ctype. }

apply VeqFun. eapply ceq_trans.
instantiate (1:=
  (Do (Ret (Fun
          (Do (App (Fun (App (Var 5) Unit)) Unit)
             (App (Var 0) (Var 4)))))) (App (Var 0) (Var 2)) ).
eapply (letbind_reduce (TyFun TyState (CTy A SigØ EqsØ))).

{ apply Ceq; obvious. 3: apply βApp.
  { ctype_step. 2:obvious_vtype. vtype_step. ctype_step.
    vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
    + ctype_step. 2:obvious_vtype. vtype_step. obvious_ctype.
    + ctype_step. instantiate (1:=TyState). all: obvious_vtype. }
  { ctype_step. vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
    + ctype_step. 2:obvious_vtype. vtype_step. obvious_ctype.
    + ctype_step. instantiate (1:=TyState). all: obvious_vtype. } }
{ ctype_step. instantiate (1:=TyState). all: obvious_vtype. }

eapply ceq_trans. apply Ceq; obvious. 3: apply βDoRet.

{ eapply letbind_ctype. instantiate (1:= (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step. vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step. 2: obvious_vtype. vtype_step. obvious_ctype. 
  ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype.
  ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype. }
{ simpl_c_subs. ctype_step. instantiate (1:= TyState). 2:obvious_vtype.
  vtype_step. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step. vtype_step. obvious_ctype. obvious_vtype.
  ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype. }

simpl_c_subs. eapply ceq_trans. apply Ceq. 3: apply βApp. all: simpl_c_subs.

{ ctype_step. instantiate (1:=TyState). 2: obvious_vtype.
  vtype_step.  eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step. vtype_step. obvious_ctype. obvious_vtype.
  ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype. }
{ eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
  ctype_step. vtype_step. obvious_ctype. obvious_vtype.
  ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype.  }

apply ceq_refl. eapply (letbind_ctype (TyFun TyState (CTy A SigØ EqsØ))).
ctype_step. vtype_step. obvious_ctype. obvious_vtype.
ctype_step. instantiate (1:= TyState). obvious_vtype. obvious_vtype.

Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Lemma respects_get_get A:
  wf_vtype A ->
  respects 
    CtxØ state_cases 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_get.
Proof.
intros wfa.
unfold state_cases. unfold sig. unfold eq_get_get.
apply Respects; obvious. apply wf_eq_get_get.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
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


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Lemma respects_set_get A:
  wf_vtype A ->
  respects 
    CtxØ state_cases 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_set_get.
Proof.
intros wfa.
unfold state_cases. unfold sig. unfold eq_set_get.
apply Respects; obvious. apply wf_eq_set_get.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
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


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Lemma respects_get_set A:
  wf_vtype A ->
  respects 
    CtxØ state_cases 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_set.
Proof.
intros wfa.
unfold state_cases. unfold sig. unfold eq_get_set.
apply Respects; obvious. apply wf_eq_get_set.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
simpl. simpl_c_subs.
admit.
Admitted.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Lemma respects_get_set_weak A:
  wf_vtype A ->
  respects 
    CtxØ state_cases 
    sig (CTy (TyFun TyState (CTy A SigØ EqsØ)) SigØ EqsØ) eq_get_set_weak.
Proof.
intros wfa.
unfold state_cases. unfold sig. unfold eq_get_set_weak.
apply Respects; obvious. apply wf_eq_get_set_weak.
apply RespectEqsU. apply Respects; obvious. apply RespectEqsØ.
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