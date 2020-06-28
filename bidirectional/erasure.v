(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\bidirectional". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\bidirectional".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Require Import syntax bidirectional declarational subtyping.


Fixpoint v_erase v :=
  match v with
  | BVar id => Var id
  | BUnit => Unit
  | BInt n => Int n
  | BLeft v => Left (v_erase v)
  | BRight v => Right (v_erase v)
  | BPair v1 v2 => Pair (v_erase v1) (v_erase v2)
  | BNil => Nil
  | BCons v vs => Cons (v_erase v) (v_erase vs)
  | BFun c => Fun (c_erase c)
  | BHandler c_r h => Handler (c_erase c_r) (h_erase h)
  | BAnnV v ty => v_erase v
  end

with c_erase c :=
  match c with
  | BRet v => Ret (v_erase v)
  | BAbsurd v => Absurd (v_erase v)
  | BProdMatch v c => ProdMatch (v_erase v) (c_erase c)
  | BSumMatch v c1 c2 => SumMatch (v_erase v) (c_erase c1) (c_erase c2)
  | BListMatch v c1 c2 => ListMatch (v_erase v) (c_erase c1) (c_erase c2)
  | BApp v1 v2 => App (v_erase v1) (v_erase v2)
  | BOp op v c => Op op (v_erase v) (c_erase c)
  | BLetRec ty c1 c2 => LetRec (c_erase c1) (c_erase c2)
  | BDo c1 c2 => Do (c_erase c1) (c_erase c2)
  | BHandle v c => Handle (v_erase v) (c_erase c)
  | BAnnC c ty => c_erase c
  end

with h_erase h :=
  match h with
  | BCasesØ => CasesØ
  | BCasesU h op c => CasesU (h_erase h) op (c_erase c) 
  end.

Fixpoint tmpl_erase T :=
  match T with
  | BTApp z v => TApp z (v_erase v)
  | BTAbsurd v => TAbsurd (v_erase v)
  | BTProdMatch v T => TProdMatch (v_erase v) (tmpl_erase T)
  | BTSumMatch v T1 T2 => 
      TSumMatch (v_erase v) (tmpl_erase T1) (tmpl_erase T2)
  | BTListMatch v T1 T2 => 
      TListMatch (v_erase v) (tmpl_erase T1) (tmpl_erase T2)
  | BTDo c T => TDo (c_erase c) (tmpl_erase T)
  | BTOp op v T => TOp op (v_erase v) (tmpl_erase T)
  end.

Fixpoint vtype_erase vty :=
  match vty with
  | BTyUnit => TyUnit
  | BTyInt => TyInt
  | BTyEmpty => TyEmpty
  | BTySum A B => TySum (vtype_erase A) (vtype_erase B)
  | BTyProd A B => TyProd (vtype_erase A) (vtype_erase B)
  | BTyList A => TyList (vtype_erase A)
  | BTyFun A C => TyFun (vtype_erase A) (ctype_erase C)
  | BTyHandler C D => TyHandler (ctype_erase C) (ctype_erase D)
  end

with ctype_erase cty :=
  match cty with
  | BCTy A Σ E => CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)
  end

with sig_erase Σ :=
  match Σ with
  | BSigØ => SigØ
  | BSigU Σ op A B => SigU (sig_erase Σ) op (vtype_erase A) (vtype_erase B)
  end

with ctx_erase Γ :=
  match Γ with
  | BCtxØ => CtxØ
  | BCtxU Γ A => CtxU (ctx_erase Γ) (vtype_erase A)
  end

with tctx_erase Z :=
  match Z with
  | BTCtxØ => TCtxØ
  | BTCtxU Z A => TCtxU (tctx_erase Z) (vtype_erase A)
  end

with eqs_erase E :=
  match E with
  | BEqsØ => EqsØ
  | BEqsU E Γ Z T1 T2 =>
      EqsU (eqs_erase E) (ctx_erase Γ) (tctx_erase Z) 
        (tmpl_erase T1) (tmpl_erase T2)
  end.

(* ==================== Getters ==================== *)

Lemma erase_get_op_None Σ o :
  bidir_get_op_type Σ o = None -> get_op_type (sig_erase Σ) o = None.
Proof.
intro. induction Σ; simpl in *. auto.
destruct (o==o0); simpl; auto. discriminate.
Qed.

Lemma erase_get_op_Some Σ o A B:
  bidir_get_op_type Σ o = Some (A, B) -> 
  get_op_type (sig_erase Σ) o = Some (vtype_erase A, vtype_erase B).
Proof.
intro. induction Σ; simpl in *. discriminate.
destruct (o==o0); simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_get_vtype_None Γ n :
  bidir_get_vtype Γ n = None -> get_vtype (ctx_erase Γ) n = None.
Proof.
revert n. induction Γ; intros; simpl in *. auto.
destruct n; simpl; auto. discriminate.
Qed.

Lemma erase_get_vtype_Some Γ n A:
  bidir_get_vtype Γ n = Some A -> 
  get_vtype (ctx_erase Γ) n = Some (vtype_erase A).
Proof.
revert n. induction Γ; intros; simpl in *. discriminate.
destruct n; simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_get_ttype_None Z n :
  bidir_get_ttype Z n = None -> get_ttype (tctx_erase Z) n = None.
Proof.
revert n. induction Z; intros; simpl in *. auto.
destruct n; simpl; auto. discriminate.
Qed.

Lemma erase_get_ttype_Some Z n A:
  bidir_get_ttype Z n = Some A -> 
  get_ttype (tctx_erase Z) n = Some (vtype_erase A).
Proof.
revert n. induction Z; intros; simpl in *. discriminate.
destruct n; simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_has_eq E Γ Z T1 T2:
  bidir_has_eq E Γ Z T1 T2 -> 
  has_eq 
    (eqs_erase E) (ctx_erase Γ) (tctx_erase Z) 
    (tmpl_erase T1) (tmpl_erase T2).
Proof.
induction E; intros; simpl in *; destruct H.
+ left. inv H. inv H1. inv H0. auto.
+ right. auto.
Qed.

Lemma erase_get_case_None h op :
  bidir_get_case h op = None -> get_case (h_erase h) op = None.
Proof.
revert h. induction h; intros; simpl in *. auto.
destruct (op==o); simpl; auto. discriminate.
Qed.


(* ==================== Subtyping ==================== *)

Fixpoint erase_vsubtype A A' (orig: Bvsubtype A A') {struct orig}:
  vsubtype (vtype_erase A) (vtype_erase A')

with erase_csubtype C C'(orig: Bcsubtype C C') {struct orig}:
  csubtype (ctype_erase C) (ctype_erase C')

with erase_sig_subtype Σ Σ'(orig: Bsig_subtype Σ Σ') {struct orig}:
  sig_subtype (sig_erase Σ) (sig_erase Σ') 

with erase_eqs_subtype E E'(orig: Beqs_subtype E E') {struct orig}:
  eqs_subtype (eqs_erase E) (eqs_erase E') .

Proof.
all: destruct orig; simpl.
+ apply STyUnit.
+ apply STyInt.
+ apply STyEmpty.
+ apply STySum; auto.
+ apply STyProd; auto.
+ apply STyFun; auto.
+ apply STyHandler; auto.
+ apply STyCTy; auto.
+ apply STySigØ.
+ eapply STySigU; eauto. apply erase_get_op_Some. assumption.
+ apply STyEqsØ.
+ apply STyEqsU. auto. apply erase_has_eq. auto.
Qed.


(* ==================== Main ==================== *)

Lemma ctx_erase_unsimpl Γ A:
  CtxU (ctx_erase Γ) (vtype_erase A) = ctx_erase (BCtxU Γ A).
Proof. simpl. auto. Qed.


Fixpoint vcheck_has_vtype Γ v A (orig : vcheck Γ v A) {struct orig}:
  has_vtype (ctx_erase Γ) (v_erase v) (vtype_erase A)

with vsynth_has_vtype Γ v A (orig : vsynth Γ v A) {struct orig}:
  has_vtype (ctx_erase Γ) (v_erase v) (vtype_erase A)

with ccheck_has_ctype Γ c C (orig : ccheck Γ c C) {struct orig}:
  has_ctype (ctx_erase Γ) (c_erase c) (ctype_erase C)

with csynth_has_ctype Γ c C (orig : csynth Γ c C) {struct orig}:
  has_ctype (ctx_erase Γ) (c_erase c) (ctype_erase C)

with hcheck_has_htype Γ h Σ D (orig : hcheck Γ h Σ D) {struct orig}:
  has_htype (ctx_erase Γ) (h_erase h) (sig_erase Σ) (ctype_erase D)

with wf_bidir_vtype_is_wf A (orig: wf_bidir_vtype A) {struct orig}:
  wf_vtype (vtype_erase A)

with wf_bidir_ctype_is_wf C (orig: wf_bidir_ctype C) {struct orig}:
  wf_ctype (ctype_erase C)

with wf_bidir_sig_is_wf Σ (orig: wf_bidir_sig Σ) {struct orig}:
  wf_sig (sig_erase Σ)

with wf_bidir_eqs_is_wf E Σ (orig: wf_bidir_eqs E Σ) {struct orig}:
  wf_eqs (eqs_erase E) (sig_erase Σ)

with wf_bidir_ctx_is_wf Γ (orig: wf_bidir_ctx Γ) {struct orig}:
  wf_ctx (ctx_erase Γ)

with wf_bidir_tctx_is_wf Z (orig: wf_bidir_tctx Z) {struct orig}:
  wf_tctx (tctx_erase Z)

with wf_bidir_tmpl_is_wf Γ Z T Σ (orig: wf_bidir_tmpl Γ Z T Σ) {struct orig}:
  wf_t (ctx_erase Γ) (tctx_erase Z) (tmpl_erase T) (sig_erase Σ).

Proof.
{
destruct orig. destruct H1; apply TypeV; auto; simpl.
+ eapply TypeVSubsume. 2: apply erase_vsubtype; eauto. auto.
+ eapply TypeLeft. auto.
+ eapply TypeRight. auto.
+ eapply TypeNil.
+ eapply TypeFun. rewrite ctx_erase_unsimpl. auto.
+ eapply TypeHandler. rewrite ctx_erase_unsimpl. auto. auto.
  inv H0; inv H5; apply Respects; auto. apply RespectAlways.
}{
destruct orig. destruct H1.
6: simpl; auto.
all: apply TypeV; auto; simpl.
+ eapply TypeUnit.
+ eapply TypeInt.
+ eapply TypeVar. apply erase_get_vtype_Some. assumption.
+ eapply TypePair; auto.
+ eapply TypeCons; eauto. apply vcheck_has_vtype in H2. auto.
}{
destruct orig. destruct H1; apply TypeC; auto; simpl.
+ eapply TypeCSubsume. 2: apply erase_csubtype; eauto. auto.
+ eapply TypeSumMatch.
  - assert (TySum (vtype_erase A) (vtype_erase B) = vtype_erase (BTySum A B)).
    simpl. auto. rewrite H4. auto.
  - rewrite ctx_erase_unsimpl. auto.
  - rewrite ctx_erase_unsimpl. auto.
+ eapply TypeListMatch; 
  assert (TyList (vtype_erase A) = vtype_erase (BTyList A)) by (simpl; auto).
  - rewrite H4. auto.
  - auto.
  - rewrite ctx_erase_unsimpl, H4, ctx_erase_unsimpl. auto.
+ eapply TypeDo.
  all: assert (forall A,
      CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (BCTy A Σ E))
      by (intro; simpl; reflexivity).
  - rewrite H3. eauto.
  - rewrite ctx_erase_unsimpl, H3. auto.
+ eapply TypeOp.
  - apply erase_get_op_Some. eauto.
  - eauto.
  - rewrite ctx_erase_unsimpl. assert (forall A,
      CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (BCTy A Σ E))
      by (intro; simpl; reflexivity).
    rewrite H4. auto.
}{
destruct orig. destruct H1; auto.
6: simpl; auto.
all: apply TypeC; simpl; auto.
all: assert (forall A Σ E,
  CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (BCTy A Σ E))
  as CTy_unsimpl by (intro; simpl; reflexivity).
+ assert (SigØ = sig_erase BSigØ) by (simpl; auto).
  assert (EqsØ = eqs_erase BEqsØ) by (simpl; auto).
  rewrite H2, H3, CTy_unsimpl. auto.
+ eapply TypeRet. auto.
+ eapply TypeProdMatch.
  - assert (TyProd (vtype_erase A) (vtype_erase B) = vtype_erase (BTyProd A B)).
    simpl. auto. rewrite H3. auto.
  - rewrite ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
+ eapply TypeApp.
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (BTyFun A C)).
    simpl. auto. rewrite H3. auto.
  - auto.
+ eapply TypeHandle.
  - assert (TyHandler (ctype_erase C) (ctype_erase D) 
      = vtype_erase (BTyHandler C D)). simpl. auto. rewrite H3. auto.
  - auto.
+ eapply TypeLetRec.
  instantiate (1:= (ctype_erase C)). instantiate (1:= (vtype_erase A)).
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (BTyFun A C)).
    simpl. auto. rewrite H3, ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (BTyFun A C)).
    simpl. auto. rewrite H3, ctx_erase_unsimpl. auto.
}{
destruct orig. destruct H2; apply TypeH; auto; simpl.
+ apply TypeCasesØ.
+ apply TypeCasesU.
  - auto.
  - assert (TyFun (vtype_erase B_op) (ctype_erase D) 
      = vtype_erase (BTyFun B_op D)) by (simpl; reflexivity).
    rewrite H5, ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
}{
induction orig; simpl.
+ apply WfTyUnit.
+ apply WfTyInt.
+ apply WfTyEmpty.
+ apply WfTySum; auto.
+ apply WfTyProd; auto.
+ apply WfTyList. auto.
+ apply WfTyFun; auto.
+ apply WfTyHandler; auto.
}{
destruct orig. simpl. apply WfCTy; auto.
}{
destruct orig; simpl.
+ apply WfSigØ.
+ apply WfSigU; auto. apply erase_get_op_None. assumption.
}{
destruct orig; simpl. apply WfEqsØ. apply WfEqsU; auto.
}{
destruct orig; simpl. apply WfCtxØ. apply WfCtxU; auto.
}{
destruct orig; simpl. apply WfTCtxØ. apply WfTCtxU; auto.
}{
destruct orig; simpl.
+ eapply WfTApp; eauto. apply erase_get_ttype_Some. assumption.
+ eapply WfTAbsurd. assert (TyEmpty = (vtype_erase BTyEmpty)) by (simpl; auto).
  rewrite H0. eapply vcheck_has_vtype. assumption.
+ eapply WfTProdMatch. 
  assert (TyProd (vtype_erase A) (vtype_erase B) = vtype_erase (BTyProd A B)).
  simpl. reflexivity. erewrite H0. auto. 
  rewrite ctx_erase_unsimpl. rewrite ctx_erase_unsimpl. auto.
+ eapply WfTSumMatch. 
  assert (TySum (vtype_erase A) (vtype_erase B) = vtype_erase (BTySum A B)).
  simpl. reflexivity. erewrite H0. auto.
  all: rewrite ctx_erase_unsimpl; auto.
+ eapply WfTListMatch; 
  assert (TyList (vtype_erase A) = vtype_erase (BTyList A)) by (simpl; auto).
  - rewrite H0. auto.
  - auto.
  - rewrite ctx_erase_unsimpl, H0, ctx_erase_unsimpl. auto.
+ eapply WfTDo. apply csynth_has_ctype in H. simpl in H. eauto.
  rewrite ctx_erase_unsimpl. apply wf_bidir_tmpl_is_wf. auto.
+ eapply WfTOp. apply erase_get_op_Some. eauto. auto.
  rewrite ctx_erase_unsimpl; auto.
}
Qed.
