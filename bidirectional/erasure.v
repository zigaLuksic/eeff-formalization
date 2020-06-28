(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\bidirectional". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\bidirectional".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Require Import syntax syntax_lemmas bidirectional declarational subtyping_lemmas.


Ltac inv H := inversion H; clear H; subst.

Fixpoint v_erase v :=
  match v with
  | βVar id => Var id
  | βUnit => Unit
  | βInt n => Int n
  | βInl v => Inl (v_erase v)
  | βInr v => Inr (v_erase v)
  | βPair v1 v2 => Pair (v_erase v1) (v_erase v2)
  | βListNil => ListNil
  | βListCons v vs => ListCons (v_erase v) (v_erase vs)
  | βFun c => Fun (c_erase c)
  | βHandler c_r h => Handler (c_erase c_r) (h_erase h)
  | βAnnV v ty => v_erase v
  end

with c_erase c :=
  match c with
  | βRet v => Ret (v_erase v)
  | βAbsurd v => Absurd (v_erase v)
  | βΠMatch v c => ΠMatch (v_erase v) (c_erase c)
  | βΣMatch v c1 c2 => ΣMatch (v_erase v) (c_erase c1) (c_erase c2)
  | βListMatch v c1 c2 => ListMatch (v_erase v) (c_erase c1) (c_erase c2)
  | βApp v1 v2 => App (v_erase v1) (v_erase v2)
  | βOp op v c => Op op (v_erase v) (c_erase c)
  | βLetRec ty c1 c2 => LetRec (c_erase c1) (c_erase c2)
  | βDoBind c1 c2 => DoBind (c_erase c1) (c_erase c2)
  | βHandle v c => Handle (v_erase v) (c_erase c)
  | βAnnC c ty => c_erase c
  end

with h_erase h :=
  match h with
  | βCasesØ => CasesØ
  | βCasesU h op c => CasesU (h_erase h) op (c_erase c) 
  end

with vtype_erase vty :=
  match vty with
  | βTyUnit => TyUnit
  | βTyInt => TyInt
  | βTyØ => TyØ
  | βTyΣ A B => TyΣ (vtype_erase A) (vtype_erase B)
  | βTyΠ A B => TyΠ (vtype_erase A) (vtype_erase B)
  | βTyList A => TyList (vtype_erase A)
  | βTyFun A C => TyFun (vtype_erase A) (ctype_erase C)
  | βTyHandler C D => TyHandler (ctype_erase C) (ctype_erase D)
  end

with ctype_erase cty :=
  match cty with
  | βCTy A Σ E => CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)
  end

with sig_erase Σ :=
  match Σ with
  | βSigØ => SigØ
  | βSigU Σ op A B => SigU (sig_erase Σ) op (vtype_erase A) (vtype_erase B)
  end

with ctx_erase Γ :=
  match Γ with
  | βCtxØ => CtxØ
  | βCtxU Γ A => CtxU (ctx_erase Γ) (vtype_erase A)
  end

with tctx_erase Z :=
  match Z with
  | βTCtxØ => TCtxØ
  | βTCtxU Z A => TCtxU (tctx_erase Z) (vtype_erase A)
  end

with tmpl_erase T :=
  match T with
  | βTApp z v => TApp z (v_erase v)
  | βTAbsurd v => TAbsurd (v_erase v)
  | βTΠMatch v T => TΠMatch (v_erase v) (tmpl_erase T)
  | βTΣMatch v T1 T2 => 
      TΣMatch (v_erase v) (tmpl_erase T1) (tmpl_erase T2)
  | βTListMatch v T1 T2 => 
      TListMatch (v_erase v) (tmpl_erase T1) (tmpl_erase T2)
  | βTLetBind c T => TLetBind (c_erase c) (tmpl_erase T)
  | βTOp op v T => TOp op (v_erase v) (tmpl_erase T)
  end

with eqs_erase E :=
  match E with
  | βEqsØ => EqsØ
  | βEqsU E Γ Z T1 T2 =>
      EqsU (eqs_erase E) (ctx_erase Γ) (tctx_erase Z) 
        (tmpl_erase T1) (tmpl_erase T2)
  end.

(* ==================== Getters ==================== *)

Lemma erase_get_op_None Σ o :
  get_op_βtype Σ o = None -> get_op_type (sig_erase Σ) o = None.
Proof.
intro. induction Σ; simpl in *. auto.
destruct (o==o0); simpl; auto. discriminate.
Qed.

Lemma erase_get_op_Some Σ o A B:
  get_op_βtype Σ o = Some (A, B) -> 
  get_op_type (sig_erase Σ) o = Some (vtype_erase A, vtype_erase B).
Proof.
intro. induction Σ; simpl in *. discriminate.
destruct (o==o0); simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_get_vtype_None Γ n :
  get_βvtype Γ n = None -> get_vtype (ctx_erase Γ) n = None.
Proof.
revert n. induction Γ; intros; simpl in *. auto.
destruct n; simpl; auto. discriminate.
Qed.

Lemma erase_get_vtype_Some Γ n A:
  get_βvtype Γ n = Some A -> 
  get_vtype (ctx_erase Γ) n = Some (vtype_erase A).
Proof.
revert n. induction Γ; intros; simpl in *. discriminate.
destruct n; simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_get_ttype_None Z n :
  get_βttype Z n = None -> get_ttype (tctx_erase Z) n = None.
Proof.
revert n. induction Z; intros; simpl in *. auto.
destruct n; simpl; auto. discriminate.
Qed.

Lemma erase_get_ttype_Some Z n A:
  get_βttype Z n = Some A -> 
  get_ttype (tctx_erase Z) n = Some (vtype_erase A).
Proof.
revert n. induction Z; intros; simpl in *. discriminate.
destruct n; simpl; auto. inv H. reflexivity.
Qed.

Lemma erase_has_eq E Γ Z T1 T2:
  has_βeq E Γ Z T1 T2 -> 
  has_eq 
    (eqs_erase E) (ctx_erase Γ) (tctx_erase Z) 
    (tmpl_erase T1) (tmpl_erase T2).
Proof.
induction E; intros; simpl in *; destruct H.
+ left. inv H. inv H1. inv H0. auto.
+ right. auto.
Qed.

Lemma erase_get_case_None h op :
  get_βcase h op = None -> get_case (h_erase h) op = None.
Proof.
revert h. induction h; intros; simpl in *. auto.
destruct (op==o); simpl; auto. discriminate.
Qed.


(* ==================== Subtyping ==================== *)

Fixpoint erase_vsubtype A A' (orig: βvsubtype A A') {struct orig}:
  vsubtype (vtype_erase A) (vtype_erase A')

with erase_csubtype C C'(orig: βcsubtype C C') {struct orig}:
  csubtype (ctype_erase C) (ctype_erase C')

with erase_sig_subtype Σ Σ'(orig: βsig_subtype Σ Σ') {struct orig}:
  sig_subtype (sig_erase Σ) (sig_erase Σ') 

with erase_eqs_subtype E E'(orig: βeqs_subtype E E') {struct orig}:
  eqs_subtype (eqs_erase E) (eqs_erase E') .

Proof.
all: destruct orig; simpl.
+ apply SubtypeUnit.
+ apply SubtypeInt.
+ apply SubtypeTyØ.
+ apply SubtypeTyΣ; auto.
+ apply SubtypeTyΠ; auto.
+ apply SubtypeTyFun; auto.
+ apply SubtypeTyHandler; auto.
+ apply SubtypeCTy; auto.
+ apply SubtypeSigØ.
+ eapply SubtypeSigU; eauto. apply erase_get_op_Some. assumption.
+ apply SubtypeEqsØ.
+ apply SubtypeEqsU. auto. apply erase_has_eq. auto.
Qed.


(* ==================== Main ==================== *)

Lemma ctx_erase_unsimpl Γ A:
  CtxU (ctx_erase Γ) (vtype_erase A) = ctx_erase (βCtxU Γ A).
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

with wf_βvtype_is_wf A (orig: wf_βvtype A) {struct orig}:
  wf_vtype (vtype_erase A)

with wf_βctype_is_wf C (orig: wf_βctype C) {struct orig}:
  wf_ctype (ctype_erase C)

with wf_βsig_is_wf Σ (orig: wf_βsig Σ) {struct orig}:
  wf_sig (sig_erase Σ)

with wf_βeqs_is_wf E Σ (orig: wf_βeqs E Σ) {struct orig}:
  wf_eqs (eqs_erase E) (sig_erase Σ)

with wf_βctx_is_wf Γ (orig: wf_βctx Γ) {struct orig}:
  wf_ctx (ctx_erase Γ)

with wf_βtctx_is_wf Z (orig: wf_βtctx Z) {struct orig}:
  wf_tctx (tctx_erase Z)

with wf_βtmpl_is_wf Γ Z T Σ (orig: wf_βtmpl Γ Z T Σ) {struct orig}:
  wf_t (ctx_erase Γ) (tctx_erase Z) (tmpl_erase T) (sig_erase Σ).

Proof.
{
destruct orig. destruct H1; apply TypeV; auto; simpl.
+ eapply TypeVSubtype. 2: apply erase_vsubtype; eauto. auto.
+ eapply TypeInl. auto.
+ eapply TypeInr. auto.
+ eapply TypeListNil.
+ eapply TypeFun. rewrite ctx_erase_unsimpl. auto.
+ eapply TypeHandler. rewrite ctx_erase_unsimpl. auto. auto.
}{
destruct orig. destruct H1.
6: simpl; auto.
all: apply TypeV; auto; simpl.
+ eapply TypeUnit.
+ eapply TypeInt.
+ eapply TypeVar. apply erase_get_vtype_Some. assumption.
+ eapply TypePair; auto.
+ eapply TypeListCons; eauto. apply vcheck_has_vtype in H2. auto.
}{
destruct orig. destruct H1; apply TypeC; auto; simpl.
+ eapply TypeCSubtype. 2: apply erase_csubtype; eauto. auto.
+ eapply TypeΣMatch.
  - assert (TyΣ (vtype_erase A) (vtype_erase B) = vtype_erase (βTyΣ A B)).
    simpl. auto. rewrite H4. auto.
  - rewrite ctx_erase_unsimpl. auto.
  - rewrite ctx_erase_unsimpl. auto.
+ eapply TypeListMatch; 
  assert (TyList (vtype_erase A) = vtype_erase (βTyList A)) by (simpl; auto).
  - rewrite H4. auto.
  - auto.
  - rewrite ctx_erase_unsimpl, H4, ctx_erase_unsimpl. auto.
+ eapply TypeDoBind.
  all: assert (forall A,
      CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (βCTy A Σ E))
      by (intro; simpl; reflexivity).
  - rewrite H3. eauto.
  - rewrite ctx_erase_unsimpl, H3. auto.
+ eapply TypeOp.
  - apply erase_get_op_Some. eauto.
  - eauto.
  - rewrite ctx_erase_unsimpl. assert (forall A,
      CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (βCTy A Σ E))
      by (intro; simpl; reflexivity).
    rewrite H4. auto.
}{
destruct orig. destruct H1; auto.
6: simpl; auto.
all: apply TypeC; simpl; auto.
all: assert (forall A Σ E,
  CTy (vtype_erase A) (sig_erase Σ) (eqs_erase E)=ctype_erase (βCTy A Σ E))
  as CTy_unsimpl by (intro; simpl; reflexivity).
+ assert (SigØ = sig_erase βSigØ) by (simpl; auto).
  assert (EqsØ = eqs_erase βEqsØ) by (simpl; auto).
  rewrite H2, H3, CTy_unsimpl. auto.
+ eapply TypeRet. auto.
+ eapply TypeΠMatch.
  - assert (TyΠ (vtype_erase A) (vtype_erase B) = vtype_erase (βTyΠ A B)).
    simpl. auto. rewrite H3. auto.
  - rewrite ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
+ eapply TypeApp.
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (βTyFun A C)).
    simpl. auto. rewrite H3. auto.
  - auto.
+ eapply TypeHandle.
  - assert (TyHandler (ctype_erase C) (ctype_erase D) 
      = vtype_erase (βTyHandler C D)). simpl. auto. rewrite H3. auto.
  - auto.
+ eapply TypeLetRec.
  instantiate (1:= (ctype_erase C)). instantiate (1:= (vtype_erase A)).
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (βTyFun A C)).
    simpl. auto. rewrite H3, ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
  - assert (TyFun (vtype_erase A) (ctype_erase C) = vtype_erase (βTyFun A C)).
    simpl. auto. rewrite H3, ctx_erase_unsimpl. auto.
}{
destruct orig. destruct H2; apply TypeH; auto; simpl.
+ apply TypeCasesØ.
+ apply TypeCasesU.
  - apply erase_get_case_None. assumption.
  - auto.
  - assert (TyFun (vtype_erase B_op) (ctype_erase D) 
      = vtype_erase (βTyFun B_op D)) by (simpl; reflexivity).
    rewrite H5, ctx_erase_unsimpl, ctx_erase_unsimpl. auto.
}{
induction orig; simpl.
+ apply WfTyUnit.
+ apply WfTyInt.
+ apply WfTyEmpty.
+ apply WfTyΣ; auto.
+ apply WfTyΠ; auto.
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
+ eapply WfTAbsurd. assert (TyØ = (vtype_erase βTyØ)) by (simpl; auto).
  rewrite H0. eapply vcheck_has_vtype. assumption.
+ eapply WfTΠMatch. 
  assert (TyΠ (vtype_erase A) (vtype_erase B) = vtype_erase (βTyΠ A B)).
  simpl. reflexivity. erewrite H0. auto. 
  rewrite ctx_erase_unsimpl. rewrite ctx_erase_unsimpl. auto.
+ eapply WfTΣMatch. 
  assert (TyΣ (vtype_erase A) (vtype_erase B) = vtype_erase (βTyΣ A B)).
  simpl. reflexivity. erewrite H0. auto.
  all: rewrite ctx_erase_unsimpl; auto.
+ eapply WfTListMatch; 
  assert (TyList (vtype_erase A) = vtype_erase (βTyList A)) by (simpl; auto).
  - rewrite H0. auto.
  - auto.
  - rewrite ctx_erase_unsimpl, H0, ctx_erase_unsimpl. auto.
+ eapply WfTLetBind. apply csynth_has_ctype in H. simpl in H. eauto.
  rewrite ctx_erase_unsimpl. apply wf_βtmpl_is_wf. auto.
+ eapply WfTOp. apply erase_get_op_Some. eauto. auto.
  rewrite ctx_erase_unsimpl; auto.
}
Qed.
