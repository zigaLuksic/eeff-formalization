(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".

Require Export syntax declarational wf_lemmas.


Ltac inv H := inversion H; clear H; subst.
Ltac aconstructor := constructor; auto.


(* ==================== Sig and Eqs Properties ==================== *)

Lemma sig_subtype_get_Some Σ Σ' op A B :
  sig_subtype Σ Σ' -> get_op_type Σ op = Some (A, B) -> exists A' B', 
  get_op_type Σ' op = Some (A', B') /\ vsubtype A A' /\ vsubtype B' B.
Proof.
intros sty gets. induction sty; simpl in gets. discriminate.
destruct (op == op0).
- inv gets. exists A'. exists B'. auto.
- apply IHsty in gets. assumption.
Qed.


Lemma sig_subtype_extend Σ Σ' op A B :
  sig_subtype Σ Σ' -> wf_sig (SigU Σ' op A B) -> sig_subtype Σ (SigU Σ' op A B).
Proof.
intros. induction H.
+ apply SubtypeSigØ.
+ eapply SubtypeSigU; eauto. inv H0. simpl.
  destruct (op0 == op); auto. rewrite e in *. rewrite H1 in H9. discriminate.
Qed.


Lemma sig_subtype_empty Σ : 
  sig_subtype Σ SigØ -> Σ = SigØ.
Proof.
intro subty. inv subty. reflexivity. simpl in *. discriminate.
Qed.


Lemma eqs_subtype_extend E E' Σ Γ Z T1 T2 :
  eqs_subtype E E' -> wf_eqs (EqsU E' Γ Z T1 T2) Σ ->
  eqs_subtype E (EqsU E' Γ Z T1 T2).
Proof.
intros. induction H.
+ apply SubtypeEqsØ.
+ eapply SubtypeEqsU. auto. simpl. right. assumption.
Qed.


Lemma eqs_subtype_contains E E' Γ Z T1 T2 :
  eqs_subtype E E' -> has_eq E Γ Z T1 T2 -> 
  has_eq E' Γ Z T1 T2.
Proof.
intros sty gets. induction sty; simpl in gets; destruct gets; auto.
destruct H0 as [a [b [c ]]]. subst. assumption.
Qed.

Lemma eqs_subtype_empty E E': 
  eqs_subtype E E' -> E' = EqsØ -> E = EqsØ.
Proof.
intros subty eq. induction subty. auto. subst. simpl in H. destruct H.
Qed.

(* ==================== Reflexivity and Transitivity ==================== *)

Lemma vsubtype_refl v : wf_vtype v -> vsubtype v v
with csubtype_refl c : wf_ctype c -> csubtype c c
with sig_subtype_refl Σ : wf_sig Σ -> sig_subtype Σ Σ
with eqs_subtype_refl E Σ : wf_eqs E Σ -> eqs_subtype E E
with ctx_subtype_refl Γ : wf_ctx Γ -> ctx_subtype Γ Γ.
Proof.
{intros; destruct v; inv H.
+ apply SubtypeUnit.
+ apply SubtypeInt.
+ apply SubtypeTyØ.
+ apply SubtypeTyΣ; auto.
+ apply SubtypeTyΠ; auto.
+ apply SubtypeTyFun; auto.
+ apply SubtypeTyHandler; auto. }
{
 destruct c. intros. inv H. apply SubtypeCTy; eauto. }
{ 
intros; induction Σ.
+ apply SubtypeSigØ.
+ eapply SubtypeSigU; inv H; eauto.
  - apply sig_subtype_extend. auto. apply WfSigU; auto.
  - simpl. destruct (o==o); try destruct n; auto.
}{induction E; intros.
+ apply SubtypeEqsØ.
+ apply SubtypeEqsU. inv H. eapply eqs_subtype_extend; auto. 
  - apply WfEqsU; eauto.
  - simpl. left. auto.
}
{clear csubtype_refl sig_subtype_refl eqs_subtype_refl ctx_subtype_refl.
induction Γ; intros.
apply SubtypeCtxØ.
apply SubtypeCtxU; inv H; auto.
}
Qed.


Fixpoint eqs_subtype_trans E1 E2 E3 (E12 : eqs_subtype E1 E2) {struct E12} : 
  eqs_subtype E2 E3 -> eqs_subtype E1 E3.
Proof.
intros E23. destruct E12.
apply SubtypeEqsØ.
eapply SubtypeEqsU; eauto; eapply eqs_subtype_contains; eauto.
Qed.


(* Weird notation for SPEED! *)
Fixpoint vsubtype_trans A1 A2 A3 
  (A12 : vsubtype A1 A2) {struct A12} : vsubtype A2 A3 -> 
  vsubtype A1 A3
with vsubtype_trans_rev A1 A2 A3
  (A21 : vsubtype A2 A1) {struct A21} : vsubtype A3 A2 -> 
  vsubtype A3 A1
with csubtype_trans C1 C2 C3
  (C12 : csubtype C1 C2) {struct C12} : csubtype C2 C3 -> 
  csubtype C1 C3
with csubtype_trans_rev C1 C2 C3 
  (C21 : csubtype C2 C1) {struct C21} : csubtype C3 C2 -> 
  csubtype C3 C1
with sig_subtype_trans Σ1 Σ2 Σ3 
  (S12 : sig_subtype Σ1 Σ2) {struct S12} : sig_subtype Σ2 Σ3 -> 
  sig_subtype Σ1 Σ3
with sig_subtype_trans_rev Σ1 Σ2 Σ3
  (S21 : sig_subtype Σ2 Σ1) {struct S21} : sig_subtype Σ3 Σ2 -> 
  sig_subtype Σ3 Σ1
with get_op_trans op A' A B B' Σ1 Σ2 (S12 : sig_subtype Σ1 Σ2) {struct S12} :
  get_op_type Σ1 op = Some (A', B') -> vsubtype A A' -> vsubtype B' B ->
  exists A'' B'', 
  get_op_type Σ2 op = Some (A'', B'') /\ vsubtype A A'' /\ vsubtype B'' B.
Proof.
{
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros A23; destruct A12; try assumption; inv A23. 
+ apply SubtypeTyΣ; eauto.
+ apply SubtypeTyΠ; eauto.
+ apply SubtypeTyFun.
  - eapply vsubtype_trans_rev; eauto. 
  - eapply csubtype_trans; eauto.
+ apply SubtypeTyHandler.
  - eapply csubtype_trans_rev; eauto. 
  - eapply csubtype_trans; eauto.
}{
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros A32; destruct A21; try assumption; inv A32. 
+ apply SubtypeTyΣ; eapply vsubtype_trans_rev; eauto.
+ apply SubtypeTyΠ; eapply vsubtype_trans_rev; eauto.
+ apply SubtypeTyFun.
  - eapply vsubtype_trans; eauto.
  - eapply csubtype_trans_rev; eauto.
+ apply SubtypeTyHandler.
  - eapply csubtype_trans; eauto.
  - eapply csubtype_trans_rev; eauto.
}{
clear vsubtype_trans_rev csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans_rev get_op_trans.
intros C23; destruct C12. inv C23. apply SubtypeCTy.
- eapply vsubtype_trans; eauto.
- eapply sig_subtype_trans; eauto.
- eapply eqs_subtype_trans; eauto.
}{
clear vsubtype_trans csubtype_trans csubtype_trans.
clear sig_subtype_trans get_op_trans.
intros C32; destruct C21. inv C32. apply SubtypeCTy.
- eapply vsubtype_trans_rev; eauto.
- eapply sig_subtype_trans_rev; eauto.
- eapply eqs_subtype_trans; eauto.
}{
clear csubtype_trans csubtype_trans_rev sig_subtype_trans_rev.
intros S23. destruct S12.
{ apply SubtypeSigØ. }
apply (sig_subtype_get_Some Σ' Σ3) in H as H'.
destruct H' as [A'' [B'' [g]]]. eapply SubtypeSigU.
2 : exact g. all: try assumption.
+ eapply sig_subtype_trans; eauto.
+ clear sig_subtype_trans vsubtype_trans_rev.
  destruct H2. eapply vsubtype_trans; eauto.
+ clear sig_subtype_trans vsubtype_trans.
  destruct H2. eapply vsubtype_trans_rev; eauto.
}{
clear csubtype_trans csubtype_trans_rev sig_subtype_trans.
intros S32. destruct S21.
{ apply sig_subtype_empty in S32. subst. apply SubtypeSigØ. }
induction Σ3.
{ apply SubtypeSigØ. }
inv S32. simpl in *. destruct (o==op).
+ inv H8. eapply SubtypeSigU. auto. eauto.
  - eapply vsubtype_trans_rev; eauto.
  - eapply vsubtype_trans; eauto.
+ eapply get_op_trans in H8 as gets'.
  2:exact S21. 2:exact H9. 2:exact H10.
  destruct gets' as [A'' [B'' [gets' [styA'']]]].
  eapply SubtypeSigU; eauto.
}{
clear csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros. revert H. induction S12; intros gets; simpl in *. discriminate.
destruct (op==op0). 2: auto. inv gets.
exists A'0. exists B'0. aconstructor. constructor.
- eapply vsubtype_trans_rev; eauto.
- eapply vsubtype_trans; eauto.
}
Qed.

(* ==================== Context Properties ==================== *)

Fixpoint ctx_subtype_get Γ Γ' A num (csty : ctx_subtype Γ Γ') {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A A'.
Proof.
revert num. induction csty. clear ctx_subtype_get.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num; eauto.
  clear IHcsty. simpl in *. inv get. exists A'. auto.
Qed.


Fixpoint ctx_subtype_get_rev Γ Γ' A num (csty : ctx_subtype Γ' Γ) {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A' A.
Proof.
revert num. induction csty. clear ctx_subtype_get_rev.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num; eauto.
  clear IHcsty. simpl in *. inv get. exists A0. auto.
Qed.


Lemma ctx_subtype_join_ctxs Γ1 Γ1' Γ2 Γ2':
  ctx_subtype Γ1 Γ1' -> ctx_subtype Γ2 Γ2' ->
  ctx_subtype (join_ctxs Γ1 Γ2) (join_ctxs Γ1' Γ2').
Proof.
intros sty1 sty2. induction sty2; auto. apply SubtypeCtxU; assumption. 
Qed.


Lemma ctx_subtype_join_ctx_tctx Γ Γ' Z D:
  ctx_subtype Γ Γ' -> wf_tctx Z -> wf_ctype D ->
  ctx_subtype (join_ctx_tctx Γ Z D) (join_ctx_tctx Γ' Z D).
Proof.
intros sty wfZ wfD. induction Z; auto.
inv wfZ. apply SubtypeCtxU. auto. apply vsubtype_refl. apply WfTyFun; auto. 
Qed.


Lemma ctx_subtype_len Γ Γ':
  ctx_subtype Γ Γ' -> ctx_len Γ = ctx_len Γ'.
Proof. 
intro sty. induction sty; simpl; auto. 
Qed. 


Lemma ctx_subtype_insert Γ A Γ' i: 
  wf_ctx Γ' -> wf_ctx Γ -> wf_vtype A -> ctx_subtype Γ' (ctx_insert Γ A i) ->
  exists Γ'' A', Γ' = ctx_insert Γ'' A' i /\ vsubtype A' A 
    /\ wf_vtype A' /\ ctx_subtype Γ'' Γ.
Proof.
revert Γ A i. induction Γ'; intros Γ A i wfg' wfg wfA sty. 
* inv sty. exists Γ. exists A. aconstructor. constructor.
  apply vsubtype_refl. assumption. destruct Γ. aconstructor. apply SubtypeCtxØ.
  simpl in H. destruct i; discriminate.
* inv sty. destruct i.
  + assert (forall Γ A, ctx_insert Γ A 0 = CtxU Γ A).
    {intros. destruct Γ0; simpl; auto. }
    rewrite H in H1. inv H1. exists Γ'. exists v. inv wfg'. auto.
  + destruct Γ. simpl in *. discriminate.
    assert (forall Γ A A', 
      ctx_insert (CtxU Γ A') A (S i) = CtxU (ctx_insert Γ A i) A').
    {intros. destruct Γ0; simpl; auto. }
    rewrite H in H1. inv H1. inv wfg'. inv wfg. 
    apply IHΓ' in H2; auto. destruct H2 as [Γ''[A'[ins[sty]]]].
    exists (CtxU Γ'' v). exists A'. constructor. rewrite H. f_equal. auto.
    aconstructor. destruct H0. aconstructor. apply SubtypeCtxU; auto.
Qed.



Lemma ctx_subtype_remove Γ Γ' i: 
  wf_ctx Γ' -> wf_ctx Γ ->
  ctx_subtype Γ' (ctx_remove Γ i) ->
  exists Γ'', Γ' = ctx_remove Γ'' i /\ ctx_subtype Γ'' Γ /\ wf_ctx Γ''.
Proof.
revert Γ' i. induction Γ; intros Γ' i wfg' wfg sty.
+  simpl in sty. destruct i; inv sty; exists CtxØ;
   aconstructor; constructor; apply SubtypeCtxØ || apply WfCtxØ. 
+ simpl in sty. destruct i.
  - exists (CtxU Γ' v). aconstructor. constructor. apply SubtypeCtxU. auto.
    all: inv wfg. apply vsubtype_refl. assumption. apply WfCtxU; auto.
  - inv sty. apply IHΓ in H2. all: try (inv wfg; inv wfg'; assumption).
    destruct H2 as [Γ''[eq[wf]]]. subst. exists (CtxU Γ'' A).
    aconstructor. constructor. apply SubtypeCtxU; auto.
    apply WfCtxU. assumption. inv wfg'. assumption.
Qed.



Fixpoint ctx_subtype_vtype Γ Γ' v A (types : has_vtype Γ v A) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ  -> has_vtype Γ' v A

with ctx_subtype_ctype Γ Γ' c C (types : has_ctype Γ c C ) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_ctype Γ' c C

with ctx_subtype_htype Γ Γ' h Σ D (types : has_htype Γ h Σ D) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_htype Γ' h Σ D

with ctx_subtype_respects Γ Γ' h Σ D E (r : respects Γ h Σ D E) {struct r}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> respects Γ' h Σ D E

with ctx_subtype_veq Γ Γ' A v1 v2 (equals : veq A Γ v1 v2) {struct equals}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> veq A Γ' v1 v2

with ctx_subtype_ceq Γ Γ' C c1 c2 (equals : ceq C Γ c1 c2) {struct equals}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> ceq C Γ' c1 c2.
Proof.
{
clear ctx_subtype_veq ctx_subtype_ceq.
intros wf ctxsty.
destruct types. induction H1; apply TypeV; try assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply (ctx_subtype_get_rev _ _ A n) in ctxsty.
  destruct ctxsty as [A' [gets]]. 2: assumption. 
  eapply TypeVSubtype. 2: eauto.
  apply TypeV. assumption. apply get_vtype_wf in gets as wfA'; eauto.
  apply TypeVar. assumption.
+ apply TypePair; apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeInl. apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeInr. apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeFun. eapply ctx_subtype_ctype; inv H0. eauto.
  - apply WfCtxU; assumption.
  - apply SubtypeCtxU. assumption. apply vsubtype_refl. assumption.
+ apply TypeHandler. eapply ctx_subtype_ctype; inv H0; inv H6. eauto.
  - apply WfCtxU; assumption.
  - apply SubtypeCtxU. assumption. apply vsubtype_refl. assumption.
  - eapply (ctx_subtype_htype Γ Γ'); assumption.
  - eapply ctx_subtype_respects; eauto.
+ eapply TypeVSubtype. 2 : eauto.
  eapply (ctx_subtype_vtype Γ Γ'); assumption.
}{
clear ctx_subtype_respects ctx_subtype_veq ctx_subtype_ceq.
intros wf ctxsty.
destruct types. induction H1; apply TypeC; try assumption.
+ apply TypeRet. eauto.
+ apply TypeAbsurd. eauto.
+ eapply TypeΠMatch.
  - eapply (ctx_subtype_vtype Γ Γ'); eauto.
  - eapply ctx_subtype_ctype. exact H2. all: inv H2; inv H3; inv H7.
    * apply WfCtxU. apply WfCtxU. all: assumption.
    * apply SubtypeCtxU. apply SubtypeCtxU. assumption.
      all: apply vsubtype_refl; assumption.
+ eapply TypeΣMatch. eauto.
  - eapply ctx_subtype_ctype. exact H2. all: inv H2; inv H4. 
    * apply WfCtxU; assumption.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. assumption.
  - eapply ctx_subtype_ctype. exact H3. all: inv H3; inv H4. 
    * apply WfCtxU; assumption.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeDoBind.
  - eapply ctx_subtype_ctype; eauto.
  - inv H1. inv H4. eapply ctx_subtype_ctype. eauto.
    * apply WfCtxU; assumption.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeApp; eauto.
+ eapply TypeHandle; eauto.
+ eapply TypeLetRec.
  - eapply ctx_subtype_ctype. eauto. all: inv H2; inv H3.
    * apply WfCtxU. apply WfCtxU. eauto. inv H8. all: eauto.
    * apply SubtypeCtxU. apply SubtypeCtxU. exact ctxsty.
      apply vsubtype_refl. inv H8. assumption. apply vsubtype_refl. assumption.
  - eapply ctx_subtype_ctype. eauto. all: inv H2; inv H3.
    * apply WfCtxU; assumption.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeOp. eauto. eapply ctx_subtype_vtype; eauto.
  eapply ctx_subtype_ctype. exact H3. all: inv H3; inv H4.
  - apply WfCtxU; assumption.
  - apply SubtypeCtxU. assumption. apply vsubtype_refl. assumption.
+ eapply TypeCSubtype. 2: exact H2.
  eapply ctx_subtype_ctype. all: eauto.
}{
clear ctx_subtype_vtype ctx_subtype_respects ctx_subtype_veq ctx_subtype_ceq.
intros wf ctxsty.
destruct types. induction H2; apply TypeH; try assumption.
+ eapply TypeCasesØ.
+ eapply TypeCasesU. assumption.
  eapply ctx_subtype_htype. all: eauto.
  eapply ctx_subtype_ctype. eauto.
  all: inv H4; inv H5; inv H9.
  - apply WfCtxU. apply WfCtxU. all: assumption.
  - apply SubtypeCtxU. apply SubtypeCtxU. assumption.
    all: apply vsubtype_refl; assumption.
}{
clear ctx_subtype_vtype ctx_subtype_ctype ctx_subtype_htype ctx_subtype_veq.
intros wf ctxsty.
inv r. eapply Respects; auto. destruct H3.
+ eapply RespectEqsØ.
+ eapply RespectEqsU; eauto.
  eapply ctx_subtype_ceq. eauto.
  apply join_ctx_tctx_wf. apply join_ctxs_wf. all: inv H2; auto. 
  apply ctx_subtype_join_ctx_tctx. apply ctx_subtype_join_ctxs. 
  all: assumption || apply ctx_subtype_refl; assumption.
}{
clear ctx_subtype_vtype ctx_subtype_ctype ctx_subtype_htype.
intros wf ctxsty.
inv equals. destruct H1; apply Veq; auto.
+ apply VRefl. auto.
+ apply VSym. eauto.
+ eapply VTrans; eauto.
+ apply ctx_subtype_insert in ctxsty. destruct ctxsty as [Γ''[A''[is[s[w]]]]].
  subst. apply VInsert. eapply ctx_subtype_veq. all: eauto.
  - eapply ctx_insert_wf_rev. eauto.
  - eapply ctx_insert_wf_rev. eauto.
+ apply ctx_subtype_remove in ctxsty; auto. destruct ctxsty as [Γ''[eq[wfg]]].
  subst. apply VRemove; auto. eapply ctx_subtype_veq; eauto.
+ eapply EqPair; eauto.
}{
clear ctx_subtype_vtype ctx_subtype_ctype ctx_subtype_htype.
intros wf ctxsty.
inv equals. destruct H1; apply Ceq; auto.
+ apply CRefl. auto.
+ apply CSym. eauto.
+ eapply CTrans; eauto.
}
Qed.


(* ==================== Subtype Shapes ==================== *)

Lemma subtype_shape_empty A : vsubtype A TyØ -> A = TyØ.
Proof.
intro sty. inv sty. reflexivity.
Qed. 

Lemma subtype_shape_prod A B C : vsubtype C (TyΠ A B) -> 
  exists A' B', C = (TyΠ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists B0. auto.
Qed.

Lemma subtype_shape_prod_rev A B C : vsubtype (TyΠ A B) C -> 
  exists A' B', C = (TyΠ A' B') /\ vsubtype A A' /\ vsubtype B B'.
Proof.
intro orig. inv orig. exists A'. exists B'. auto.
Qed.

Lemma subtype_shape_sum A B C : vsubtype C (TyΣ A B) -> 
  exists A' B', C = (TyΣ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists B0. auto.
Qed.

Lemma subtype_shape_sum_rev A B C : vsubtype (TyΣ A B) C -> 
  exists A' B', C = (TyΣ A' B') /\ vsubtype A A' /\ vsubtype B B'.
Proof.
intro orig. inv orig. exists A'. exists B'. auto.
Qed.

Lemma subtype_shape_fun A B C : vsubtype C (TyFun A B) -> 
  exists A' B', C = (TyFun A' B') /\ vsubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists C0. auto.
Qed.

Lemma subtype_shape_fun_rev A B C : vsubtype (TyFun A B) C -> 
  exists A' B', C = (TyFun A' B') /\ vsubtype A' A /\ csubtype B B'.
Proof.
intro orig. inv orig. exists A'. exists C'. auto.
Qed.

Lemma subtype_shape_handler A B C : vsubtype C (TyHandler A B) -> 
  exists A' B', C = (TyHandler A' B') /\ csubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists C0. exists D. auto.
Qed.

Lemma subtype_shape_handler_rev A B C : vsubtype (TyHandler A B) C -> 
  exists A' B', C = (TyHandler A' B') /\ csubtype A' A /\ csubtype B B'.
Proof.
intro orig. inv orig. exists C'. exists D'. auto.
Qed.

Lemma subtype_shape_cty A Σ E C : csubtype C (CTy A Σ E) ->
  exists A' Σ' E', 
    C = CTy A' Σ' E' /\ vsubtype A' A /\ sig_subtype Σ' Σ /\ eqs_subtype E' E.
Proof.
intro orig. inv orig. exists A0. exists Σ0. exists E0. auto.
Qed.
  
Lemma subtype_shape_cty_rev A Σ E C : csubtype (CTy A Σ E) C ->
  exists A' Σ' E', C = 
    CTy A' Σ' E' /\ vsubtype A A' /\ sig_subtype Σ Σ' /\ eqs_subtype E E'.
Proof.
intro orig. inv orig. exists A'. exists Σ'. exists E'. auto.
Qed.

(* ==================== Template WF Subtyping ==================== *)

Lemma wf_t_subtype_sig Γ Γ' Z T Σ Σ':
  wf_t Γ Z T Σ -> sig_subtype Σ Σ' -> 
  ctx_subtype Γ' Γ -> wf_sig Σ' -> wf_ctx Γ' ->
  wf_t Γ' Z T Σ'.
Proof.
intros orig. revert Γ'. induction orig; intros Γ' sty cty wfs wfc.
+ eapply WfTApp. eapply ctx_subtype_vtype; eauto. assumption.
+ eapply WfTAbsurd. eapply ctx_subtype_vtype; eauto.
+ eapply WfTΠMatch. eapply ctx_subtype_vtype; eauto. inv H. inv H1.
  apply IHorig; auto. apply SubtypeCtxU. 
  apply SubtypeCtxU. 4: apply WfCtxU. 4: apply WfCtxU.
  all: assumption || apply vsubtype_refl; auto.
+ eapply WfTΣMatch. eapply ctx_subtype_vtype; eauto.  all: inv H; inv H1.
  apply IHorig1; auto. 3: apply IHorig2; auto.
  1: apply SubtypeCtxU. 4: apply SubtypeCtxU. 3: apply WfCtxU. 7: apply WfCtxU.
  all: assumption || apply vsubtype_refl; auto.
+ eapply sig_subtype_get_Some in H. 2: exact sty.
  destruct H as [A'[B'[gets'[Asty]]]].
  eapply WfTOp. eauto.
  - eapply ctx_subtype_vtype; eauto. apply TypeV.
    * inv H0. assumption.
    * apply get_op_type_wf in gets'. inv gets'. all: assumption.
    * eapply TypeVSubtype; eauto.
  - apply IHorig; auto.
    * apply SubtypeCtxU; auto.
    * apply get_op_type_wf in gets'. inv gets'. apply WfCtxU. all: assumption.
Qed.

Lemma wf_eqs_sig_subtype E Σ Σ':
  wf_eqs E Σ -> sig_subtype Σ Σ' -> wf_sig Σ' -> wf_eqs E Σ'.
Proof.
intros. induction H. apply WfEqsØ.
apply WfEqsU; auto. all: eapply wf_t_subtype_sig; eauto.
all: apply ctx_subtype_refl; auto.
Qed.

(* ==================== Respects Subtypes ==================== *)

Lemma has_eq_respects Γ h Σ D E Γ' Z T1 T2:
  respects Γ h Σ D E -> has_eq E Γ' Z T1 T2 ->
  ceq D (join_ctx_tctx (join_ctxs Γ Γ') Z D)
    (handle_t (ctx_len Γ') (tctx_len Z) h T1)
    (handle_t (ctx_len Γ') (tctx_len Z) h T2).
Proof.
intros r c. induction E; simpl in c; destruct c.
- destruct H as [a[b[c]]]. subst. inv r. inv H3. assumption.
- apply IHE. inv r. inv H4. all: assumption.
Qed.


Lemma respects_eqs_subtype Γ h Σ D E E':
  respects Γ h Σ D E -> wf_eqs E' Σ -> eqs_subtype E' E ->
  respects Γ h Σ D E'.
Proof.
intros. induction H1.
+ inv H; apply Respects; auto. apply RespectEqsØ.
+ apply Respects; try (inv H; assumption). 
  apply RespectEqsU. inv H0. auto. eapply has_eq_respects; eauto.
Qed.
  
(* ==================== Value Shapes ==================== *)

(* Var *)
Fixpoint shape_var_full Γ v x n A (orig : has_vtype Γ v A) {struct orig} :
  v = Var (x, n) -> 
  (exists A', get_vtype Γ n = Some A' /\ vsubtype A' A).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_var_full.
  exists A. inv same. aconstructor. apply vsubtype_refl. assumption.
+ subst. eapply shape_var_full in H1. clear shape_var_full. 2: reflexivity.
  destruct H1 as [A'' [gets]].
  exists A''. aconstructor. eapply vsubtype_trans; eauto.
Qed.


Lemma shape_var Γ x n A:
  has_vtype Γ (Var (x, n)) A -> 
  (exists A', get_vtype Γ n = Some A' /\ vsubtype A' A).
Proof.
intro orig. apply (shape_var_full _ _ x n A) in orig as shape; eauto.
Qed.


Lemma shape_var_ctx_empty id A:
  has_vtype CtxØ (Var id) A -> False.
Proof.
intro orig. destruct id as (x, n).
apply (shape_var_full _ _ x n A) in orig as shape. 
2: reflexivity. destruct shape as [A'[gets]]. simpl in gets. discriminate.
Qed.


(* Empty *)
Fixpoint shape_empty_full Γ v A (orig : has_vtype Γ v A) {struct orig} :
  A = TyØ -> (exists x n, v = Var (x, n)).
Proof.
intros samety.
destruct orig. destruct H1; try discriminate. eauto.
subst. apply subtype_shape_empty in H2. subst; eauto.
Qed.


Lemma shape_empty Γ v:
  has_vtype Γ v TyØ -> (exists x num, v = Var (x, num)).
Proof.
intro orig. apply (shape_empty_full _ _) in orig as shape; auto.
Qed.


(* Pair *)
Fixpoint shape_prod_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΠ A B ->
  (exists x n, v = Var (x, n)) \/
  (exists v1 v2, v = Pair v1 v2 /\ has_vtype Γ v1 A /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ left. eauto.
+ right. inv same. eauto.
+ rewrite same in H2. apply subtype_shape_prod in H2. 
  destruct H2 as [A'' [B'' [pity]]]. subst.
  apply (shape_prod_full _ _ A'' B'') in H1. clear shape_prod_full. 
  2: reflexivity. destruct H1. auto.
  right. destruct H1 as [v1 [v2]].
  exists v1. exists v2. destruct H1 as [s[vty1]]. destruct H2.
  aconstructor. inv H0. constructor; apply TypeV.
  all: assumption || eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_pair_full Γ v v1 v2 ty (orig : has_vtype Γ v ty) {struct orig} :
  v = Pair v1 v2 ->
  (exists A B, ty = TyΠ A B /\ has_vtype Γ v1 A /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_pair_full. exists A. exists B. inv same. auto.
+ subst. apply (shape_pair_full _ _ v1 v2) in H1. clear shape_pair_full. 
  2: reflexivity. destruct H1 as [A''[B''[ty[tyv1]]]]. subst.
  apply subtype_shape_prod_rev in H2. destruct H2 as [A'''[B'''[s[sty1]]]].
  exists A'''. exists B'''. subst. inv H0. aconstructor. constructor;
  apply TypeV; try assumption; eapply TypeVSubtype; eauto.
Qed.


Lemma shape_pair Γ v1 v2 A B :
  has_vtype Γ (Pair v1 v2) (TyΠ A B) ->  
  has_vtype Γ v1 A /\ has_vtype Γ v2 B.
Proof.
intro orig.
apply (shape_prod_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [x [n]]. discriminate.
+ destruct H as [v1' [v2' [same]]]. inv same. assumption.
Qed.


(* Sum *)
Fixpoint shape_sum_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΣ A B ->
  (exists x n, v = Var (x, n)) \/
  (exists v1, v = Inl v1 /\ has_vtype Γ v1 A) \/
  (exists v2, v = Inr v2 /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ left. eauto.
+ right. left. inv same. eauto.
+ right. right. inv same. eauto.
+ rewrite same in H2. apply subtype_shape_sum in H2. 
  destruct H2 as [A'' [B'' [sigty]]]. subst. inv H0. destruct H2. 
  apply (shape_sum_full _ _ A'' B'') in H1. clear shape_sum_full. 
  2: reflexivity. destruct H1. auto. right. do 3 destruct H1; subst.
  * left. exists x. aconstructor.
    apply TypeV; try assumption. eapply TypeVSubtype; eauto.
  * right. exists x. aconstructor.
    apply TypeV; try assumption. eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_inl_full Γ v A v' (orig : has_vtype Γ v A) {struct orig} :
  v = Inl v' ->
  (exists A' B', A = TyΣ A' B' /\ has_vtype Γ v' A').
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ inv same. eapply shape_inl_full in H1. 2: reflexivity.
  destruct H1 as [A''[B''[tysum]]]. subst. 
  apply subtype_shape_sum_rev in H2. destruct H2 as [A'''[B'''[tysum]]]. subst.
  exists A'''. exists B'''. aconstructor. inv H0. destruct H2.
  apply TypeV; auto. eapply TypeVSubtype; eauto.
Qed.

Fixpoint shape_inr_full Γ v A v' (orig : has_vtype Γ v A) {struct orig} :
  v = Inr v' ->
  (exists A' B', A = TyΣ A' B' /\ has_vtype Γ v' B').
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ inv same. eapply shape_inr_full in H1. 2: reflexivity.
  destruct H1 as [A''[B''[tysum]]]. subst.
  apply subtype_shape_sum_rev in H2. destruct H2 as [A'''[B'''[tysum]]]. subst.
  exists A'''. exists B'''. aconstructor. inv H0. destruct H2.
  apply TypeV; auto. eapply TypeVSubtype; eauto.
Qed.


Lemma shape_sum_inl Γ v A B :
  has_vtype Γ (Inl v) (TyΣ A B) -> has_vtype Γ v A.
Proof.
intro orig. apply (shape_sum_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [x [n]]. discriminate.
+ destruct H; destruct H; destruct H; inv H. auto.
Qed.


Lemma shape_sum_inr Γ v A B :
  has_vtype Γ (Inr v) (TyΣ A B) -> has_vtype Γ v B.
Proof.
intro orig. apply (shape_sum_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [x [n]]. discriminate.
+ destruct H; destruct H; destruct H; inv H. auto.
Qed.


(* Function *)
Fixpoint shape_fun_full Γ v x c ty (orig : has_vtype Γ v ty) {struct orig} :
  v = Fun x c ->
  (exists A C, ty = TyFun A C /\ has_ctype (CtxU Γ A) c C).
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ subst. apply (shape_fun_full _ _ x c) in H1. clear shape_fun_full. 
  2: reflexivity. destruct H1 as [A''[C''[s]]]. subst.
  apply subtype_shape_fun_rev in H2. destruct H2 as [A'''[C'''[s[vty1]]]].
  exists A'''. exists C'''. aconstructor. subst. inv H0.
  apply TypeC; auto.
  * apply WfCtxU; assumption.
  * eapply TypeCSubtype. 2: eauto.
    eapply ctx_subtype_ctype. eauto. apply WfCtxU; assumption.
    apply SubtypeCtxU. apply ctx_subtype_refl. all: assumption.
Qed.

Fixpoint shape_tyfun_full Γ v A C ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyFun A C ->
  (exists x n, v = Var (x, n)) \/
  (exists x c, v = Fun x c /\ has_ctype (CtxU Γ A) c C).
Proof.
intros same. destruct orig. destruct H1; try discriminate. eauto.
+ inv same. eauto. 
+ rewrite same in H2. apply subtype_shape_fun in H2. 
  destruct H2 as [A'' [C'' [funty]]]. subst. 
  apply (shape_tyfun_full _ _ A'' C'') in H1. clear shape_tyfun_full. 
  2: reflexivity. destruct H1. auto.
  right. destruct H1. destruct H1 as [c']. 
  exists x. exists c'.
  destruct H1. aconstructor. apply TypeC; inv H0; auto.
  * apply WfCtxU; assumption.
  * destruct H2. eapply TypeCSubtype. 2: eauto.
    eapply ctx_subtype_ctype. eauto. apply WfCtxU; assumption.
    apply SubtypeCtxU. apply ctx_subtype_refl. all: assumption.
Qed.

Lemma shape_fun Γ x c A C :
  has_vtype Γ (Fun x c) (TyFun A C) -> has_ctype (CtxU Γ A) c C.
Proof.
intro orig. apply (shape_tyfun_full _ _ A C) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [y [n]]. discriminate.
+ do 3 (destruct H). inv H. inv H0. apply TypeC; assumption.
Qed.


(* Handler *)
Fixpoint shape_handler_full Γ v x c_r h ty
  (orig : has_vtype Γ v ty) {struct orig} :
  v = Handler x c_r h ->
  (exists A Σ E D Σ' D', ty = TyHandler (CTy A Σ E) D /\ 
    has_ctype (CtxU Γ A) c_r D /\ has_htype Γ h Σ' D' /\ respects Γ h Σ' D' E
    /\ sig_subtype Σ Σ' /\ csubtype D' D).
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_handler_full. exists A. exists Σ. exists E. exists D.
  exists Σ. exists D. inv same. do 3 aconstructor.
  inv H0. inv H6. aconstructor. constructor.
  apply sig_subtype_refl. auto. apply csubtype_refl. auto.
+ subst. apply (shape_handler_full _ _ x c_r h) in H1.
  clear shape_handler_full. 2: reflexivity.
  destruct H1 as [A''[Σ[E[D[Σ'[D'[same[cty[hty[r[sty]]]]]]]]]]]. subst.
  apply subtype_shape_handler_rev in H2. destruct H2 as [C' [D''[same[sty']]]].
  subst. apply subtype_shape_cty in sty'.
  destruct sty' as [A'''[Σ'''[E'''[same]]]]. subst.
  exists A'''. exists Σ'''. exists E'''. exists D''. exists Σ'. exists D'.
  aconstructor. constructor. 2: constructor. 3: constructor. 4: constructor.
  - eapply ctx_subtype_ctype. 
    3 : apply SubtypeCtxU. 3: apply ctx_subtype_refl. 3: assumption.
    3 : destruct H3; eauto.
    * apply TypeC. inv cty. assumption. inv H0. assumption.
      eapply TypeCSubtype; eauto.
    * inv H0. inv H6. apply WfCtxU; assumption.
  - assumption.
  - eapply respects_eqs_subtype; destruct H3 as [_[e]]; eauto. 
    inv H0. inv H6. eapply wf_eqs_sig_subtype; eauto.
    eapply sig_subtype_trans; eauto. inv hty. assumption.
  - destruct H3 as [_[a]]. eapply sig_subtype_trans; eauto.
  - eapply csubtype_trans; eauto.
Qed.


Fixpoint shape_tyhandler_full Γ v A Σ E D ty
  (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyHandler (CTy A Σ E) D ->
  (exists x n, v = Var (x, n)) \/
  (exists x c_r h Σ' D', v = Handler x c_r h /\ has_ctype (CtxU Γ A) c_r D' 
    /\ has_htype Γ h Σ' D' /\ respects Γ h Σ' D' E
    /\ sig_subtype Σ Σ' /\ csubtype D' D).
Proof.
intros same. destruct orig. destruct H1; try discriminate. eauto.
+ clear shape_tyhandler_full. right.
  exists x. exists c_ret. exists h. exists Σ. exists D.
  inv same. do 4 aconstructor. constructor; inv H2.
  apply sig_subtype_refl. assumption. apply csubtype_refl. assumption.
+ rewrite same in *. apply subtype_shape_handler in H2. 
  destruct H2 as [C' [D' [hty]]]. destruct H2. subst.
  destruct C' as [A' Σ' E'].
  apply (shape_tyhandler_full _ _ A' Σ' E' D') in H1.
  clear shape_tyhandler_full. 2: reflexivity. destruct H1. auto.
  right. destruct H1 as [x[cr[h[Σ''[D''[same[cty[hty[r]]]]]]]]].
  exists x. exists cr. exists h. exists Σ''. exists D''.
  aconstructor. constructor; destruct H1.
  - eapply ctx_subtype_ctype. eauto.
    inv H0. inv H7. apply WfCtxU; assumption.
    apply SubtypeCtxU. apply ctx_subtype_refl. all: inv H2; assumption.
  - inv H2. aconstructor. constructor.  eapply respects_eqs_subtype; eauto. 
    inv H0. inv H6. eapply wf_eqs_sig_subtype; eauto.
    eapply sig_subtype_trans; eauto. inv hty. assumption. constructor.
    eapply sig_subtype_trans; eauto. eapply csubtype_trans; eauto.
Qed.

Lemma shape_handler Γ x c_r h A Σ E D:
  has_vtype Γ (Handler x c_r h) (TyHandler (CTy A Σ E) D) ->
    (exists Σ' D', has_ctype (CtxU Γ A) c_r D' /\ has_htype Γ h Σ' D'
      /\ respects Γ h Σ' D' E /\ sig_subtype Σ Σ' /\ csubtype D' D).
Proof.
intro orig.
apply (shape_tyhandler_full _ _ A Σ E D) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [y [n]]. discriminate.
+ do 6 (destruct H). inv H. eauto.
Qed.

(* ========================= Handler Cases Shapes ========================= *)

Lemma h_has_case Γ h Σ D op A_op B_op:
  has_htype Γ h Σ D ->
  get_op_type Σ op = Some (A_op, B_op) ->
  exists x k c_op, find_case h op = Some (x, k, c_op).
Proof.
revert Γ Σ. induction h; intros Γ Σ typed gets; inv typed; inv H2.
+ simpl in gets. discriminate.
+ simpl in *. destruct (op==o); eauto.
Qed.

Lemma case_has_type Γ h Σ D op Aop Bop x k c_op:
  has_htype Γ h Σ D -> get_op_type Σ op = Some (Aop, Bop) ->
  find_case h op = Some (x, k, c_op) ->
  has_ctype (CtxU (CtxU Γ (TyFun Bop D)) Aop) c_op D.
Proof.
revert Σ. induction h; intros Σ tys gets finds.
simpl in finds. discriminate.
simpl in *. destruct (op==o).
- inv tys. inv H2. simpl in *. destruct (o==o). 2: (destruct n; reflexivity).
  inv finds. inv gets. assumption.
- inv tys. inv H2. eapply IHh; eauto.
  simpl in gets. destruct (op==o); eauto. rewrite e in n. destruct n. auto.
Qed. 

(* ==================== Computation Shapes ==================== *)

(* Return *)
Fixpoint shape_ret_full Γ c C v A Σ E (orig : has_ctype Γ c C) {struct orig} :
  c = (Ret v) -> C = (CTy A Σ E) -> 
  has_vtype Γ v A.
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate.
+ clear shape_ret_full. inv same. inv samety. assumption.
+ destruct C as (A', Σ', E').
  apply (shape_ret_full _ _ (CTy A' Σ' E') v A' Σ' E') in H1;
  clear shape_ret_full; auto. subst.
  inv H0. apply TypeV; auto. inv H2. eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_ret Γ v A Σ E :
  has_ctype Γ (Ret v) (CTy A Σ E) -> has_vtype Γ v A.
Proof.  
intro orig. eapply (shape_ret_full _ _ _ v A Σ E) in orig; auto.
Qed.


(* Return *)
Fixpoint shape_absurd_full Γ c C v (orig : has_ctype Γ c C) {struct orig} :
  c = (Absurd v) -> has_vtype Γ v TyØ.
Proof.  
intros same. destruct orig. destruct H1; try discriminate; inv same; auto.
apply (shape_absurd_full _ _ _ v) in H1; auto.
Qed.


Fixpoint shape_absurd Γ v C :
  has_ctype Γ (Absurd v) C -> has_vtype Γ v TyØ.
Proof.  
intro orig. eapply (shape_absurd_full _ _ _ v) in orig; auto.
Qed.


(* ΠMatch *)
Fixpoint shape_prodmatch_full Γ c v x y c' C
  (orig : has_ctype Γ c C) {struct orig} :
  c = (ΠMatch v x y c') ->
  (exists A B, has_vtype Γ v (TyΠ A B) /\ has_ctype (CtxU (CtxU Γ A) B) c' C).
Proof.  
intros same. destruct orig. destruct H1; try discriminate; inv same.
+ clear shape_prodmatch_full. exists A. exists B. auto.
+ apply (shape_prodmatch_full _ _ v x y c') in H1; clear shape_prodmatch_full. 
  2: reflexivity. destruct H1 as [A' [B' [vty]]].
  exists A'. exists B'. aconstructor.
  apply TypeC; try (inv H1; assumption). eapply TypeCSubtype; eauto.
Qed.


Fixpoint shape_prodmatch Γ v x y c C :
  has_ctype Γ (ΠMatch v x y c) C ->
  (exists A B, has_vtype Γ v (TyΠ A B) /\  has_ctype (CtxU (CtxU Γ A) B) c C).
Proof.
intro orig. apply (shape_prodmatch_full _ _ v x y c) in orig; auto.
Qed.


(* ΣMatch *)
Fixpoint shape_summatch_full Γ c v xl cl xr cr C
  (orig : has_ctype Γ c C) {struct orig} :
  c = (ΣMatch v xl cl xr cr) ->
  (exists A B, has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) cl C /\ has_ctype (CtxU Γ B) cr C).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_summatch_full. inv same. exists A. exists B. auto.
+ apply (shape_summatch_full _ _ v xl cl xr cr) in H1;
  clear shape_summatch_full. 2: assumption.
  destruct H1 as [A' [B' [vty]]].
  exists A'. exists B'. aconstructor.
  inv H1. constructor; apply TypeC; auto.
  all: (eapply TypeCSubtype; eauto) || (inv H3; inv H4; assumption).
Qed.


Fixpoint shape_summatch Γ v xl cl xr cr C :
  has_ctype Γ (ΣMatch v xl cl xr cr) C ->
  (exists A B, has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) cl C /\ has_ctype (CtxU Γ B) cr C).
Proof.
intro orig. apply (shape_summatch_full _ _ v xl cl xr cr) in orig; auto.
Qed.


(* App *)
Fixpoint shape_app_full Γ c v1 v2 C (orig : has_ctype Γ c C) {struct orig} :
  c = (App v1 v2) ->
  (exists A, has_vtype Γ v1 (TyFun A C) /\ has_vtype Γ v2 A).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_app_full. inv same. exists A. auto.
+ apply (shape_app_full _ _ v1 v2) in H1;
  clear shape_app_full. 2: assumption.
  destruct H1 as [A' [fty]].
  exists A'. aconstructor. apply TypeV. auto.
  - inv fty. inv H4. apply WfTyFun; assumption.
  - eapply TypeVSubtype. exact fty. apply SubtypeTyFun.
    apply vsubtype_refl. inv fty. inv H4. all: assumption.
Qed.


Fixpoint shape_app Γ x c v C :
  has_ctype Γ (App (Fun x c) v) C ->
  (exists A, has_ctype (CtxU Γ A) c C /\ has_vtype Γ v A).
Proof.
intro orig. eapply (shape_app_full _ _ (Fun x c) v C) in orig.
2: reflexivity. destruct orig as [A [fty]]. apply shape_fun in fty. eauto.
Qed.


(* Handle *)
Fixpoint shape_handle_full Γ c v c' C (orig : has_ctype Γ c C) {struct orig} :
  c = (Handle v c') ->
  (exists C', has_vtype Γ v (TyHandler C' C) /\ has_ctype Γ c' C').
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_handle_full. inv same. exists C. auto.
+ apply (shape_handle_full _ _ v c') in H1; auto.
  destruct H1 as [D [vty]].
  exists D. aconstructor. inv H1.
  apply TypeV. assumption. apply WfTyHandler; auto.
  eapply TypeVSubtype. exact vty.
  apply SubtypeTyHandler. apply csubtype_refl. all: assumption.
Qed.


Fixpoint shape_handle Γ v c D :
  has_ctype Γ (Handle v c) D ->
  (exists C, has_vtype Γ v (TyHandler C D) /\ has_ctype Γ c C).
Proof.
intro orig. eapply (shape_handle_full _ _ v c D) in orig; auto.
Qed.


(* LetRec *)
Fixpoint shape_letrec_full Γ c f x c1 c2 D
  (orig : has_ctype Γ c D) {struct orig} :
  c = (LetRec f x c1 c2) ->
  (exists A C, has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
    has_ctype (CtxU Γ (TyFun A C)) c2 D).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_letrec_full. inv same. exists A. exists C. auto.
+ apply (shape_letrec_full _ _ f x c1 c2) in H1;
  clear shape_letrec_full. 2: assumption.
  destruct H1 as [A' [C'' [cty]]]. inv H1.
  exists A'. exists C''. aconstructor. apply TypeC; auto.
  eapply TypeCSubtype. 2: eauto. apply TypeC; assumption.
Qed.


Fixpoint shape_letrec Γ f x c1 c2 D :
  has_ctype Γ (LetRec f x c1 c2) D ->
  (exists A C, has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
    has_ctype (CtxU Γ (TyFun A C)) c2 D).
Proof.
intro orig. eapply (shape_letrec_full _ _ f x c1 c2 D) in orig; auto.
Qed.


(* DoBind *)
Fixpoint shape_dobind_full Γ c C x c1 c2 A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = (DoBind x c1 c2) -> C = (CTy A Σ E) ->
  (exists A', has_ctype Γ c1 (CTy A' Σ E) /\ has_ctype (CtxU Γ A') c2 C).
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. clear shape_dobind_full. exists A0. auto.
+ destruct C as (A', Σ', E').
  apply (shape_dobind_full _ _ (CTy A' Σ' E') x c1 c2 A' Σ' E') in H1;
  clear shape_dobind_full; auto. destruct H1 as [A'' [cty]].
  exists A''. constructor.
  - apply TypeC. assumption. inv cty. inv H0. inv H4.
    apply WfCTy; assumption. eapply TypeCSubtype. exact cty.
    inv H2. inv cty. inv H3. apply SubtypeCTy; auto. apply vsubtype_refl; auto.
  - apply TypeC. inv H1. 3: eapply TypeCSubtype. all: eauto.
Qed.


Fixpoint shape_dobind Γ x c1 c2 A Σ E :
  has_ctype Γ (DoBind x c1 c2) (CTy A Σ E) ->
  (exists A', has_ctype Γ c1 (CTy A' Σ E) /\ 
    has_ctype (CtxU Γ A') c2 (CTy A Σ E)).
Proof.  
intro orig. eapply (shape_dobind_full _ _ _ x c1 c2 A Σ E) in orig; auto.
Qed.


(* Op *)
Fixpoint shape_op_full Γ c C op v y c' A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = (Op op v y c') -> C = (CTy A Σ E) ->
  (exists Aop Bop, get_op_type Σ op = Some (Aop, Bop) /\
    has_vtype Γ v Aop /\  has_ctype (CtxU Γ Bop) c' C).
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. eauto.
+ destruct C as (A', Σ', E').
  apply (shape_op_full _ _ (CTy A' Σ' E') op v y c' A' Σ' E') in H1;
  clear shape_op_full; eauto. destruct H1 as [A'' [B'' [g [vty]]]]. inv H2.
  eapply sig_subtype_get_Some in g; eauto. destruct g as [A'''[B'''[g'[s']]]].
  exists A'''. exists B'''. aconstructor. constructor.
  - apply TypeV. assumption. apply get_op_type_wf in g'. destruct g'.
    assumption. inv H0. assumption. eapply TypeVSubtype; eauto.
  - eapply (ctx_subtype_ctype (CtxU Γ B'') (CtxU Γ B''')).
    * apply TypeC. inv H1. assumption. assumption.
      eapply TypeCSubtype. eauto. apply SubtypeCTy; assumption.
    * apply WfCtxU. assumption. apply get_op_type_wf in g'. destruct g'.
      all: inv H0; assumption.
    * apply SubtypeCtxU. apply ctx_subtype_refl. all: assumption.
Qed.


Fixpoint shape_op Γ op v y c A Σ E :
  has_ctype Γ (Op op v y c) (CTy A Σ E) -> 
  (exists Aop Bop, get_op_type Σ op = Some (Aop, Bop) /\
    has_vtype Γ v Aop /\  has_ctype (CtxU Γ Bop) c (CTy A Σ E)).
Proof.  
intro orig. eapply (shape_op_full _ _ _ op v y c A Σ E) in orig; auto.
Qed.

(* ==================== Logic Subtyping ==================== *)

Fixpoint veq_subtype A A' Γ v1 v2 (orig : veq A Γ v1 v2) {struct orig} :
  wf_vtype A' -> vsubtype A A' -> veq A' Γ v1 v2.
Proof. 
intros. inv orig. apply Veq; auto. induction H3.
+ apply VRefl. auto.
+ apply VSym. eauto.
+ eapply VTrans; eauto.
+ eapply VInsert; eauto.
+ eapply VRemove; eauto.
+ inv H0. inv H. eapply EqPair; eapply veq_subtype; eauto.
Qed.

Fixpoint ceq_subtype C C' Γ c1 c2 (orig : ceq C Γ c1 c2) {struct orig} :
  wf_ctype C' -> csubtype C C' -> ceq C' Γ c1 c2.
Proof. 
intros. inv orig. apply Ceq; auto. destruct H3.
+ apply CRefl. auto.
+ apply CSym. eauto.
+ eapply CTrans; eauto.
Qed.
