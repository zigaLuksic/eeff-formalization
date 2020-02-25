Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)

Require Export declarational wf_lemmas.

(* ==================== Sig and Eqs Properties ==================== *)

Lemma sig_subtype_get_Some Σ Σ' op A B :
  sig_subtype Σ Σ' -> get_op_type Σ op = Some (A, B) -> 
  exists A' B', 
    get_op_type Σ' op = Some (A', B') /\ 
    vsubtype A A' /\ vsubtype B' B.
Proof.
intros sty gets. induction sty; simpl in gets. discriminate.
destruct (op == op0); eauto.
inv gets. exists A', B'. auto.
Qed.


Lemma sig_subtype_extend Σ Σ' op A B :
  sig_subtype Σ Σ' -> wf_sig (SigU Σ' op A B) -> 
  sig_subtype Σ (SigU Σ' op A B).
Proof.
intros. induction H.
+ apply SubtypeSigØ.
+ eapply SubtypeSigU; eauto. inv H0. simpl.
  destruct (op0 == op); auto. rewrite e in *. rewrite H1 in H9. discriminate.
Qed.


Lemma sig_subtype_empty Σ : 
  sig_subtype Σ SigØ -> Σ = SigØ.
Proof.
intro subty. inv subty.
auto. simpl in *. discriminate.
Qed.


Lemma eqs_subtype_extend E E' Σ Γ Z T1 T2 :
  eqs_subtype E E' -> wf_eqs (EqsU E' Γ Z T1 T2) Σ ->
  eqs_subtype E (EqsU E' Γ Z T1 T2).
Proof.
intros. induction H.
+ apply SubtypeEqsØ.
+ eapply SubtypeEqsU. auto. simpl. right. auto.
Qed.


Lemma eqs_subtype_contains E E' Γ Z T1 T2 :
  eqs_subtype E E' -> has_eq E Γ Z T1 T2 -> 
  has_eq E' Γ Z T1 T2.
Proof.
intros sty gets. induction sty; simpl in gets; destruct gets; auto.
destruct H0 as [a [b [c d]]]. subst. assumption.
Qed.

Lemma eqs_subtype_empty E E': 
  eqs_subtype E E' -> E' = EqsØ -> E = EqsØ.
Proof.
intros subty eq. induction subty.
auto. subst. simpl in H. destruct H.
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
+ apply SubtypeTyList; auto.
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


Fixpoint eqs_subtype_trans E1 E2 E3 
  (E12 : eqs_subtype E1 E2) {struct E12} :  eqs_subtype E2 E3 -> 
  eqs_subtype E1 E3.
Proof.
intros E23. destruct E12.
+ apply SubtypeEqsØ.
+ eapply SubtypeEqsU; eauto; eapply eqs_subtype_contains; eauto.
Qed.

(* Use all lemmas explicitly, in order to ensure termination. The 'rev' lemmas
   are used for precisely that reason. *)
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
  get_op_type Σ1 op = Some (A', B') ->
  vsubtype A A' -> vsubtype B' B ->
  exists A'' B'', 
    get_op_type Σ2 op = Some (A'', B'') /\ 
    vsubtype A A'' /\ vsubtype B'' B.

Proof.
all: rename vsubtype_trans into VT; rename vsubtype_trans_rev into VTR.
all: rename csubtype_trans into CT; rename csubtype_trans_rev into CTR.
all: rename sig_subtype_trans into ST; rename sig_subtype_trans_rev into STR.
all: rename get_op_trans into GOPT.
{
clear ST STR GOPT.
intros A23; destruct A12; try assumption; inv A23. 
+ apply SubtypeTyΣ; eauto.
+ apply SubtypeTyΠ; eauto.
+ apply SubtypeTyList; eauto.
+ apply SubtypeTyFun.
  - eapply VTR; eauto. 
  - eapply CT; eauto.
+ apply SubtypeTyHandler.
  - eapply CTR; eauto. 
  - eapply CT; eauto.
}{
clear ST STR GOPT.
intros A32; destruct A21; try assumption; inv A32. 
+ apply SubtypeTyΣ; eapply VTR; eauto.
+ apply SubtypeTyΠ; eapply VTR; eauto.
+ apply SubtypeTyList; eapply VTR; eauto.
+ apply SubtypeTyFun.
  - eapply VT; eauto.
  - eapply CTR; eauto.
+ apply SubtypeTyHandler.
  - eapply CT; eauto.
  - eapply CTR; eauto.
}{
clear VTR CT CTR STR GOPT.
intros C23; destruct C12. inv C23. apply SubtypeCTy.
- eapply VT; eauto.
- eapply ST; eauto.
- eapply eqs_subtype_trans; eauto.
}{
clear VT CT CTR ST GOPT.
intros C32; destruct C21. inv C32. apply SubtypeCTy.
- eapply VTR; eauto.
- eapply STR; eauto.
- eapply eqs_subtype_trans; eauto.
}{
clear CT CTR STR.
intros S23. destruct S12.
apply SubtypeSigØ.
apply (sig_subtype_get_Some Σ' Σ3) in H as H'.
destruct H' as [A'' [B'' [g [stya' styb']]]].
eapply SubtypeSigU.
2 : exact g. all: try assumption.
+ eapply ST; eauto.
+ eapply VT; eauto.
+ eapply VTR; eauto.
}{
clear CT CTR ST.
intros S32. destruct S21.
{ apply sig_subtype_empty in S32. subst. apply SubtypeSigØ. }
induction Σ3.
{ apply SubtypeSigØ. }
inv S32. simpl in *. destruct (o==op).
+ inv H8. eapply SubtypeSigU. auto. eauto.
  - eapply VTR; eauto.
  - eapply VT; eauto.
+ eapply GOPT in H8 as gets'. all: eauto.
  destruct gets' as [A'' [B'' [gets' [styA'' styB'']]]].
  eapply SubtypeSigU; eauto.
}{
clear CT CTR ST STR GOPT.
intros. revert H. induction S12; intros gets; simpl in *. discriminate.
destruct (op==op0). 2: auto. inv gets.
exists A'0, B'0. aconstructor. constructor.
- eapply VTR; eauto.
- eapply VT; eauto.
}
Qed.


Fixpoint ctx_subtype_trans Γ Γ' Γ'':
  ctx_subtype Γ Γ' -> ctx_subtype Γ' Γ'' -> 
  ctx_subtype Γ Γ''.
Proof.
destruct Γ; destruct Γ'; destruct Γ''; intros sty sty'. 
all: inv sty; inv sty'.
- apply SubtypeCtxØ.
- apply SubtypeCtxU. eauto. eapply vsubtype_trans; eauto.
Qed.

(* ==================== Context Properties ==================== *)

Fixpoint ctx_subtype_get Γ Γ' A num (csty : ctx_subtype Γ Γ') {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', 
    get_vtype Γ' num = Some A' /\ vsubtype A A'.
Proof.
revert num. induction csty. clear ctx_subtype_get.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num; eauto.
  simpl in *. inv get. exists A'. auto.
Qed.


Fixpoint ctx_subtype_get_rev Γ Γ' A num (csty : ctx_subtype Γ' Γ) {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', 
    get_vtype Γ' num = Some A' /\ vsubtype A' A.
Proof.
revert num. induction csty. clear ctx_subtype_get_rev.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num; eauto.
  simpl in *. inv get. exists A0. auto.
Qed.


Lemma ctx_subtype_join_ctxs Γ1 Γ1' Γ2 Γ2':
  ctx_subtype Γ1 Γ1' -> ctx_subtype Γ2 Γ2' ->
  ctx_subtype (join_ctxs Γ1 Γ2) (join_ctxs Γ1' Γ2').
Proof.
intros sty1 sty2. induction sty2; auto. apply SubtypeCtxU; assumption. 
Qed.


Lemma ctx_subtype_tctx_to_ctx Z C C':
  wf_tctx Z -> csubtype C C' -> 
  ctx_subtype (tctx_to_ctx Z C) (tctx_to_ctx Z C').
Proof.
intros wfz sty. induction Z; simpl.
+ apply SubtypeCtxØ. 
+ apply SubtypeCtxU. inv wfz. auto.
  apply SubtypeTyFun. apply vsubtype_refl. inv wfz. auto. auto.
Qed.


Lemma ctx_subtype_len Γ Γ':
  ctx_subtype Γ Γ' -> ctx_len Γ = ctx_len Γ'.
Proof. 
intro sty. induction sty; simpl; auto. 
Qed. 


Fixpoint ctx_subtype_insert Γ Γ' A A' n:
  ctx_subtype Γ Γ' -> vsubtype A A' ->
  ctx_subtype (ctx_insert Γ n A) (ctx_insert Γ' n A').
Proof.
intros. destruct H; simpl in *; destruct n.
+ apply SubtypeCtxU. apply SubtypeCtxØ. auto.
+ apply SubtypeCtxØ.
+ apply SubtypeCtxU. apply SubtypeCtxU. all: auto.
+ apply SubtypeCtxU; auto.
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
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> ceq C Γ' c1 c2

with ctx_subtype_heq Γ Γ' Σ D h1 h2 (equals : heq Σ D Γ h1 h2) {struct equals}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> heq Σ D Γ' h1 h2

with ctx_subtype_wf_inst Γ Γ' I Γi (wf : wf_inst Γ I Γi) {struct wf}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> wf_inst Γ' I Γi.

Proof.
all: rename ctx_subtype_vtype into VL.
all: rename ctx_subtype_ctype into CL.
all: rename ctx_subtype_htype into HL.
all: rename ctx_subtype_respects into RL.
all: rename ctx_subtype_veq into VEL.
all: rename ctx_subtype_ceq into CEL.
all: rename ctx_subtype_heq into HEL.
all: rename ctx_subtype_wf_inst into WFL.
{
clear VEL CEL HEL WFL.
intros wf ctxsty.
destruct types. induction H1; apply TypeV; eauto.
+ apply TypeUnit.
+ apply TypeInt.
+ apply (ctx_subtype_get_rev _ _ A n) in ctxsty; auto.
  destruct ctxsty as [A' [gets stya]].
  eapply TypeVSubtype; eauto.
  apply TypeV; eauto. apply get_vtype_wf in gets as wfA'; eauto.
  apply TypeVar. auto.
+ apply TypePair; eauto.
+ apply TypeInl; eauto.
+ apply TypeInr; eauto.
+ apply TypeListNil.
+ apply TypeListCons; eauto.
+ apply TypeFun. eapply CL; inv H0. eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ apply TypeHandler; eauto. eapply CL; inv H0; inv H6; eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply TypeVSubtype; eauto.
}{
clear WFL RL VEL CEL HEL.
intros wf ctxsty.
destruct types. induction H1; apply TypeC; eauto.
+ apply TypeRet. eauto.
+ apply TypeAbsurd. eauto.
+ eapply TypeΠMatch; eauto.
  eapply CL. eauto.
  all: inv H2; inv H3; inv H7.
  * apply WfCtxU. apply WfCtxU. all: auto.
  * apply SubtypeCtxU. apply SubtypeCtxU. auto.
    all: apply vsubtype_refl; auto.
+ eapply TypeΣMatch; eauto.
  - eapply CL. eauto.
    all: inv H2; inv H4. 
    * apply WfCtxU; auto.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. auto.
  - eapply CL; eauto.
    all: inv H3; inv H4. 
    * apply WfCtxU; auto.
    * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. auto.
+ eapply TypeListMatch; eauto.
  eapply CL. eauto.
  all: inv H3; inv H4; inv H8.
  * apply WfCtxU. apply WfCtxU. all: auto.
  * apply SubtypeCtxU. apply SubtypeCtxU. auto.
    all: apply vsubtype_refl; auto. 
+ eapply TypeDoBind; eauto.
  inv H1. inv H4. eapply CL. eauto.
  * apply WfCtxU; auto.
  * apply SubtypeCtxU. exact ctxsty. apply vsubtype_refl. auto.
+ eapply TypeApp; eauto.
+ eapply TypeHandle; eauto.
+ eapply TypeLetRec.
  - eapply CL. eauto.
    all: inv H2; inv H3.
    * apply WfCtxU. apply WfCtxU. eauto. inv H8. all: eauto.
    * apply SubtypeCtxU. apply SubtypeCtxU. eauto.
      apply vsubtype_refl. inv H8. auto. apply vsubtype_refl. auto.
  - eapply CL. eauto. all: inv H2; inv H3.
    * apply WfCtxU; auto.
    * apply SubtypeCtxU. eauto. apply vsubtype_refl. auto.
+ eapply TypeOp; eauto.
  eapply CL. eauto. all: inv H3; inv H4.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply TypeCSubtype; eauto.
}{
clear VL RL VEL CEL HEL WFL.
intros wf ctxsty.
destruct types. induction H2; apply TypeH; eauto.
+ eapply TypeCasesØ.
+ eapply TypeCasesU. auto.
  eapply HL. all: eauto.
  eapply CL. eauto.
  all: inv H4; inv H5; inv H9.
  - apply WfCtxU. apply WfCtxU. all: auto.
  - apply SubtypeCtxU. apply SubtypeCtxU. auto.
    all: apply vsubtype_refl; auto.
}{
clear VL CL HL VEL HEL.
intros wf ctxsty.
inv r. eapply Respects; auto. destruct H3.
+ eapply RespectEqsØ.
+ eapply RespectEqsU; eauto.
  eapply CEL; eauto; inv H2.
  - apply wf_join_ctxs. apply wf_join_ctxs. auto.
    apply wf_tctx_to_ctx. all: auto.
  - apply ctx_subtype_join_ctxs. apply ctx_subtype_join_ctxs. 
    all: auto; apply ctx_subtype_refl.
    apply wf_tctx_to_ctx; auto. auto.
}{
intros wf ctxsty.
inv equals. destruct H1; apply Veq; eauto.
all: clear VL CL HL.
+ apply VeqSym. eauto.
+ eapply VeqTrans; eauto.
+ eapply ctx_subtype_get_rev in ctxsty as cget; eauto.
  destruct cget as [A''[gets sty]]. 
  eapply VeqVar; eauto. eapply vsubtype_trans; eauto.
+ eapply VeqUnit.
+ eapply VeqInt.
+ eapply VeqPair; eauto.
+ eapply VeqInl; eauto.
+ eapply VeqInr; eauto.
+ eapply VeqListNil.
+ eapply VeqListCons; eauto.
+ eapply VeqFun. eapply CEL. eauto.
  all: inv H; inv H3.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply VeqHandler. eapply CEL;
  inv H; inv H5; inv H8. all: eauto.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ apply ηUnit.
+ apply ηFun.
}{
intros wf ctxsty.
inv equals. destruct H1; apply Ceq; eauto.
all: clear HL HEL.
+ apply CeqSym. eauto.
+ eapply CeqTrans; eauto.
+ eapply CeqRet; eauto.
+ eapply CeqAbsurd; eauto.
+ eapply CeqΠMatch; eauto.
  eapply CEL. eauto.
  all: inv H1; inv H3; inv H6.
  - apply WfCtxU. apply WfCtxU. all: auto.
  - apply SubtypeCtxU. apply SubtypeCtxU. auto.
    all: apply vsubtype_refl; auto.
+ eapply CeqΣMatch; eauto; 
  eapply CEL; eauto.
  all: inv H1; inv H4; inv H7.
  all: apply WfCtxU || apply SubtypeCtxU; auto.
  all: apply vsubtype_refl; auto.
+ eapply CeqListMatch; eauto.
  eapply CEL; eauto. 
  all: inv H1; inv H4.
  - apply WfCtxU. apply WfCtxU. all: auto. inv H7. auto.
  - apply SubtypeCtxU. apply SubtypeCtxU. auto.
    all: apply vsubtype_refl. inv H7. all: auto.
+ eapply CeqDoBind; eauto. eapply CEL; eauto.
  all: inv H1; inv H3; inv H6.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply CeqApp; eauto.
+ eapply CeqHandle; eauto.
+ eapply CeqLetRec.
  - eapply CEL; eauto.
    all: inv H2; inv H4; inv H2.
    * apply WfCtxU. apply WfCtxU. 2: inv H10. all: eauto.
    * apply SubtypeCtxU. apply SubtypeCtxU. auto.
      all: apply vsubtype_refl. inv H10. all: auto.
  - eapply CEL; eauto.
    all: inv H2; inv H4; inv H2.
    * apply WfCtxU; auto.
    * apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply CeqOp; eauto.
  eapply CEL; eauto.
  all: inv H3; inv H5; inv H3.
  - apply WfCtxU; auto.
  - apply SubtypeCtxU. auto. apply vsubtype_refl. auto.
+ eapply OOTB; eauto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βListMatch_Nil.
+ eapply βListMatch_Cons.
+ eapply βApp.
+ eapply βLetRec.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
+ eapply ηPair. 
  apply ctx_subtype_len in ctxsty. omega.
  assert (wf_vtype (TyΠ A B)). 
  { inv H2. apply wf_ctx_insert_vtype in H3; auto. }
  eapply CL; eauto. 
  - apply wf_ctx_insert; eauto.
  - eapply ctx_subtype_insert. auto.
    apply vsubtype_refl. auto.
+ eapply ηSum. apply ctx_subtype_len in ctxsty. omega.
  assert (wf_vtype (TyΣ A B)). 
  { inv H2. apply wf_ctx_insert_vtype in H3; auto. }
  eapply CL; eauto.
  - apply wf_ctx_insert; eauto.
  - eapply ctx_subtype_insert. auto.
    apply vsubtype_refl. auto.
+ eapply ηList. 
  apply ctx_subtype_len in ctxsty. omega.
  assert (wf_vtype (TyList A)). 
  { inv H2. apply wf_ctx_insert_vtype in H3; auto. }
  eapply CL; eauto. 
  - apply wf_ctx_insert; eauto.
  - eapply ctx_subtype_insert. auto.
    apply vsubtype_refl. auto.
+ eapply ηDoBind.
}{
intros wf ctxsty.
inv equals. destruct H4.
all: clear VL CL.
all: clear VEL WFL.
+ eapply Heq. auto. exact H0. exact H1. all: eauto. eapply HeqSigØ.
+ eapply Heq. exact H. exact H0. all: eauto.
  eapply HeqSigU; eauto.
  eapply CEL; eauto; inv H6; inv H8; inv H6; inv H14.
  - apply WfCtxU. apply WfCtxU. all: assumption.
  - apply SubtypeCtxU. apply SubtypeCtxU. assumption.
    all: apply vsubtype_refl; assumption.
}{
clear HL CL VEL CEL.
clear RL HEL.
intros wfc ctxsty.
destruct wf.
+ eapply WfInstØ. auto.
+ eapply WfInstU; eauto.
}
Qed.


(* ==================== Instantiation Properties ==================== *)


Lemma wf_inst_subtype Γcheck I Γ Γ':
  wf_ctx Γ' -> ctx_subtype Γ Γ' -> wf_inst Γcheck I Γ ->
  wf_inst Γcheck I Γ'.
Proof.
intros wfc csty orig. revert Γ' wfc csty.
induction orig; intros Γ' wfc csty; inv csty.
+ apply WfInstØ. auto.
+ apply WfInstU.
  - apply TypeV. inv H. auto. inv wfc. auto.
    eapply TypeVSubtype; eauto.
  - apply IHorig. inv wfc. auto. auto.
Qed.


Lemma wf_inst_tctx_subtype C C' Γ' Γ Z I:
  csubtype C C' -> wf_ctype C' ->
  wf_inst Γ' I (join_ctxs (tctx_to_ctx Z C) Γ) ->
  wf_inst Γ' I (join_ctxs (tctx_to_ctx Z C') Γ).
Proof.
intros. 
apply wf_inst_wf_ctx in H1 as wfjc.
apply wf_join_ctxs_rev in wfjc. destruct wfjc as [wfz wfc].
apply wf_tctx_to_ctx_rev in wfz.
eapply wf_inst_subtype; eauto.
+ apply wf_join_ctxs; auto. apply wf_tctx_to_ctx; auto.
+ apply ctx_subtype_join_ctxs. apply ctx_subtype_tctx_to_ctx; eauto.
  apply ctx_subtype_refl. auto.
Qed.

(* ==================== Subtype Shapes ==================== *)

Lemma subtype_shape_empty A : vsubtype A TyØ -> A = TyØ.
Proof.
intro sty. inv sty. reflexivity.
Qed. 


Lemma subtype_shape_prod A B C : vsubtype C (TyΠ A B) -> 
  exists A' B',
    C = (TyΠ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0, B0. auto.
Qed.


Lemma subtype_shape_prod_rev A B C : vsubtype (TyΠ A B) C -> 
  exists A' B',
    C = (TyΠ A' B') /\ vsubtype A A' /\ vsubtype B B'.
Proof.
intro orig. inv orig. exists A', B'. auto.
Qed.


Lemma subtype_shape_sum A B C : vsubtype C (TyΣ A B) -> 
  exists A' B',
    C = (TyΣ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0, B0. auto.
Qed.


Lemma subtype_shape_sum_rev A B C : vsubtype (TyΣ A B) C -> 
  exists A' B',
    C = (TyΣ A' B') /\ vsubtype A A' /\ vsubtype B B'.
Proof.
intro orig. inv orig. exists A', B'. auto.
Qed.


Lemma subtype_shape_fun A B C : vsubtype C (TyFun A B) -> 
  exists A' B',
    C = (TyFun A' B') /\ vsubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists A0, C0. auto.
Qed.


Lemma subtype_shape_list A B : vsubtype B (TyList A) -> 
  exists A',
    B = (TyList A') /\ vsubtype A' A.
Proof.
intro orig. inv orig. exists A0. auto.
Qed.


Lemma subtype_shape_list_rev A B : vsubtype (TyList A) B -> 
  exists A',
    B = (TyList A') /\ vsubtype A A'.
Proof.
intro orig. inv orig. exists A'. auto.
Qed.


Lemma subtype_shape_fun_rev A B C : vsubtype (TyFun A B) C -> 
  exists A' B',
    C = (TyFun A' B') /\ vsubtype A' A /\ csubtype B B'.
Proof.
intro orig. inv orig. exists A', C'. auto.
Qed.


Lemma subtype_shape_handler A B C : vsubtype C (TyHandler A B) -> 
  exists A' B',
    C = (TyHandler A' B') /\ csubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists C0, D. auto.
Qed.


Lemma subtype_shape_handler_rev A B C : vsubtype (TyHandler A B) C -> 
  exists A' B',
    C = (TyHandler A' B') /\ csubtype A' A /\ csubtype B B'.
Proof.
intro orig. inv orig. exists C', D'. auto.
Qed.


Lemma subtype_shape_cty A Σ E C : csubtype C (CTy A Σ E) ->
  exists A' Σ' E', 
    C = CTy A' Σ' E' /\ vsubtype A' A /\ sig_subtype Σ' Σ /\ eqs_subtype E' E.
Proof.
intro orig. inv orig. exists A0, Σ0, E0. auto.
Qed.
  
Lemma subtype_shape_cty_rev A Σ E C : csubtype (CTy A Σ E) C ->
  exists A' Σ' E', 
    C = CTy A' Σ' E' /\ vsubtype A A' /\ sig_subtype Σ Σ' /\ eqs_subtype E E'.
Proof.
intro orig. inv orig. exists A', Σ', E'. auto.
Qed.

(* ==================== Template WF Subtyping ==================== *)

Lemma wf_t_subtype_sig Γ Γ' Z T Σ Σ':
  wf_t Γ Z T Σ ->
  sig_subtype Σ Σ' -> ctx_subtype Γ' Γ ->
  wf_sig Σ' -> wf_ctx Γ' ->
  wf_t Γ' Z T Σ'.
Proof.
intros orig. revert Γ'. induction orig; intros Γ' sty cty wfs wfc.
+ eapply WfTApp. eapply ctx_subtype_vtype; eauto. auto.
+ eapply WfTAbsurd. eapply ctx_subtype_vtype; eauto.
+ eapply WfTΠMatch. eapply ctx_subtype_vtype; eauto. inv H. inv H1.
  apply IHorig; auto. apply SubtypeCtxU. 
  apply SubtypeCtxU. 4: apply WfCtxU. 4: apply WfCtxU.
  all: try apply vsubtype_refl; auto.
+ eapply WfTΣMatch. eapply ctx_subtype_vtype; eauto. 
  all: inv H; inv H1.
  all: apply IHorig1 || apply IHorig2; auto.
  all: apply SubtypeCtxU || apply WfCtxU; auto.
  all: apply vsubtype_refl; auto.
+ eapply WfTListMatch. eapply ctx_subtype_vtype; eauto.
  all: inv H.
  all: apply IHorig1 || apply IHorig2; auto.
  all: do 2 (try (apply SubtypeCtxU || apply WfCtxU)); auto.
  all: try apply vsubtype_refl; auto || inv H1; auto.
+ eapply sig_subtype_get_Some in H. 2: exact sty.
  destruct H as [A'[B'[gets'[Asty Bsty]]]].
  eapply WfTOp. eauto.
  - eapply ctx_subtype_vtype; eauto. apply TypeV.
    * inv H0. auto.
    * apply get_op_type_wf in gets'. inv gets'. all: auto.
    * eapply TypeVSubtype; eauto.
  - apply IHorig; auto.
    * apply SubtypeCtxU; auto.
    * apply get_op_type_wf in gets'. inv gets'.
      apply WfCtxU. all: auto.
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
  respects Γ' h Σ D E -> has_eq E Γ Z T1 T2 ->
  ceq D (join_ctxs (join_ctxs Γ' (tctx_to_ctx Z D)) Γ)
    (handle_t (ctx_len Γ) (tctx_len Z) h T1) 
    (handle_t (ctx_len Γ) (tctx_len Z) h T2) .
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
Fixpoint shape_var_full Γ v n A (orig : has_vtype Γ v A) {struct orig} :
  v = Var n -> 
  exists A', 
    get_vtype Γ n = Some A' /\ vsubtype A' A.
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_var_full.
  exists A. inv same. aconstructor. apply vsubtype_refl. auto.
+ subst. eapply shape_var_full in H1; eauto.
  destruct H1 as [A'' [gets stya]].
  exists A''. aconstructor. eapply vsubtype_trans; eauto.
Qed.


Lemma shape_var Γ n A:
  has_vtype Γ (Var n) A -> 
  exists A',
    get_vtype Γ n = Some A' /\ vsubtype A' A.
Proof.
intro orig. apply (shape_var_full _ _ n A) in orig as shape; eauto.
Qed.


Lemma shape_var_ctx_empty n A:
  has_vtype CtxØ (Var n) A -> False.
Proof.
intro orig.
apply (shape_var_full _ _ n A) in orig as shape; eauto.
destruct shape as [A'[gets]]. simpl in gets. discriminate.
Qed.


(* Empty *)
Fixpoint shape_empty_full Γ v A (orig : has_vtype Γ v A) {struct orig} :
  A = TyØ -> exists n, v = Var n.
Proof.
intros samety.
destruct orig. destruct H1; try discriminate. eauto.
subst. apply subtype_shape_empty in H2. subst; eauto.
Qed.


Lemma shape_empty Γ v:
  has_vtype Γ v TyØ -> exists n, v = Var n.
Proof.
intro orig. apply (shape_empty_full _ _) in orig as shape; auto.
Qed.


(* Pair *)
Fixpoint shape_prod_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΠ A B ->
  (exists n, v = Var n) \/
  (exists v1 v2, 
    v = Pair v1 v2 /\ has_vtype Γ v1 A /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ left. eauto.
+ right. inv same. eauto.
+ rewrite same in H2. apply subtype_shape_prod in H2. 
  destruct H2 as [A'' [B'' [samety]]]. subst.
  apply (shape_prod_full _ _ A'' B'') in H1; eauto. clear shape_prod_full. 
  destruct H1. auto.
  right. destruct H1 as [v1[v2[s[vty1]]]].
  exists v1, v2. destruct H2.
  aconstructor. inv H0. constructor; apply TypeV.
  all: try eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_pair_full Γ v v1 v2 ty (orig : has_vtype Γ v ty) {struct orig} :
  v = Pair v1 v2 ->
  exists A B, 
    ty = TyΠ A B /\ has_vtype Γ v1 A /\ has_vtype Γ v2 B.
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_pair_full. exists A, B. inv same. auto.
+ subst. apply (shape_pair_full _ _ v1 v2) in H1; eauto.
  clear shape_pair_full. 
  destruct H1 as [A''[B''[ty[tyv1 tyv2]]]]. subst.
  apply subtype_shape_prod_rev in H2.
  destruct H2 as [A'''[B'''[s[stya styb]]]].
  exists A''', B'''. aconstructor. 
  subst. inv H0. constructor; apply TypeV; auto.
  all: eapply TypeVSubtype; eauto.
Qed.


Lemma shape_pair Γ v1 v2 A B :
  has_vtype Γ (Pair v1 v2) (TyΠ A B) ->  
  has_vtype Γ v1 A /\ has_vtype Γ v2 B.
Proof.
intro orig.
apply (shape_prod_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [n same]. discriminate.
+ destruct H as [v1' [v2' [same]]]. inv same. assumption.
Qed.


(* Sum *)
Fixpoint shape_sum_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΣ A B ->
  (exists n, v = Var n) \/
  (exists v1, v = Inl v1 /\ has_vtype Γ v1 A) \/
  (exists v2, v = Inr v2 /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ left. eauto.
+ right. left. inv same. eauto.
+ right. right. inv same. eauto.
+ rewrite same in H2. apply subtype_shape_sum in H2. 
  destruct H2 as [A'' [B'' [sigty[stya styb]]]]. subst. inv H0. 
  apply (shape_sum_full _ _ A'' B'') in H1. clear shape_sum_full. 
  2: reflexivity. destruct H1. auto. right. do 3 destruct H0; subst.
  * left. exists x. aconstructor.
    apply TypeV; auto. eapply TypeVSubtype; eauto.
  * right. exists x. aconstructor.
    apply TypeV; auto. eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_inl_full Γ v A v' (orig : has_vtype Γ v A) {struct orig} :
  v = Inl v' ->
  exists A' B',
    A = TyΣ A' B' /\ has_vtype Γ v' A'.
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ inv same. eapply shape_inl_full in H1. 2: reflexivity.
  destruct H1 as [A''[B''[tysum]]]. subst. 
  apply subtype_shape_sum_rev in H2.
  destruct H2 as [A'''[B'''[tysum]]]. subst.
  exists A''', B'''. aconstructor. inv H0. destruct H2.
  apply TypeV; auto. eapply TypeVSubtype; eauto.
Qed.


Fixpoint shape_inr_full Γ v A v' (orig : has_vtype Γ v A) {struct orig} :
  v = Inr v' ->
  exists A' B',
    A = TyΣ A' B' /\ has_vtype Γ v' B'.
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ inv same. eapply shape_inr_full in H1. 2: reflexivity.
  destruct H1 as [A''[B''[tysum]]]. subst.
  apply subtype_shape_sum_rev in H2.
  destruct H2 as [A'''[B'''[tysum]]]. subst.
  exists A''', B'''. aconstructor. inv H0. destruct H2.
  apply TypeV; auto. eapply TypeVSubtype; eauto.
Qed.


Lemma shape_inl Γ v A B :
  has_vtype Γ (Inl v) (TyΣ A B) -> has_vtype Γ v A.
Proof.
intro orig. apply (shape_sum_full _ _ A B) in orig as shape; eauto.
destruct shape.
+ destruct H as [n same]. discriminate.
+ destruct H; destruct H; destruct H; inv H. auto.
Qed.


Lemma shape_inr Γ v A B :
  has_vtype Γ (Inr v) (TyΣ A B) -> has_vtype Γ v B.
Proof.
intro orig. apply (shape_sum_full _ _ A B) in orig as shape; eauto.
destruct shape.
+ destruct H as [n same]. discriminate.
+ destruct H; destruct H; destruct H; inv H. auto.
Qed.


(* List *)
Fixpoint shape_list_full Γ v A ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyList A ->
  (exists n, v = Var n) \/ (v = ListNil) \/
  (exists w ws, v = 
    ListCons w ws /\ has_vtype Γ w A /\ has_vtype Γ ws (TyList A)).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ left. eauto.
+ right. left. inv same. eauto.
+ right. right. inv same. eauto.
+ rewrite same in H2. apply subtype_shape_list in H2.
  destruct H2 as [A'' [sigty]]. subst. 
  apply (shape_list_full _ _ A'') in H1; eauto. clear shape_list_full.
  destruct H1. auto. right. destruct H1. auto.
  destruct H1 as [w[ws[shape[tys1 tys2]]]].
  right. exists w, ws. aconstructor. constructor.
  all: apply TypeV; try assumption. inv H0. auto.
  all: eapply TypeVSubtype; eauto. apply SubtypeTyList. auto.
Qed.


Fixpoint shape_list_cons_full Γ v A w ws (orig: has_vtype Γ v A) {struct orig}:
  v = ListCons w ws ->
  exists A',
    A = TyList A' /\ has_vtype Γ w A' /\ has_vtype Γ ws (TyList A').
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ inv same. eapply shape_list_cons_full in H1. 2: reflexivity.
  destruct H1 as [A''[same[tys1 tys2]]]. subst. 
  apply subtype_shape_list_rev in H2.
  destruct H2 as [A'''[tyl]]. subst.
  exists A'''. aconstructor. constructor.
  all: apply TypeV; auto. inv H0. auto. 
  all: eapply TypeVSubtype; eauto. apply SubtypeTyList. auto.
Qed.


Lemma shape_cons Γ v vs A :
  has_vtype Γ (ListCons v vs) (TyList A) -> 
  has_vtype Γ v A /\ has_vtype Γ vs (TyList A).
Proof.
intro orig. eapply (shape_list_cons_full) in orig as shape; eauto.
destruct shape as [A'[same[tys1 tys2]]]. inv same. auto.
Qed.


(* Function *)
Fixpoint shape_fun_full Γ v c ty (orig : has_vtype Γ v ty) {struct orig} :
  v = Fun c ->
  exists A C,
    ty = TyFun A C /\ has_ctype (CtxU Γ A) c C.
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ inv same. eauto.
+ subst. apply (shape_fun_full _ _ c) in H1; eauto. clear shape_fun_full. 
  destruct H1 as [A''[C''[s]]]. subst.
  apply subtype_shape_fun_rev in H2.
  destruct H2 as [A'''[C'''[s[vty1]]]].
  exists A''', C'''. aconstructor. subst. inv H0.
  apply TypeC; auto.
  * apply WfCtxU; auto.
  * eapply TypeCSubtype. 2: eauto.
    eapply ctx_subtype_ctype. eauto. apply WfCtxU; auto.
    apply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
Qed.


Fixpoint shape_tyfun_full Γ v A C ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyFun A C ->
  (exists n, v = Var n) \/
  (exists c, v = Fun c /\ has_ctype (CtxU Γ A) c C).
Proof.
intros same. destruct orig. destruct H1; try discriminate. eauto.
+ inv same. eauto. 
+ rewrite same in H2. apply subtype_shape_fun in H2. 
  destruct H2 as [A'' [C'' [funty]]]. subst. 
  apply (shape_tyfun_full _ _ A'' C'') in H1; eauto. clear shape_tyfun_full. 
  destruct H1. auto. right. destruct H1 as [c']. 
  exists c'.
  destruct H1. aconstructor. apply TypeC; inv H0; auto.
  * apply WfCtxU; auto.
  * destruct H2. eapply TypeCSubtype. 2: eauto.
    eapply ctx_subtype_ctype. eauto. apply WfCtxU; auto.
    apply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
Qed.


Lemma shape_fun Γ c A C :
  has_vtype Γ (Fun c) (TyFun A C) -> has_ctype (CtxU Γ A) c C.
Proof.
intro orig. apply (shape_tyfun_full _ _ A C) in orig as shape; eauto.
destruct shape.
+ destruct H. discriminate.
+ destruct H as [c'[same tys]]. inv same. auto.
Qed.


(* Handler *)
Fixpoint shape_handler_full Γ v c_r h ty
  (orig : has_vtype Γ v ty) {struct orig} :
  v = Handler c_r h ->
  exists A Σ E D Σ' D',
    ty = TyHandler (CTy A Σ E) D /\ 
    has_ctype (CtxU Γ A) c_r D /\ has_htype Γ h Σ' D' /\ 
    respects Γ h Σ' D' E /\ sig_subtype Σ Σ' /\ csubtype D' D.
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_handler_full. exists A, Σ, E, D, Σ, D.
  inv same. do 3 aconstructor.
  inv H0. inv H6. aconstructor. constructor.
  apply sig_subtype_refl. auto. apply csubtype_refl. auto.
+ subst. apply (shape_handler_full _ _ c_r h) in H1; eauto.
  clear shape_handler_full.
  destruct H1 as [A''[Σ[E[D[Σ'[D'[same[cty[hty[r[sty]]]]]]]]]]]. subst.
  apply subtype_shape_handler_rev in H2.
  destruct H2 as [C' [D''[same[sty']]]]. subst.
  apply subtype_shape_cty in sty'.
  destruct sty' as [A'''[Σ'''[E'''[same]]]]. subst.
  exists A''', Σ''', E''', D'', Σ', D'.
  aconstructor. aconstructor. 2: aconstructor. 2: constructor. 3: constructor.
  - eapply ctx_subtype_ctype.
    3 : apply SubtypeCtxU; apply ctx_subtype_refl || destruct H3; eauto.
    * apply TypeC. inv cty. auto. inv H0. auto.
      eapply TypeCSubtype; eauto.
    * inv H0. inv H6. apply WfCtxU; auto.
  - eapply respects_eqs_subtype; destruct H3 as [_[e]]; eauto. 
    inv H0. inv H6.
    eapply wf_eqs_sig_subtype; eauto.
    eapply sig_subtype_trans; eauto. inv hty. auto.
  - destruct H3 as [_[a]]. eapply sig_subtype_trans; eauto.
  - eapply csubtype_trans; eauto.
Qed.


Fixpoint shape_tyhandler_full Γ v A Σ E D ty
  (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyHandler (CTy A Σ E) D ->
  (exists n, v = Var n) \/
  (exists c_r h Σ' D', 
    v = Handler c_r h /\ has_ctype (CtxU Γ A) c_r D' /\ 
    has_htype Γ h Σ' D' /\ respects Γ h Σ' D' E /\
    sig_subtype Σ Σ' /\ csubtype D' D).
Proof.
intros same. destruct orig. destruct H1; try discriminate. eauto.
+ clear shape_tyhandler_full. right.
  exists cr, h, Σ, D.
  inv same. do 4 aconstructor. constructor; inv H2.
  apply sig_subtype_refl. auto. apply csubtype_refl. auto.
+ rewrite same in *. apply subtype_shape_handler in H2. 
  destruct H2 as [C' [D' [hty[csty dsty]]]]. subst.
  destruct C' as [A' Σ' E'].
  apply (shape_tyhandler_full _ _ A' Σ' E' D') in H1; eauto. 
  destruct H1. auto.
  right. destruct H1 as [cr[h[Σ''[D''[same[cty[hty[r]]]]]]]].
  exists cr, h, Σ'', D''.
  aconstructor. constructor; destruct H1.
  - eapply ctx_subtype_ctype. eauto.
    inv H0. inv H5.
    apply WfCtxU; auto.
    apply SubtypeCtxU. apply ctx_subtype_refl.
    all: inv csty; auto.
  - inv csty. aconstructor. constructor. 
    * eapply respects_eqs_subtype; eauto.
      inv H0. inv H5. eapply wf_eqs_sig_subtype; eauto.
      eapply sig_subtype_trans; eauto. inv hty. auto.
    * constructor. eapply sig_subtype_trans; eauto.
      eapply csubtype_trans; eauto.
Qed.


Lemma shape_handler Γ c_r h A Σ E D:
  has_vtype Γ (Handler c_r h) (TyHandler (CTy A Σ E) D) ->
  exists Σ' D',
    has_ctype (CtxU Γ A) c_r D' /\ has_htype Γ h Σ' D' /\
    respects Γ h Σ' D' E /\ sig_subtype Σ Σ' /\ csubtype D' D.
Proof.
intro orig.
apply (shape_tyhandler_full _ _ A Σ E D) in orig as shape; eauto.
destruct shape.
+ destruct H as [n]. discriminate.
+ do 5 (destruct H). inv H. eauto.
Qed.

(* ==================== Handler Cases Shapes ==================== *)

Lemma h_has_case Γ h Σ D op A_op B_op:
  has_htype Γ h Σ D ->
  get_op_type Σ op = Some (A_op, B_op) ->
  exists c_op, get_case h op = Some c_op.
Proof.
revert Γ Σ. induction h; intros Γ Σ typed gets; inv typed; inv H2.
+ simpl in gets. discriminate.
+ simpl in *. destruct (op==o); eauto.
Qed.

Lemma case_has_type Γ h Σ D op A B c:
  has_htype Γ h Σ D -> get_op_type Σ op = Some (A, B) ->
  get_case h op = Some c ->
  has_ctype (CtxU (CtxU Γ (TyFun B D)) A) c D.
Proof.
revert Σ. induction h; intros Σ tys gets finds.
simpl in finds. discriminate.
simpl in *. destruct (op==o).
- inv tys. inv H2. simpl in *. destruct (o==o).
  + inv finds. inv gets. auto.
  + destruct n; auto.
- inv tys. inv H2. eapply IHh; eauto.
  simpl in gets. destruct (op==o); eauto.
  rewrite e in n. destruct n. auto.
Qed. 

(* ==================== Computation Shapes ==================== *)

(* Return *)
Fixpoint shape_ret_full Γ c C v A Σ E (orig : has_ctype Γ c C) {struct orig} :
  c = Ret v -> C = CTy A Σ E -> 
  has_vtype Γ v A.
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate.
+ clear shape_ret_full. inv same. inv samety. auto.
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
  c = Absurd v -> has_vtype Γ v TyØ.
Proof.  
intros same. destruct orig. 
destruct H1; try discriminate; inv same; auto.
apply (shape_absurd_full _ _ _ v) in H1; auto.
Qed.


Fixpoint shape_absurd Γ v C :
  has_ctype Γ (Absurd v) C -> has_vtype Γ v TyØ.
Proof.  
intro orig. eapply (shape_absurd_full _ _ _ v) in orig; auto.
Qed.


(* ΠMatch *)
Fixpoint shape_prodmatch_full Γ c v c' C
  (orig : has_ctype Γ c C) {struct orig} :
  c = ΠMatch v c' ->
  exists A B,
    has_vtype Γ v (TyΠ A B) /\ has_ctype (CtxU (CtxU Γ A) B) c' C.
Proof.  
intros same. destruct orig. destruct H1; try discriminate; inv same.
+ clear shape_prodmatch_full. exists A, B. auto.
+ apply (shape_prodmatch_full _ _ v c') in H1; eauto.
  destruct H1 as [A' [B' [vty]]].
  exists A', B'. aconstructor.
  apply TypeC; try (inv H1; assumption). eapply TypeCSubtype; eauto.
Qed.


Fixpoint shape_prodmatch Γ v c C :
  has_ctype Γ (ΠMatch v c) C ->
  exists A B,
    has_vtype Γ v (TyΠ A B) /\  has_ctype (CtxU (CtxU Γ A) B) c C.
Proof.
intro orig. apply (shape_prodmatch_full _ _ v c) in orig; auto.
Qed.


(* ΣMatch *)
Fixpoint shape_summatch_full Γ c v c1 c2 C
  (orig : has_ctype Γ c C) {struct orig} :
  c = ΣMatch v c1 c2 ->
  exists A B,
    has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) c1 C /\ has_ctype (CtxU Γ B) c2 C.
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_summatch_full. inv same. exists A, B. auto.
+ apply (shape_summatch_full _ _ v c1 c2) in H1; eauto.
  destruct H1 as [A' [B' [vty]]].
  exists A', B'. aconstructor.
  inv H1. constructor; apply TypeC; auto.
  all: (eapply TypeCSubtype; eauto) || (inv H3; inv H4; assumption).
Qed.


Fixpoint shape_summatch Γ v c1 c2 C :
  has_ctype Γ (ΣMatch v c1 c2) C ->
  exists A B,
    has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) c1 C /\ has_ctype (CtxU Γ B) c2 C.
Proof.
intro orig. apply (shape_summatch_full _ _ v c1 c2) in orig; auto.
Qed.


(* ListMatch *)
Fixpoint shape_listmatch_full Γ c v c1 c2 C
  (orig : has_ctype Γ c C) {struct orig} :
  c = ListMatch v c1 c2 ->
  exists A,
    has_vtype Γ v (TyList A) /\
    has_ctype Γ c1 C /\ has_ctype (CtxU (CtxU Γ A) (TyList A)) c2 C.
Proof.
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_listmatch_full. inv same. exists A. auto.
+ apply (shape_listmatch_full _ _ v c1 c2) in H1; eauto.
  destruct H1 as [A' [vty[ty1 ty2]]].
  exists A'. aconstructor. constructor; apply TypeC; auto.
  all: (eapply TypeCSubtype || inv ty2); eauto.
Qed.


Fixpoint shape_listmatch Γ v c1 c2 C:
  has_ctype Γ (ListMatch v c1 c2) C ->
  exists A,
    has_vtype Γ v (TyList A) /\
    has_ctype Γ c1 C /\ has_ctype (CtxU (CtxU Γ A) (TyList A)) c2 C.
Proof.
intro orig. eapply shape_listmatch_full in orig; eauto.
Qed.


(* App *)
Fixpoint shape_app_full Γ c v1 v2 C (orig : has_ctype Γ c C) {struct orig} :
  c = App v1 v2 ->
  exists A,
    has_vtype Γ v1 (TyFun A C) /\ has_vtype Γ v2 A.
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_app_full. inv same. exists A. auto.
+ apply (shape_app_full _ _ v1 v2) in H1; eauto.
  destruct H1 as [A' [fty]].
  exists A'. aconstructor. apply TypeV. auto.
  - inv fty. inv H4. apply WfTyFun; auto.
  - eapply TypeVSubtype. exact fty. apply SubtypeTyFun.
    apply vsubtype_refl. inv fty. inv H4. all: auto.
Qed.


Fixpoint shape_app Γ c v C :
  has_ctype Γ (App (Fun c) v) C ->
  exists A, has_ctype (CtxU Γ A) c C /\ has_vtype Γ v A.
Proof.
intro orig. eapply (shape_app_full _ _ (Fun c) v C) in orig; eauto.
destruct orig as [A [fty]]. apply shape_fun in fty. eauto.
Qed.


(* Handle *)
Fixpoint shape_handle_full Γ c v c' C (orig : has_ctype Γ c C) {struct orig} :
  c = Handle v c' ->
  exists C',
    has_vtype Γ v (TyHandler C' C) /\ has_ctype Γ c' C'.
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_handle_full. inv same. exists C. auto.
+ apply (shape_handle_full _ _ v c') in H1; auto.
  destruct H1 as [D [vty]].
  exists D. aconstructor. inv H1.
  apply TypeV. auto. apply WfTyHandler; auto.
  eapply TypeVSubtype. exact vty.
  apply SubtypeTyHandler. apply csubtype_refl. all: auto.
Qed.


Fixpoint shape_handle Γ v c D :
  has_ctype Γ (Handle v c) D ->
  exists C, has_vtype Γ v (TyHandler C D) /\ has_ctype Γ c C.
Proof.
intro orig. eapply (shape_handle_full _ _ v c D) in orig; auto.
Qed.


(* LetRec *)
Fixpoint shape_letrec_full Γ c c1 c2 D
  (orig : has_ctype Γ c D) {struct orig} :
  c = LetRec c1 c2 ->
  exists A C,
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
    has_ctype (CtxU Γ (TyFun A C)) c2 D.
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_letrec_full. inv same. exists A, C. auto.
+ apply (shape_letrec_full _ _ c1 c2) in H1; eauto.
  destruct H1 as [A' [C'' [cty]]]. inv H1.
  exists A', C''. aconstructor. apply TypeC; auto.
  eapply TypeCSubtype. 2: eauto. apply TypeC; assumption.
Qed.


Fixpoint shape_letrec Γ c1 c2 D :
  has_ctype Γ (LetRec c1 c2) D ->
  exists A C, 
    has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
    has_ctype (CtxU Γ (TyFun A C)) c2 D.
Proof.
intro orig. eapply (shape_letrec_full _ _ c1 c2 D) in orig; auto.
Qed.


(* DoBind *)
Fixpoint shape_dobind_full Γ c C c1 c2 A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = DoBind c1 c2 -> C = CTy A Σ E ->
  exists A',
    has_ctype Γ c1 (CTy A' Σ E) /\ has_ctype (CtxU Γ A') c2 C.
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. clear shape_dobind_full. exists A0. auto.
+ destruct C as (A', Σ', E').
  apply (shape_dobind_full _ _ (CTy A' Σ' E') c1 c2 A' Σ' E') in H1; eauto.
  destruct H1 as [A'' [cty]].
  exists A''. constructor.
  - apply TypeC. auto. inv cty. inv H0. inv H4.
    apply WfCTy; auto. eapply TypeCSubtype. exact cty.
    inv H2. inv cty. inv H3. apply SubtypeCTy; auto. apply vsubtype_refl; auto.
  - apply TypeC. inv H1. 3: eapply TypeCSubtype. all: eauto.
Qed.


Fixpoint shape_dobind Γ c1 c2 A Σ E :
  has_ctype Γ (DoBind c1 c2) (CTy A Σ E) ->
  exists A',
    has_ctype Γ c1 (CTy A' Σ E) /\ 
    has_ctype (CtxU Γ A') c2 (CTy A Σ E).
Proof.  
intro orig. eapply (shape_dobind_full _ _ _ c1 c2 A Σ E) in orig; auto.
Qed.


(* Op *)
Fixpoint shape_op_full Γ c C op v c' A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = Op op v c' -> C = CTy A Σ E ->
  exists Aop Bop,
    get_op_type Σ op = Some (Aop, Bop) /\
    has_vtype Γ v Aop /\  has_ctype (CtxU Γ Bop) c' C.
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. eauto.
+ destruct C as (A', Σ', E').
  apply (shape_op_full _ _ (CTy A' Σ' E') op v c' A' Σ' E') in H1; eauto.
  destruct H1 as [A'' [B'' [g [vty]]]]. inv H2.
  eapply sig_subtype_get_Some in g; eauto.
  destruct g as [A'''[B'''[g'[s']]]].
  exists A''', B'''. aconstructor. constructor.
  - apply TypeV. auto. apply get_op_type_wf in g'. destruct g'.
    auto. inv H0. auto. eapply TypeVSubtype; eauto.
  - eapply (ctx_subtype_ctype (CtxU Γ B'') (CtxU Γ B''')).
    * apply TypeC. inv H1. auto. auto.
      eapply TypeCSubtype. eauto. apply SubtypeCTy; auto.
    * apply WfCtxU. auto. apply get_op_type_wf in g'. destruct g'.
      all: inv H0; auto.
    * apply SubtypeCtxU. apply ctx_subtype_refl. all: auto.
Qed.


Fixpoint shape_op Γ op v c A Σ E :
  has_ctype Γ (Op op v c) (CTy A Σ E) -> 
  exists Aop Bop,
    get_op_type Σ op = Some (Aop, Bop) /\
    has_vtype Γ v Aop /\  has_ctype (CtxU Γ Bop) c (CTy A Σ E).
Proof.  
intro orig. eapply (shape_op_full _ _ _ op v c A Σ E) in orig; auto.
Qed.
