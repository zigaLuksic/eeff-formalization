Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)

Require Import syntax declarational wellfounded_lemmas.


Ltac inv H := inversion H; clear H; subst.


(* ========================== Auxiliary Lemmas ========================== *)


Lemma sig_subtype_gets_Some Σ Σ' op A B :
  sig_subtype Σ Σ' -> get_op_type Σ op = Some (A, B) -> exists A' B', 
  get_op_type Σ' op = Some (A', B') /\ vsubtype A' A /\ vsubtype B B'.
Proof.
intros sty gets. induction sty; simpl in gets. discriminate.
destruct (op == op0).
- injection gets. intros. subst. exists A'. exists B'.
  constructor. assumption. constructor; assumption.
- apply IHsty in gets. assumption.
Qed.


Lemma sig_subtype_gets_None Σ Σ' op :
  sig_subtype Σ Σ' -> get_op_type Σ' op = None -> get_op_type Σ op = None.
Proof.
intros sty gets. induction sty; simpl. reflexivity.
destruct (op == op0).
- rewrite e in *. rewrite gets in H. discriminate.
- apply IHsty. assumption.
Qed.


Lemma sig_subtype_extend Σ Σ' op A B :
  sig_subtype Σ Σ' -> wf_sig (SigU Σ' op A B) -> sig_subtype Σ (SigU Σ' op A B).
Proof.
intros.
induction H.
+ apply SigØsubty.
+ eapply SigUsubty.
  - apply IHsig_subtype. assumption.
  - inv H0. simpl. destruct (op0 == op). 
    * rewrite e in *. rewrite H1 in H9. discriminate.
    * exact H1.
  - assumption.
  - assumption.
Qed.


Lemma sig_subtype_sigempty Σ : sig_subtype Σ SigØ -> Σ = SigØ.
Proof.
intro subty. inv subty. reflexivity. simpl in H1. discriminate.
Qed.


Lemma eqs_subtype_extend E E' Σ Γ Z T1 T2 :
  eqs_subtype E E' -> wf_eqs (EqsU E' Γ Z T1 T2) Σ ->
  eqs_subtype E (EqsU E' Γ Z T1 T2).
Proof.
intros. induction H.
apply EqsØsubty.
eapply EqsUsubty.
- apply IHeqs_subtype. assumption.
- simpl. right. assumption.
Qed.


Lemma eqs_subtype_contains E E' Γ Z T1 T2 :
  eqs_subtype E E' -> eqs_contain_eq E Γ Z T1 T2 -> eqs_contain_eq E' Γ Z T1 T2.
Proof.
intros sty gets. induction sty; simpl in gets; destruct gets.
- destruct H0 as [a [b [c ]]]. subst. assumption.
- apply IHsty. assumption.
Qed.


(* ========================== Basic Properties ========================== *)

Lemma vsubtype_refl v : wf_vtype v -> vsubtype v v
with csubtype_refl c : wf_ctype c -> csubtype c c
with sig_subty_refl Σ : wf_sig Σ -> sig_subtype Σ Σ
with eqs_subty_refl E Σ : wf_eqs E Σ -> eqs_subtype E E
with ctx_subty_refl Γ : wf_ctx Γ -> ctx_subtype Γ Γ.
Proof.
{intros; induction v; inv H.
+ apply VsubtyUnit.
+ apply VsubtyInt.
+ apply VsubtyTyØ.
+ apply VsubtyTyΣ; auto.
+ apply VsubtyTyΠ; auto.
+ apply VsubtyFun. apply IHv. assumption. apply csubtype_refl. assumption.
+ apply VsubtyHandler; apply csubtype_refl; assumption.
}{ destruct c. intros. inv H. apply Csubty.
apply vsubtype_refl. assumption. 
apply sig_subty_refl. assumption.
eapply eqs_subty_refl. exact H5.
}{ 
intros; induction Σ.
+ apply SigØsubty.
+ eapply SigUsubty.
  - apply sig_subtype_extend. apply IHΣ. inv H. assumption. assumption.
  - simpl. destruct (o==o). reflexivity. destruct n. reflexivity.
  - apply vsubtype_refl. inv H. assumption.
  - apply vsubtype_refl. inv H. assumption.
}{induction E; intros.
+ apply EqsØsubty.
+ apply EqsUsubty. inv H. eapply eqs_subtype_extend. 
  - apply IHE. assumption.
  - apply WfEqsU. exact H6. assumption. assumption.
  - simpl. left. auto.
}
{clear csubtype_refl sig_subty_refl eqs_subty_refl ctx_subty_refl.
induction Γ; intros.
apply CtxØsubty.
apply CtxUsubty; inv H. apply IHΓ. assumption. 
apply vsubtype_refl. assumption.
}
Qed.



Fixpoint eqs_subtype_trans E1 E2 E3  
  (E12 : eqs_subtype E1 E2) {struct E12} : 
  eqs_subtype E2 E3 -> eqs_subtype E1 E3.
Proof.
intros E23. destruct E12.
apply EqsØsubty.
eapply EqsUsubty.
+ eapply eqs_subtype_trans. exact E12. all : assumption.
+ eapply eqs_subtype_contains. exact E23. assumption.
Qed.


(* Weird notation for SPEED! *)
Fixpoint vsubtype_trans A1 A2 A3 
  (A12 : vsubtype A1 A2) {struct A12} : vsubtype A2 A3 -> vsubtype A1 A3

with vsubtype_trans_rev A1 A2 A3
  (A21 : vsubtype A2 A1) {struct A21} : vsubtype A3 A2 -> vsubtype A3 A1

with csubtype_trans C1 C2 C3
  (C12 : csubtype C1 C2) {struct C12} : csubtype C2 C3 -> csubtype C1 C3

with csubtype_trans_rev C1 C2 C3 
  (C21 : csubtype C2 C1) {struct C21} : csubtype C3 C2 -> csubtype C3 C1

with sig_subtype_trans Σ1 Σ2 Σ3 
  (S12 : sig_subtype Σ1 Σ2) {struct S12} : sig_subtype Σ2 Σ3 -> 
  sig_subtype Σ1 Σ3

with sig_subtype_trans_rev Σ1 Σ2 Σ3
  (S21 : sig_subtype Σ2 Σ1) {struct S21} : sig_subtype Σ3 Σ2 -> 
  sig_subtype Σ3 Σ1

with get_op_trans op A' A B B' Σ1 Σ2 (S12 : sig_subtype Σ1 Σ2) {struct S12} :
  get_op_type Σ1 op = Some (A', B') -> vsubtype A' A -> vsubtype B B' ->
  exists A'' B'', 
  get_op_type Σ2 op = Some (A'', B'') /\ vsubtype A'' A /\ vsubtype B B''.
Proof.
{
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros A23; destruct A12; try assumption; inv A23. 
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans. exact A12_1. assumption.
  - eapply vsubtype_trans. exact A12_2. assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans. exact A12_1. assumption.
  - eapply vsubtype_trans. exact A12_2. assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans_rev. exact A12. assumption. 
  - eapply csubtype_trans. exact H. assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans_rev. exact H. assumption. 
  - eapply csubtype_trans. exact H0. assumption.
}{
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros A32; destruct A21; try assumption; inv A32. 
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans_rev. exact A21_1. assumption.
  - eapply vsubtype_trans_rev. exact A21_2. assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans_rev. exact A21_1. assumption.
  - eapply vsubtype_trans_rev. exact A21_2. assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans. exact A21. assumption. 
  - eapply csubtype_trans_rev. exact H. assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans. exact H. assumption. 
  - eapply csubtype_trans_rev. exact H0. assumption.
}{
clear vsubtype_trans_rev csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans_rev get_op_trans.
intros C23; destruct C12. inv C23. apply Csubty.
- eapply vsubtype_trans. exact H. assumption.
- eapply sig_subtype_trans. exact H0. assumption.
- eapply eqs_subtype_trans. exact H1. assumption.
}{
clear vsubtype_trans csubtype_trans csubtype_trans.
clear sig_subtype_trans get_op_trans.
intros C32; destruct C21. inv C32. apply Csubty.
- eapply vsubtype_trans_rev. exact H. assumption.
- eapply sig_subtype_trans_rev. exact H0. assumption.
- eapply eqs_subtype_trans. exact H8. assumption.
}{
clear csubtype_trans csubtype_trans_rev sig_subtype_trans_rev.
intros S23. destruct S12.
apply SigØsubty.
apply (sig_subtype_gets_Some Σ' Σ3) in H as H'.
destruct H' as [A'' [B'' [g]]]. eapply SigUsubty.
2 : exact g. all: try assumption.
+ eapply sig_subtype_trans. exact S12. assumption.
+ clear sig_subtype_trans vsubtype_trans.
  destruct H2. eapply vsubtype_trans_rev. exact H0. assumption.
+ clear sig_subtype_trans vsubtype_trans_rev.
  destruct H2. eapply vsubtype_trans. exact H1. assumption.
}{
clear csubtype_trans csubtype_trans_rev sig_subtype_trans.
intros S32. destruct S21.
apply sig_subtype_sigempty in S32. subst. apply SigØsubty.
induction Σ3.
apply SigØsubty.
inv S32. simpl in H8. destruct (o==op).
+ injection H8. intros. subst. eapply SigUsubty.
  - apply IHΣ3. assumption.
  - exact H.
  - eapply vsubtype_trans. exact H0. assumption.
  - eapply vsubtype_trans_rev. exact H1. assumption.
+ eapply get_op_trans in H8 as gets'.
  2:exact S21. 2:exact H9. 2:exact H10.
  destruct gets' as [A'' [B'' [gets' [styA'']]]]. eapply SigUsubty.
  2: exact gets'. all: try assumption.
  apply IHΣ3. assumption.
}{
clear csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans sig_subtype_trans_rev get_op_trans.
intros. revert H. induction S12; intros gets.
simpl in gets. discriminate.
simpl in *. destruct (op==op0).
+ injection gets. intros. subst.
  exists A'0. exists B'0. constructor. assumption. constructor.
  eapply vsubtype_trans. exact H2. assumption.
  eapply vsubtype_trans_rev. exact H3. assumption.
+ apply IHS12. assumption.
}
Qed.


Fixpoint ctx_subtype_get Γ Γ' A num (csty : ctx_subtype Γ Γ') {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A A'.
Proof.
revert num. induction csty. clear ctx_subtype_get.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num.
  - clear IHcsty. simpl in *. injection get. intros. subst. exists A'.
    constructor. reflexivity. assumption.
  - simpl in *. eapply IHcsty. exact get.
Qed.


Fixpoint ctx_subtype_get_rev Γ Γ' A num (csty : ctx_subtype Γ' Γ) {struct csty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A' A.
Proof.
revert num. induction csty. clear ctx_subtype_get_rev.
+ intros num H. simpl in H. discriminate.
+ intros num get. destruct num.
  - clear IHcsty. simpl in *. injection get. intros. subst. exists A0.
    constructor. reflexivity. assumption.
  - simpl in *. eapply IHcsty. exact get.
Qed.


Fixpoint ctx_subtype_vtype Γ Γ' v A (types : has_vtype Γ v A) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ  -> has_vtype Γ' v A

with ctx_subtype_ctype Γ Γ' c C (types : has_ctype Γ c C ) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_ctype Γ' c C

with ctx_subtype_htype Γ Γ' h Σ D (types : has_htype Γ h Σ D) {struct types}:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_htype Γ' h Σ D.
Proof.
{
intros wf ctxsty.
destruct types. induction H1; apply TypeV; try assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply (ctx_subtype_get_rev _ _ A num) in ctxsty.
  destruct ctxsty as [A' [gets]]. 
  eapply TypeVSubtype.
  - apply TypeV. assumption. apply ctx_gets_wf in gets as wfA'.
    exact wfA'. assumption. apply TypeVar. assumption.
  - assumption.
  - assumption.
+ apply TypePair; apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeInl. apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeInr. apply (ctx_subtype_vtype Γ Γ'); assumption.
+ apply TypeFun. eapply ctx_subtype_ctype.
  - exact H1.
  - apply WfCtxU. assumption. inv H0. assumption.
  - apply CtxUsubty. exact ctxsty. apply vsubtype_refl. inv H0. assumption.
+ apply TypeHandler. eapply ctx_subtype_ctype.
  - exact H1.
  - apply WfCtxU. assumption. inv H0. inv H5. assumption.
  - apply CtxUsubty. exact ctxsty. apply vsubtype_refl.
    inv H0. inv H5. assumption.
  - eapply (ctx_subtype_htype Γ Γ'); assumption.
+ eapply TypeVSubtype. 2 : exact H2.
  eapply (ctx_subtype_vtype Γ Γ'); assumption.
}{
intros wf ctxsty.
destruct types. induction H1; apply TypeC; try assumption.
+ apply TypeRet. eapply (ctx_subtype_vtype Γ Γ'); assumption.
+ eapply TypeΠMatch.
  - eapply (ctx_subtype_vtype Γ Γ'). exact H1. all: assumption.
  - eapply ctx_subtype_ctype.
    * exact H2.
    * inv H2. inv H3. inv H7. apply WfCtxU. apply WfCtxU. all: assumption.
    * apply CtxUsubty. apply CtxUsubty. exact ctxsty.
      all: inv H2; inv H3; inv H7; apply vsubtype_refl; assumption.
+ eapply TypeΣMatch.
  - eapply ctx_subtype_vtype.  exact H1. all: assumption.
  - eapply ctx_subtype_ctype. exact H2. all: inv H2; inv H4. 
    * apply WfCtxU; assumption.
    * apply CtxUsubty. exact ctxsty. apply vsubtype_refl. assumption.
  - eapply ctx_subtype_ctype. exact H3. all: inv H3; inv H4. 
    * apply WfCtxU; assumption.
    * apply CtxUsubty. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeDoBind.
  - eapply ctx_subtype_ctype. exact H1. all: assumption.
  - inv H1. inv H4. eapply ctx_subtype_ctype.
    * exact H2.
    * apply WfCtxU; assumption.
    * apply CtxUsubty. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeApp.
  - eapply ctx_subtype_vtype. exact H1. all: assumption.
  - eapply ctx_subtype_vtype. exact H2. all: assumption.
+ eapply TypeHandle.
  - eapply ctx_subtype_vtype. exact H1. all: assumption.
  - eapply ctx_subtype_ctype. exact H2. all: assumption.
+ eapply TypeLetRec.
  - eapply ctx_subtype_ctype. exact H1. all: inv H2; inv H3.
    * apply WfCtxU. apply WfCtxU. assumption. inv H8. exact H6. exact H8.
    * apply CtxUsubty. apply CtxUsubty. exact ctxsty.
      apply vsubtype_refl. inv H8. assumption. apply vsubtype_refl. assumption.
  - eapply ctx_subtype_ctype. exact H2. all: inv H2; inv H3.
    * apply WfCtxU; assumption.
    * apply CtxUsubty. exact ctxsty. apply vsubtype_refl. assumption.
+ eapply TypeOp.
  exact H1. eapply ctx_subtype_vtype. exact H2. assumption. assumption.
  eapply ctx_subtype_ctype. exact H3. all: inv H3; inv H4.
  - apply WfCtxU; assumption.
  - apply CtxUsubty. assumption. apply vsubtype_refl. assumption.
+ eapply TypeCSubtype. 2: exact H2.
  eapply ctx_subtype_ctype. exact H1. all: assumption.
}{
intros wf ctxsty.
destruct types. induction H2; apply TypeH; try assumption.
+ eapply TypeCasesØ.
+ eapply TypeCasesU. assumption.
  eapply ctx_subtype_htype. exact H3. assumption. assumption.
  eapply ctx_subtype_ctype. exact H4.
  all: inv H4; inv H5; inv H9.
  - apply WfCtxU. apply WfCtxU. all: assumption.
  - apply CtxUsubty. apply CtxUsubty. assumption.
    all: apply vsubtype_refl; assumption. 
}
Qed.


(* ========================== Subtype Shapes ========================== *)


Fixpoint subty_shape_pair A B C : vsubtype C (TyΠ A B) -> 
  exists A' B', C = (TyΠ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists B0.
constructor. reflexivity. constructor; assumption.
Qed.


Fixpoint subty_shape_sum A B C : vsubtype C (TyΣ A B) -> 
  exists A' B', C = (TyΣ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists B0.
constructor. reflexivity. constructor; assumption.
Qed.


Fixpoint subty_shape_fun A B C : vsubtype C (TyFun A B) -> 
  exists A' B', C = (TyFun A' B') /\ vsubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists A0. exists C0.
constructor. reflexivity. constructor; assumption.
Qed.


Fixpoint subty_shape_handler A B C : vsubtype C (TyHandler A B) -> 
  exists A' B', C = (TyHandler A' B') /\ csubtype A A' /\ csubtype B' B.
Proof.
intro orig. inv orig. exists C0. exists D.
constructor. reflexivity. constructor; assumption.
Qed.


(* ========================== Value Shapes ========================== *)


(* Pair *)
Fixpoint shape_pair_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΠ A B ->
  (exists name num, v = Var (name, num)) \/
  (exists v1 v2, v = Pair v1 v2 /\ has_vtype Γ v1 A /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_pair_full. left. exists name. exists num. reflexivity.
+ clear shape_pair_full. right. exists v1. exists v2. 
  constructor. reflexivity. injection same. intros. subst. 
  constructor; assumption.
+ rewrite same in H2. apply subty_shape_pair in H2. 
  destruct H2 as [A'' [B'' [pity]]]. subst. 
  apply (shape_pair_full _ _ A'' B'') in H1. clear shape_pair_full. 
  2: reflexivity. destruct H1.
  - left. assumption.
  - right. destruct H1 as [v1 [v2]]. exists v1. exists v2.
    constructor. destruct H1. assumption.
    constructor; destruct H1; destruct H3; destruct H2;
    apply TypeV; inv H0; try assumption. 
    * eapply TypeVSubtype. exact H3. assumption.
    * eapply TypeVSubtype. exact H4. assumption.
Qed.


Lemma shape_pair Γ v1 v2 A B :
  has_vtype Γ (Pair v1 v2) (TyΠ A B) ->  
  has_vtype Γ v1 A /\ has_vtype Γ v2 B.
Proof.
intro orig.
apply (shape_pair_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ destruct H as [v1' [v2' [same]]]. injection same. intros. subst. assumption.
Qed.


(* Sum *)
Fixpoint shape_sum_full Γ v A B ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyΣ A B ->
  (exists name num, v = Var (name, num)) \/
  (exists v1, v = Inl v1 /\ has_vtype Γ v1 A) \/
  (exists v2, v = Inr v2 /\ has_vtype Γ v2 B).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_sum_full. left. exists name. exists num. reflexivity.
+ clear shape_sum_full. right. left. exists v. constructor. reflexivity.
  inv same. assumption.
+ clear shape_sum_full. right. right. exists v. constructor. reflexivity.
  inv same. assumption.
+ rewrite same in H2. apply subty_shape_sum in H2. 
  destruct H2 as [A'' [B'' [sigty]]]. subst. 
  apply (shape_sum_full _ _ A'' B'') in H1. clear shape_sum_full. 
  2: reflexivity. destruct H1.
  - left. assumption.
  - right. destruct H1.
    * left. destruct H1. exists x. destruct H1. constructor. assumption.
      apply TypeV. assumption. inv H0. assumption. eapply TypeVSubtype.
      exact H3. destruct H2. assumption.
    * right. destruct H1. exists x. destruct H1. constructor. assumption.
      apply TypeV. assumption. inv H0. assumption. eapply TypeVSubtype.
      exact H3. destruct H2. assumption.
Qed.


Lemma shape_sum_inl Γ v A B :
  has_vtype Γ (Inl v) (TyΣ A B) -> has_vtype Γ v A.
Proof.
intro orig.
apply (shape_sum_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ destruct H; destruct H; destruct H.
  - inv H. assumption.
  - discriminate.
Qed.


Lemma shape_sum_inr Γ v A B :
  has_vtype Γ (Inr v) (TyΣ A B) -> has_vtype Γ v B.
Proof.
intro orig.
apply (shape_sum_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ destruct H; destruct H; destruct H.
  - discriminate.
  - inv H. assumption.
Qed.


(* Function *)
Fixpoint shape_fun_full Γ v A C ty (orig : has_vtype Γ v ty) {struct orig} :
  ty = TyFun A C ->
  (exists name num, v = Var (name, num)) \/
  (exists x c, v = Fun x c /\ has_ctype (CtxU Γ A) c C).
Proof.
intros same.
destruct orig. destruct H1; try discriminate.
+ clear shape_fun_full. left. exists name. exists num. reflexivity.
+ clear shape_fun_full. right. exists x. exists c. constructor. reflexivity.
  inv same. assumption.
+ rewrite same in H2. apply subty_shape_fun in H2. 
  destruct H2 as [A'' [C'' [funty]]]. subst. 
  apply (shape_fun_full _ _ A'' C'') in H1. clear shape_fun_full. 
  2: reflexivity. destruct H1.
  - left. assumption.
  - right. destruct H1. destruct H1 as [c']. exists x. exists c'.
    destruct H1. constructor. assumption.
    apply TypeC; inv H0.
    * apply WfCtxU; assumption.
    * assumption.
    * destruct H2. eapply TypeCSubtype. 2: exact H1.
      eapply ctx_subtype_ctype. exact H3.
      apply WfCtxU; assumption.
      apply CtxUsubty. apply ctx_subty_refl. assumption. assumption.
Qed.

Lemma shape_fun Γ x c A C :
  has_vtype Γ (Fun x c) (TyFun A C) -> has_ctype (CtxU Γ A) c C.
Proof.
intro orig.
apply (shape_fun_full _ _ A C) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ do 3 (destruct H). inv H. inv H0. apply TypeC; assumption.
Qed.


(* ========================== Computation Shapes ========================== *)


(* ΠMatch *)
Fixpoint shape_prodmatch_full Γ c v x y c' C
  (orig : has_ctype Γ c C) {struct orig} :
  c = (ΠMatch v (x, y) c') ->
  (exists A B, has_vtype Γ v (TyΠ A B) /\ has_ctype (CtxU (CtxU Γ A) B) c' C).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_prodmatch_full. 
  inv same. exists A. exists B. constructor; assumption.
+ apply (shape_prodmatch_full _ _ v x y c') in H1; clear shape_prodmatch_full. 
  2: assumption. destruct H1 as [A' [B' [vty]]].
  exists A'. exists B'. constructor. assumption.
  apply TypeC.
  - inv H1. assumption.
  - assumption.
  - eapply TypeCSubtype. exact H1. assumption.
Qed.


Fixpoint shape_prodmatch Γ v x y c C :
  has_ctype Γ (ΠMatch v (x, y) c) C ->
  (exists A B, has_vtype Γ v (TyΠ A B) /\  has_ctype (CtxU (CtxU Γ A) B) c C).
Proof.
intro orig. apply (shape_prodmatch_full _ _ v x y c) in orig.
2: reflexivity. assumption.
Qed.


(* ΣMatch *)
Fixpoint shape_summatch_full Γ c v xl cl xr cr C
  (orig : has_ctype Γ c C) {struct orig} :
  c = (ΣMatch v xl cl xr cr) ->
  (exists A B, has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) cl C /\ has_ctype (CtxU Γ B) cr C).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_summatch_full. 
  inv same. exists A. exists B. constructor. assumption.
  constructor ; assumption.
+ apply (shape_summatch_full _ _ v xl cl xr cr) in H1;
  clear shape_summatch_full. 2: assumption.
  destruct H1 as [A' [B' [vty]]].
  exists A'. exists B'. constructor. assumption.
  inv H1. constructor; apply TypeC; auto.
  - inv H3. assumption.
  - eapply TypeCSubtype. exact H3. assumption.
  - inv H4. assumption.
  - eapply TypeCSubtype. exact H4. assumption.
Qed.


Fixpoint shape_summatch Γ v xl cl xr cr C :
  has_ctype Γ (ΣMatch v xl cl xr cr) C ->
  (exists A B, has_vtype Γ v (TyΣ A B) /\
    has_ctype (CtxU Γ A) cl C /\ has_ctype (CtxU Γ B) cr C).
Proof.
intro orig. apply (shape_summatch_full _ _ v xl cl xr cr) in orig.
2: reflexivity. assumption.
Qed.


(* App *)
Fixpoint shape_app_full Γ c x c' v C (orig : has_ctype Γ c C) {struct orig} :
  c = (App (Fun x c') v) ->
  (exists A, has_ctype (CtxU Γ A) c' C /\ has_vtype Γ v A).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_app_full. 
  inv same. exists A. apply shape_fun in H1. constructor; assumption.
+ apply (shape_app_full _ _ x c' v) in H1;
  clear shape_app_full. 2: assumption.
  destruct H1 as [A' [cty]].
  exists A'. constructor. 2: assumption.
  inv cty. apply TypeC; auto.
  eapply TypeCSubtype. apply TypeC.
  assumption. exact H4. exact H5. assumption.
Qed.


Fixpoint shape_app Γ x c v C :
  has_ctype Γ (App (Fun x c) v) C ->
  (exists A, has_ctype (CtxU Γ A) c C /\ has_vtype Γ v A).
Proof.
intro orig. eapply (shape_app_full _ _ x c v C) in orig.
2: reflexivity. assumption.
Qed.


(* LetRec *)
Fixpoint shape_letrec_full Γ c f x c1 c2 D
  (orig : has_ctype Γ c D) {struct orig} :
  c = (LetRec f x c1 c2) ->
  (exists A C, has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
  has_ctype (CtxU Γ (TyFun A C)) c2 D).
Proof.  
intros same. destruct orig. destruct H1; try discriminate.
+ clear shape_letrec_full. 
  inv same. exists A. exists C. constructor; assumption.
+ apply (shape_letrec_full _ _ f x c1 c2) in H1;
  clear shape_letrec_full. 2: assumption.
  destruct H1 as [A' [C'' [cty]]].
  exists A'. exists C''. constructor. assumption.
  inv H1. apply TypeC; auto.
  eapply TypeCSubtype. 2: exact H2. apply TypeC; assumption.
Qed.


Fixpoint shape_letrec Γ f x c1 c2 D :
  has_ctype Γ (LetRec f x c1 c2) D ->
  (exists A C, has_ctype (CtxU (CtxU Γ A) (TyFun A C)) c1 C /\ 
    has_ctype (CtxU Γ (TyFun A C)) c2 D).
Proof.
intro orig. eapply (shape_letrec_full _ _ f x c1 c2 D) in orig.
2: reflexivity. assumption.
Qed.


(* DoBind *)
Fixpoint shape_dobind_full Γ c C x c1 c2 A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = (DoBind x c1 c2) -> C = (CTy A Σ E) ->
  (exists A', has_ctype Γ c1 (CTy A' Σ E) /\ has_ctype (CtxU Γ A') c2 C).
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. clear shape_dobind_full. 
  exists A0. constructor; assumption.
+ destruct C as (A', Σ', E').
  apply (shape_dobind_full _ _ (CTy A' Σ' E') x c1 c2 A' Σ' E') in H1;
  clear shape_dobind_full. 2: reflexivity. 2: reflexivity.
  destruct H1 as [A'' [cty]].
  exists A''. constructor.
  - apply TypeC. assumption. inv cty. inv H0. inv H4.
    apply WfCty; assumption. eapply TypeCSubtype. exact cty.
     inv H2. inv cty. inv H3. 
    apply Csubty. apply vsubtype_refl. all: assumption.
  - apply TypeC. inv H1. assumption. assumption.
    eapply TypeCSubtype. exact H1. assumption.
Qed.


Fixpoint shape_dobind Γ x c1 c2 A Σ E :
  has_ctype Γ (DoBind x c1 c2) (CTy A Σ E) ->
  (exists A', has_ctype Γ c1 (CTy A' Σ E) /\ 
    has_ctype (CtxU Γ A') c2 (CTy A Σ E)).
Proof.  
intro orig. eapply (shape_dobind_full _ _ _ x c1 c2 A Σ E) in orig.
2: reflexivity. assumption. reflexivity.
Qed.


(* Return *)
Fixpoint shape_ret_full Γ c C v A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = (Ret v) -> C = (CTy A Σ E) -> has_vtype Γ v A.
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. assumption.
+ destruct C as (A', Σ', E').
  apply (shape_ret_full _ _ (CTy A' Σ' E') v A' Σ' E') in H1;
  clear shape_ret_full. 2: reflexivity. 2: reflexivity.
  - apply TypeV. assumption. inv H0. assumption.
    eapply TypeVSubtype. exact H1. inv H2. assumption.
Qed.


Fixpoint shape_ret Γ v A Σ E :
  has_ctype Γ (Ret v) (CTy A Σ E) -> has_vtype Γ v A.
Proof.  
intro orig. eapply (shape_ret_full _ _ _ v A Σ E) in orig.
2: reflexivity. assumption. reflexivity.
Qed.

(* Op
Fixpoint shape_op_full Γ c C op v y c' A Σ E
  (orig : has_ctype Γ c C) {struct orig} :
  c = (Op op v y c') -> C = (CTy A Σ E) ->
  (exists Aop Bop Aarg, get_op_type Σ op = Some (Aop, Bop) /\
  has_vtype Γ v Aarg /\ vsubtype Aop Aarg /\ has_ctype (CtxU Γ Bop) c' C).
Proof.  
intros same samety. destruct orig. destruct H1; try discriminate; inv same.
+ inv samety. clear shape_op_full. 
  exists A_op. exists B_op. exists A_op.
  constructor. assumption. constructor. assumption.
  constructor. apply vsubtype_refl. inv H2. assumption. assumption.
+ destruct C as (A', Σ', E').
  apply (shape_op_full _ _ (CTy A' Σ' E') op v y c' A' Σ' E') in H1;
  clear shape_op_full. 2: reflexivity. 2: reflexivity.
  destruct H1 as [A'' [B'' [Aarg [g [vty]]]]]. 
  inv H2. eapply sig_subtype_gets_Some in g. 2: exact H10.
  destruct g as [A''' [B''' [g' [sty']]]].
  exists A'''. exists B'''. exists Aarg. 
  constructor. assumption. constructor. assumption.
  constructor. eapply vsubtype_trans. exact sty'. destruct H1. assumption.
  destruct H1. apply (ctx_subtype_ctype (CtxU Γ B'') (CtxU Γ B''')).
  - apply TypeC. inv H3. assumption. assumption.
    eapply TypeCSubtype. exact H3. apply Csubty; assumption.
  - apply WfCtxU. assumption. apply get_op_type_wf in g'. destruct g'.
    assumption. inv H0. assumption.
  - apply CtxUsubty. apply ctx_subty_refl. assumption. assumption.

Qed. *)

