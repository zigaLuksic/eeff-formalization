(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".

Require Import syntax declarational wellfounded_lemmas.


Ltac inv H := inversion H; clear H; subst.

(* ========================== Auxiliary Lemmas ========================== *)

Lemma sig_subtype_gets_Some Σ Σ' op A B :
  sig_subtype Σ Σ' -> get_op_type Σ op = Some (A, B) -> exists A' B', 
  get_op_type Σ' op = Some (A', B') /\ vsubtype A' A /\ vsubtype B B'.
Proof.
intros sty gets. induction sty.
+ simpl in gets. discriminate.
+ simpl in gets. destruct (op == op0).
  - injection gets. intros. subst. exists A'. exists B'.
    constructor. assumption. constructor; assumption.
  - apply IHsty in gets. assumption.
Qed.

Lemma sig_subtype_gets_None Σ Σ' op :
  sig_subtype Σ Σ' -> get_op_type Σ' op = None -> get_op_type Σ op = None.
Proof.
intros sty gets. induction sty.
+ simpl. reflexivity.
+ simpl. destruct (op == op0).
  - rewrite e in *. rewrite gets in H0. discriminate.
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
  - assumption.
  - inv H0. simpl. destruct (op0 == op). 
    * rewrite e in *. rewrite H2 in H10. discriminate.
    * exact H2.
  - assumption.
  - assumption.
Qed.

Lemma sig_subtype_sigempty Σ : sig_subtype Σ SigØ -> Σ = SigØ.
Proof.
intro subty.
inv subty. reflexivity.
simpl in H1. discriminate.
Qed.

Lemma eqs_subtype_extend E E' Σ Γ Z T1 T2 :
  eqs_subtype E E' -> wf_eqs (EqsU E' Γ Z T1 T2) Σ ->
  eqs_subtype E (EqsU E' Γ Z T1 T2).
Proof.
intros.
induction H.
+ apply EqsØsubty.
+ eapply EqsUsubty.
  - apply IHeqs_subtype. assumption.
  - simpl. right. assumption.
Qed.

(* ========================== Basic Properties ========================== *)

Lemma vsubty_refl v : wf_vtype v -> vsubtype v v
with csubty_refl c : wf_ctype c -> csubtype c c
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
+ apply VsubtyFun. apply IHv. assumption. apply csubty_refl. assumption.
+ apply VsubtyHandler; apply csubty_refl; assumption.
}{ destruct c. intros. inv H. apply Csubty.
apply vsubty_refl. assumption. 
apply sig_subty_refl. assumption.
eapply eqs_subty_refl. exact H5.
}{ 
intros; induction Σ.
+ apply SigØsubty.
+ eapply SigUsubty.
  - apply sig_subtype_extend. apply IHΣ. inv H. assumption. assumption.
  - inv H. assumption.
  - simpl. destruct (o==o). reflexivity. destruct n. reflexivity.
  - apply vsubty_refl. inv H. assumption.
  - apply vsubty_refl. inv H. assumption.
}{induction E; intros.
+ apply EqsØsubty.
+ apply EqsUsubty. inv H. eapply eqs_subtype_extend. 
  - apply IHE. assumption.
  - apply WfEqsU. exact H6. assumption. assumption.
  - simpl. left. auto.
}{induction Γ; intros.
+ apply CtxØsubty.
+ apply CtxUsubty; inv H. apply IHΓ. assumption. apply vsubty_refl. assumption.
}
Qed.

(* stupid auxiliary definition for reverse sigma transitivity *)
Fixpoint remove_op_from_sig Σ op :=
  match Σ with
  | SigØ => SigØ
  | SigU Σ' op' A B => 
      if (op == op') then Σ' 
      else SigU (remove_op_from_sig Σ' op) op' A B
end.

Lemma remove_op_get_op Σ op op' :
  op <> op' -> get_op_type (remove_op_from_sig Σ op) op' = get_op_type Σ op'.
Proof.
intros. induction Σ.
+ auto.
+ simpl. destruct (op'==o); destruct (op==o).
  - subst. destruct H. reflexivity.
  - simpl. destruct (op'==o). reflexivity. subst. destruct n0. auto.
  - reflexivity.
  - simpl. destruct (op'==o). subst. destruct n. auto. assumption.
Qed.

Lemma remove_op_wf Σ op : wf_sig Σ -> wf_sig (remove_op_from_sig Σ op).
Proof.
intros. induction H.
+ simpl. apply WfSigØ.
+ simpl in *. destruct (op == op0). assumption. apply WfSigU.
  all: try assumption. rewrite remove_op_get_op; assumption.
Qed.

Lemma sig_remove_op_intro Σ Σ' op A B :
  wf_sig Σ' -> sig_subtype Σ (SigU Σ' op A B) -> 
  sig_subtype (remove_op_from_sig Σ op) Σ'.
Proof.
intros wf' orig.
induction Σ.
+ simpl. apply SigØsubty.
+ simpl. destruct (op==o).
  assert (forall Σ op, get_op_type Σ op = None -> remove_op_from_sig Σ op = Σ).
  { intros. induction Σ0. simpl. reflexivity. simpl in *.
    destruct (op0==o0). discriminate. f_equal. apply IHΣ0. assumption. }
  - inv orig. rewrite H in IHΣ. apply IHΣ. all: assumption.
  - inv orig. eapply SigUsubty. apply IHΣ. assumption.
    * rewrite remove_op_get_op. assumption. assumption.
    * simpl in H6. destruct (o==op). subst. destruct n. reflexivity.
      exact H6.
    * assumption.
    * assumption.
Qed.

Lemma sig_remove_op_elim Σ Σ' op A B :
  get_op_type Σ op = Some (A, B) ->
  sig_subtype (SigU (remove_op_from_sig Σ op) op A B) Σ' ->
  sig_subtype Σ Σ'.
Proof.
Admitted.

(* Weird notation for SPEED! *)
Fixpoint vsubtype_trans A1 A2 A3 
  (A12 : vsubtype A1 A2) {struct A12} : 
  wf_vtype A1 -> wf_vtype A2 -> wf_vtype A3 -> 
  vsubtype A2 A3 -> 
  vsubtype A1 A3
with vsubtype_trans_rev A1 A2 A3
  (A21 : vsubtype A2 A1) {struct A21} : 
  wf_vtype A1 -> wf_vtype A2 -> wf_vtype A3 -> 
  vsubtype A3 A2 ->
  vsubtype A3 A1
with csubtype_trans C1 C2 C3
  (C12 : csubtype C1 C2) {struct C12} : 
  wf_ctype C1 -> wf_ctype C2 -> wf_ctype C3 -> 
  csubtype C2 C3 -> 
  csubtype C1 C3
with csubtype_trans_rev C1 C2 C3 
  (C21 : csubtype C2 C1) {struct C21} : 
  wf_ctype C1 -> wf_ctype C2 -> wf_ctype C3 -> 
  csubtype C3 C2 -> 
  csubtype C3 C1
with sig_subtype_trans Σ1 Σ2 Σ3 
  (S12 : sig_subtype Σ1 Σ2) {struct S12} : 
  wf_sig Σ1 -> wf_sig Σ2 -> wf_sig Σ3 ->  
  sig_subtype Σ2 Σ3 -> 
  sig_subtype Σ1 Σ3
with sig_subtype_trans_rev Σ1 Σ2 Σ3
  (S21 : sig_subtype Σ2 Σ1) {struct S21} : 
  wf_sig Σ1 -> wf_sig Σ2 -> wf_sig Σ3 ->  sig_subtype Σ3 Σ2 ->
  sig_subtype Σ3 Σ1
with eqs_subtype_trans E1 E2 E3 Σ1 Σ2 Σ3 
  (E12 : eqs_subtype E1 E2) {struct E12} : 
  wf_eqs E1 Σ1 -> wf_eqs E2 Σ2 -> wf_eqs E3 Σ3 ->  
  eqs_subtype E2 E3 -> 
  eqs_subtype E1 E3
with eqs_subtype_trans_rev E1 E2 E3 Σ1 Σ2 Σ3
  (E21 : eqs_subtype E2 E1) {struct E21} : 
  wf_eqs E1 Σ1 -> wf_eqs E2 Σ2 -> wf_eqs E3 Σ3 ->  eqs_subtype E3 E2 ->
  eqs_subtype E3 E1.
Proof.
{
clear sig_subtype_trans sig_subtype_trans_rev.
clear eqs_subtype_trans eqs_subtype_trans_rev.
intros wf1 wf2 wf3 A23; destruct A12; try assumption; 
inv A23; inv wf1; inv wf2; inv wf3. 
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans. exact A12_1. all: assumption.
  - eapply vsubtype_trans. exact A12_2. all: assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans. exact A12_1. all: assumption.
  - eapply vsubtype_trans. exact A12_2. all: assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans_rev. exact A12. all: assumption. 
  - eapply csubtype_trans. exact H. all: assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans_rev. exact H. all: assumption. 
  - eapply csubtype_trans. exact H0. all: assumption.
}{
clear sig_subtype_trans sig_subtype_trans_rev.
clear eqs_subtype_trans eqs_subtype_trans_rev.
intros wf1 wf2 wf3 A32; destruct A21; try assumption;
inv A32; inv wf1; inv wf2; inv wf3. 
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans_rev. exact A21_1. all: assumption.
  - eapply vsubtype_trans_rev. exact A21_2. all: assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans_rev. exact A21_1. all: assumption.
  - eapply vsubtype_trans_rev. exact A21_2. all: assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans. exact A21. all: assumption. 
  - eapply csubtype_trans_rev. exact H. all: assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans. exact H. all: assumption. 
  - eapply csubtype_trans_rev. exact H0. all: assumption.
}{
clear vsubtype_trans_rev csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans_rev eqs_subtype_trans_rev.
intros wf1 wf2 wf3 C23; destruct C12. 
inv C23; inv wf1; inv wf2; inv wf3. 
apply Csubty.
- eapply vsubtype_trans. exact H. all: assumption.
- eapply sig_subtype_trans. exact H0. all: assumption.
- eapply eqs_subtype_trans. all: eauto.
}{
clear vsubtype_trans csubtype_trans csubtype_trans.
clear sig_subtype_trans eqs_subtype_trans.
intros wf1 wf2 wf3 C32; destruct C21. 
inv C32; inv wf1; inv wf2; inv wf3. 
apply Csubty.
- eapply vsubtype_trans_rev. exact H. all: assumption.
- eapply sig_subtype_trans_rev. exact H0. all: assumption.
- eapply eqs_subtype_trans_rev. all: eauto.
}{
clear csubtype_trans csubtype_trans_rev eqs_subtype_trans eqs_subtype_trans_rev.
intros wf1 wf2 wf3 S23. destruct S12.
apply SigØsubty.
apply (sig_subtype_gets_Some Σ' Σ3) in H0 as H0'. destruct H0' as [A'' [B'' [g]]].
eapply SigUsubty.
+ eapply sig_subtype_trans. exact S12. inv wf1. all : assumption.
+ assumption.
+ exact g.
+ clear sig_subtype_trans vsubtype_trans.
  destruct H3. eapply vsubtype_trans_rev. exact H1.
  - inv wf1. assumption.
  - apply get_op_type_wf in H0. destruct H0. assumption. assumption.
  - apply get_op_type_wf in g. destruct g. assumption. assumption.
  - assumption.
+ clear sig_subtype_trans vsubtype_trans_rev.
  destruct H3. eapply vsubtype_trans. exact H2.
  - inv wf1. assumption.
  - apply get_op_type_wf in H0. destruct H0. assumption. assumption.
  - apply get_op_type_wf in g. destruct g. assumption. assumption.
  - assumption.
+ assumption.
}{
(* clear csubtype_trans csubtype_trans_rev eqs_subtype_trans eqs_subtype_trans_rev.
clear sig_subtype_trans.
intros wf1 wf2 wf3 S32. destruct S21.
apply sig_subtype_sigempty in S32. subst. apply SigØsubty.
apply sig_remove_op_intro in S32 as S32'. 2: (inv wf2; assumption).
specialize (remove_op_wf Σ3 op wf3) as wfr. inv wf2.
specialize (sig_subtype_trans_rev _ _ _ S21 wf1 H7 wfr S32') as rec.
clear sig_subtype_trans_rev.
destruct (get_op_type Σ3 op) eqn: gets.
- destruct p. eapply sig_remove_op_elim. exact gets.
  inv S32. simpl. *)


}
Qed.



Fixpoint ctx_subtype_get Γ Γ' A num
  (ctx_sty : ctx_subtype Γ Γ') {struct ctx_sty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A A'.
Proof.
revert num. induction ctx_sty.
+ intros num H. simpl in H. discriminate.
+ intros num get.
  destruct num.
  - clear IHctx_sty. simpl in *. injection get. intros. subst. exists A'.
    constructor. reflexivity. assumption.
  - simpl in *. eapply IHctx_sty.  clear IHctx_sty. exact get.
Qed.

Fixpoint ctx_subtype_get_reverse Γ Γ' A num
  (ctx_sty : ctx_subtype Γ' Γ) {struct ctx_sty}:
  get_vtype Γ num = Some A -> 
  exists A', get_vtype Γ' num = Some A' /\ vsubtype A' A.
Proof.
revert num. induction ctx_sty.
+ intros num H. simpl in H. discriminate.
+ intros num get.
  destruct num.
  - clear IHctx_sty. simpl in *. injection get. intros. subst. exists A0.
    constructor. reflexivity. assumption.
  - simpl in *. eapply IHctx_sty.  clear IHctx_sty. exact get.
Qed.


Fixpoint ctx_subtype_vtype Γ Γ' v A:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_vtype Γ v A -> has_vtype Γ' v A
with ctx_subtype_ctype Γ Γ' c C:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_ctype Γ c C -> has_ctype Γ' c C
with ctx_subtype_htype Γ Γ' h Σ D:
  wf_ctx Γ' -> ctx_subtype Γ' Γ -> has_htype Γ h Σ D -> has_htype Γ' h Σ D.
Proof.
Admitted.
(* {
intros wf ctxsty types.
destruct types. induction H1; apply TypeV; try assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply (ctx_subtype_get_reverse _ _ A num) in ctxsty. destruct ctxsty as [A' [gets]]. 
  eapply TypeVSubtype.
  - apply TypeV. assumption. apply ctx_gets_wf in gets as wfA'.
    exact wfA'. assumption. apply TypeVar. assumption.
  - assumption.
  - assumption.
+ apply TypePair.
  - eapply ctx_subtype_vtype. assumption. exact ctxsty. assumption.
  - eapply ctx_subtype_vtype. assumption. exact ctxsty. assumption.
+ apply TypeInl. admit.
+ admit.
+ apply TypeFun. admit.
+ apply TypeHandler; admit.
+ admit.
}{
intros wf ctxsty types.
destruct types. induction H1; apply TypeC; try assumption.
+ admit.
+ eapply TypeΠMatch.  *)


(* ========================== Subtype Shapes ========================== *)

Fixpoint subty_shape_pair A B C :
  vsubtype C (TyΠ A B) -> 
  exists A' B', C = (TyΠ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig.
inv orig. exists A0. exists B0.
constructor. reflexivity. constructor; assumption.
Qed.

Fixpoint subty_shape_sum A B C :
  vsubtype C (TyΣ A B) -> 
  exists A' B', C = (TyΣ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig.
inv orig. exists A0. exists B0.
constructor. reflexivity. constructor; assumption.
Qed.

Fixpoint subty_shape_fun A B C :
  vsubtype C (TyFun A B) -> 
  exists A' B', C = (TyFun A' B') /\ vsubtype A A' /\ csubtype B' B.
Proof.
intro orig.
inv orig. exists A0. exists C0.
constructor. reflexivity. constructor; assumption.
Qed.

Fixpoint subty_shape_handler A B C :
  vsubtype C (TyHandler A B) -> 
  exists A' B', C = (TyHandler A' B') /\ csubtype A A' /\ csubtype B' B.
Proof.
intro orig.
inv orig. exists C0. exists D.
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
+ destruct H.
  - destruct H. destruct H. inv H. assumption.
  - destruct H. destruct H. discriminate.
Qed.

Lemma shape_sum_inr Γ v A B :
  has_vtype Γ (Inr v) (TyΣ A B) -> has_vtype Γ v B.
Proof.
intro orig.
apply (shape_sum_full _ _ A B) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ destruct H.
  - destruct H. destruct H. discriminate.
  - destruct H. destruct H. inv H. assumption.
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
      eapply ctx_subtype_ctype. 3: exact H3.
      apply WfCtxU; assumption.
      apply CtxUsubty. apply ctx_subty_refl. assumption.
Qed.

Lemma shape_fun Γ x c A C :
  has_vtype Γ (Fun x c) (TyFun A C) -> has_ctype (CtxU Γ A) c C.
Proof.
intro orig.
apply (shape_fun_full _ _ A C) in orig as shape. 2: reflexivity.
destruct shape.
+ destruct H as [name [num]]. discriminate.
+ destruct H. destruct H. destruct H. inv H. inv H0. apply TypeC; assumption.
Qed.

(* ========================== Computation Shapes ========================== *)

(* ΠMatch *)
Fixpoint shape_prodmatch_full Γ c v x y c' C
  (orig : has_ctype Γ c C) {struct orig} :
  c = (ΠMatch v (x, y) c') ->
  (exists A B, has_vtype Γ v (TyΠ A B) /\
    has_ctype (CtxU (CtxU Γ A) B) c' C).
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
Fixpoint shape_app_full Γ c x c' v C
  (orig : has_ctype Γ c C) {struct orig} :
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