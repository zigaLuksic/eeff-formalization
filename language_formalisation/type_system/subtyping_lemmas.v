(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".

Require Import syntax declarational.

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