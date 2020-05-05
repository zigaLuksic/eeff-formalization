(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\skeletons". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\skeletons".
Require Export skeletons subtyping_lemmas.


Lemma skeletons_ignore_vsubtype A A':
  vsubtype A A' -> skeletize_vtype A = skeletize_vtype A'
with skeletons_ignore_csubtype C C':
  csubtype C C' -> skeletize_ctype C = skeletize_ctype C'.
Proof.
all: intros sty; induction sty; simpl; f_equal; auto.
apply skeletons_ignore_csubtype in H. auto.
Qed.


Fixpoint has_vtype_annotates Γ v A (types : has_vtype Γ v A):
  exists v', v_ann Γ v A types v'
with has_ctype_annotates Γ c C (types : has_ctype Γ c C):
  exists c', c_ann Γ c C types c'
with has_htype_annotates Γ h Σ D (types : has_htype Γ h Σ D):
  exists h', h_ann Γ h Σ D types h'.
{
rename has_vtype_annotates into VL.
rename has_ctype_annotates into CL.
rename has_htype_annotates into HL.
destruct types. destruct h.
+ eexists. apply AnnUnit.
+ eexists. apply AnnInt.
+ eexists. apply AnnVar. auto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  specialize (VL _ _ _ h0) as IH2. destruct IH2 as [v2' ann2].
  eexists. eapply AnnPair; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v' ann1].
  eexists. eapply AnnInl; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v' ann1].
  eexists. eapply AnnInr; eauto. 
+ eexists. apply AnnListNil.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  specialize (VL _ _ _ h0) as IH2. destruct IH2 as [v2' ann2].
  eexists. eapply AnnListCons; eauto.
+ specialize (CL _ _ _ h) as IH1. destruct IH1 as [c' ann1].
  eexists. eapply AnnFun; eauto.
+ specialize (CL _ _ _ h0) as IH1. destruct IH1 as [c' ann1].
  specialize (HL _ _ _ _ h1) as IH2. destruct IH2 as [h' ann2].
  eexists. eapply AnnHandler; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  eexists. eapply AnnVSubtype; eauto.
}{
rename has_vtype_annotates into VL.
rename has_ctype_annotates into CL.
rename has_htype_annotates into HL.
destruct types. destruct h.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  eexists. eapply AnnRet; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  eexists. eapply AnnAbsurd; eauto.
+ specialize (VL _ _ _ h) as IH. destruct IH as [v' ann].
  specialize (CL _ _ _ h0) as IH1. destruct IH1 as [c1' ann1].
  eexists. eapply AnnΠMatch; eauto.
+ specialize (VL _ _ _ h) as IH. destruct IH as [v' ann].
  specialize (CL _ _ _ h0) as IH1. destruct IH1 as [c1' ann1].
  specialize (CL _ _ _ h1) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnΣMatch; eauto.
+ specialize (VL _ _ _ h) as IH. destruct IH as [v' ann].
  specialize (CL _ _ _ h0) as IH1. destruct IH1 as [c1' ann1].
  specialize (CL _ _ _ h1) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnListMatch; eauto.
+ specialize (CL _ _ _ h) as IH1. destruct IH1 as [c1' ann1].
  specialize (CL _ _ _ h0) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnDoBind; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  specialize (VL _ _ _ h0) as IH2. destruct IH2 as [v2' ann2].
  eexists. eapply AnnApp; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  specialize (CL _ _ _ h0) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnHandle; eauto.
+ specialize (CL _ _ _ h) as IH1. destruct IH1 as [c1' ann1].
  specialize (CL _ _ _ h0) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnLetRec; eauto.
+ specialize (VL _ _ _ h) as IH1. destruct IH1 as [v1' ann1].
  specialize (CL _ _ _ h0) as IH2. destruct IH2 as [c2' ann2].
  eexists. eapply AnnOp; eauto.
+ specialize (CL _ _ _ h) as IH1. destruct IH1 as [c1' ann1].
  eexists. eapply AnnCSubtype; eauto.
}{
rename has_vtype_annotates into VL.
rename has_ctype_annotates into CL.
rename has_htype_annotates into HL.
destruct types. destruct h0.
+ eexists. eapply AnnCasesØ.
+ specialize (HL _ _ _ _ h0) as IH1. destruct IH1 as [c' ann1].
  specialize (CL _ _ _ h1) as IH2. destruct IH2 as [h' ann2].
  eexists. eapply AnnCasesU; eauto.
}
Qed.


Fixpoint ann_val_types Γ v A (types : has_vtype Γ v A) v'
  (ann: v_ann Γ v A types v') {struct ann}:
  has_sk_vtype 
    (skeletize_ctx Γ) v' (skeletize_vtype A)
with ann_comp_types Γ c C (types : has_ctype Γ c C) c'
  (ann: c_ann Γ c C types c') {struct ann}:
  has_sk_ctype 
    (skeletize_ctx Γ) c' (skeletize_ctype C)
with ann_hcases_types Γ h Σ D (types : has_htype Γ h Σ D) h'
  (ann: h_ann Γ h Σ D types h') {struct ann}:
  has_sk_htype 
    (skeletize_ctx Γ) h' (skeletize_ctype D).
Proof.
{
destruct ann; simpl.
+ apply SkTypeVar.
  assert (forall n γ A, get_vtype γ n = Some A ->
    get_sk_vtype (skeletize_ctx γ) n = Some (skeletize_vtype A)).
  { intros k γ B. revert k. induction γ; intros k gets. discriminate. simpl.
    destruct k. 
    + simpl in gets. inv gets. auto.
    + simpl in *. auto. }
  apply H0. auto.
+ apply SkTypeUnit.
+ apply SkTypeInt.
+ apply SkTypePair; eauto.
+ apply SkTypeInl; eauto.
+ apply SkTypeInr; eauto.
+ apply SkTypeListNil.
+ apply SkTypeListCons; eauto.
  eapply ann_val_types in ann2. simpl in *. auto.
+ apply SkTypeFun.
  eapply ann_comp_types in H. simpl in *. auto.
+ apply SkTypeHandler.
  eapply ann_comp_types in H. simpl in *. auto.
  eapply ann_hcases_types in H0. simpl in *. auto.
+ eapply ann_val_types in ann. simpl in *.
  apply skeletons_ignore_vsubtype in H. inv H. auto.
}{
destruct ann; simpl.
+ apply SkTypeRet. eauto.
+ apply SkTypeAbsurd.
  eapply ann_val_types in H. simpl in *. auto.
+ eapply SkTypeΠMatch.
  eapply ann_val_types in H. simpl in *. eauto.
  eapply ann_comp_types in ann. simpl in *. auto.
+ eapply SkTypeΣMatch.
  eapply ann_val_types in H. simpl in *. eauto.
  eapply ann_comp_types in ann1. simpl in *. auto.
  eapply ann_comp_types in ann2. simpl in *. auto.
+ eapply SkTypeListMatch.
  eapply ann_val_types in H. simpl in *. eauto.
  eapply ann_comp_types in ann1. simpl in *. auto.
  eapply ann_comp_types in ann2. simpl in *. auto.
+ eapply SkTypeDoBind.
  eapply ann_comp_types in ann1. simpl in *. eauto.
  eapply ann_comp_types in ann2. simpl in *. auto.
+ eapply SkTypeApp; eauto.
  eapply ann_val_types in H. simpl in *. auto.
+ eapply SkTypeHandle; eauto.
  eapply ann_val_types in H. simpl in *. auto.
+ eapply SkTypeLetRec.
  eapply ann_comp_types in ann1. simpl in *. eauto.
  eapply ann_comp_types in ann2. simpl in *. auto.
+ eapply SkTypeOp. eauto.
  eapply ann_comp_types in ann. simpl in *. auto.
+ eapply ann_comp_types in ann. simpl in *.
  apply skeletons_ignore_csubtype in H. inv H. auto.
}{
destruct ann; simpl.
+ apply SkTypeCasesØ.
+ eapply SkTypeCasesU. eauto.
  eapply ann_comp_types in H. simpl in *. auto.
}
Qed.


(* Due to subtyping we need manual inversion :( *)

Fixpoint inv_ann_Var Γ n A p v'
  (ann: v_ann Γ (Var n) A p v'):
  v' = SkVar n.
Proof.
inv ann. auto. apply inv_ann_Var in H. auto.
Qed.

Fixpoint inv_ann_Unit Γ A p v'
  (ann: v_ann Γ Unit A p v'):
  v' = SkUnit.
Proof.
inv ann. auto. apply inv_ann_Unit in H. auto.
Qed.

Fixpoint inv_ann_Int Γ n A p v'
  (ann: v_ann Γ (Int n) A p v'):
  v' = SkInt n.
Proof.
inv ann. auto. apply inv_ann_Int in H. auto.
Qed.

Fixpoint inv_ann_Pair Γ v1 v2 A B p v'
  (ann: v_ann Γ (Pair v1 v2) (TyΠ A B) p v') {struct ann}:
  exists v1' v2' A' B' p1 p2,
    vsubtype A' A /\ vsubtype B' B /\
    v_ann Γ v1 A' p1 v1' /\ v_ann Γ v2 B' p2 v2' /\
    v' = SkPair v1' v2'.
Proof.
inv ann.
+ exists v1', v2', A, B, p1, p2. aconstructor. 2: aconstructor.
  all: apply vsubtype_refl; inv p; inv H0; auto.
+ inv H0. eapply inv_ann_Pair in H.
  destruct H as [v1'[v2'[A'[B'[p1[p2[stya[styb othr]]]]]]]].
  exists v1',v2',A',B',p1,p2.
  do 2 try aconstructor.
  all: eapply vsubtype_trans; eauto.
Qed.

Fixpoint inv_ann_Inl Γ v A B p v'
  (ann: v_ann Γ (Inl v) (TyΣ A B) p v') {struct ann}:
  exists v1' A' p1,
    vsubtype A' A /\ v_ann Γ v A' p1 v1' /\ v' = SkInl v1'.
Proof.
inv ann.
+ exists v'0, A, pl. aconstructor.
  apply vsubtype_refl. inv p. inv H0. auto.
+ inv H0. eapply inv_ann_Inl in H.
  destruct H as [v1'[A'[p1[stya othr]]]].
  exists v1',A',p1. aconstructor.
  eapply vsubtype_trans; eauto.
Qed.

Fixpoint inv_ann_Inr Γ v A B p v'
  (ann: v_ann Γ (Inr v) (TyΣ A B) p v') {struct ann}:
  exists v1' B' p1,
    vsubtype B' B /\ v_ann Γ v B' p1 v1' /\ v' = SkInr v1'.
Proof.
inv ann.
+ exists v'0, B, pr. aconstructor.
  apply vsubtype_refl. inv p. inv H0. auto.
+ inv H0. eapply inv_ann_Inr in H.
  destruct H as [v1'[B'[p1[styb othr]]]].
  exists v1',B',p1. aconstructor.
  eapply vsubtype_trans; eauto.
Qed.

Fixpoint inv_ann_ListNil Γ A p v'
  (ann: v_ann Γ ListNil A p v') {struct ann}:
  v' = SkListNil.
Proof.
inv ann. auto.
eapply inv_ann_ListNil in H. auto.
Qed.

Fixpoint inv_ann_ListCons Γ v1 v2 A p v'
  (ann: v_ann Γ (ListCons v1 v2) (TyList A) p v') {struct ann}:
  exists v1' v2' A' p1 p2,
    vsubtype A' A /\
    v_ann Γ v1 A' p1 v1' /\ v_ann Γ v2 (TyList A') p2 v2' /\
    v' = SkListCons v1' v2'.
Proof.
inv ann.
+ exists v1', v2', A, p1, p2. aconstructor.
  all: apply vsubtype_refl; inv p; inv H0; auto.
+ inv H0. eapply inv_ann_ListCons in H.
  destruct H as [v1'[v2'[A'[p1[p2[stya othr]]]]]].
  exists v1',v2',A',p1,p2.
  aconstructor. eapply vsubtype_trans; eauto.
Qed.

Fixpoint inv_ann_Fun Γ c A C p v'
  (ann: v_ann Γ (Fun c) (TyFun A C) p v') {struct ann}:
  exists c' A' C' p1,
    vsubtype A A' /\ csubtype C' C /\
    c_ann (CtxU Γ A') c C' p1 c' /\
    v' = SkFun c'.
Proof.
inv ann.
+ exists c', A, C, pc. do 2 try aconstructor.
  all: apply vsubtype_refl || apply csubtype_refl ; inv p; inv H0; auto.
+ inv H0. eapply inv_ann_Fun in H.
  destruct H as [c'[A'[C'[p1[stya[styc othr]]]]]].
  exists c',A',C',p1.
  do 2 try aconstructor. eapply vsubtype_trans; eauto.
  eapply csubtype_trans; eauto.
Qed.

Fixpoint inv_ann_Handler Γ c h C D p v'
  (ann: v_ann Γ (Handler c h) (TyHandler C D) p v') {struct ann}:
  exists c' h' A' Σ' E' D' pc ph,
    csubtype C (CTy A' Σ' E') /\ csubtype D' D /\
    c_ann (CtxU Γ A') c D' pc c' /\
    h_ann Γ h Σ' D' ph h' /\
    v' = SkHandler c' h'.
Proof.
inv ann.
+ exists c', h', A, Σ, E, D, pc, ph. aconstructor. 2: aconstructor.
  all: apply csubtype_refl ; inv p; inv H0; auto.
+ inv H0. eapply inv_ann_Handler in H. clear inv_ann_Handler.
  destruct H as [c'[h'[A'[Σ'[E'[D'[pc[ph[styc[styd othr]]]]]]]]]].
  exists c',h',A',Σ',E',D',pc,ph.
  do 2 try aconstructor. all: eapply csubtype_trans; eauto.
Qed.



Fixpoint inv_ann_Op Γ id v c C p c'
  (ann: c_ann Γ (Op id v c) C p c') {struct ann}:
  exists vop' cop' Aop' Bop' A' Σ' E' p1 p2,
    csubtype (CTy A' Σ' E') C /\
    get_op_type Σ' id = Some (Aop', Bop') /\
    v_ann Γ v Aop' p1 vop' /\ c_ann (CtxU Γ Bop') c (CTy A' Σ' E') p2 cop' /\
    c' = SkOp id (skeletize_vtype Aop') (skeletize_vtype Bop') vop' cop'.
Proof.
inv ann.
+ exists v', c'0, Aop, Bop, A, Σ, E, pv, pc. do 2 try aconstructor.
  all: apply vsubtype_refl || apply sig_subtype_refl || eapply eqs_subtype_refl.
  all: inv p; inv H0; eauto.
+ destruct C as [a σ e]. inv H0.
  eapply shape_op_full in p' as shape. 2: reflexivity. 2: reflexivity.
  destruct shape as [Aop'[Bop'[gets' _]]]. 
  eapply inv_ann_Op in H. clear inv_ann_Op.
  destruct H as [vop'[cop'[Aop''[Bop''[A''[Σ''[E'' othr]]]]]]].
  destruct othr as [p1[p2[styc[gets''[ann1[ann2 s']]]]]].
  subst. inv styc.
  exists vop', cop', Aop'', Bop'', A'', Σ'', E'', p1, p2.
  do 2 try aconstructor.
  - eapply vsubtype_trans; eauto.
  - eapply sig_subtype_trans; eauto.
  - eapply eqs_subtype_trans; eauto.
Qed.


(* TODO:

  show that here is preciseliy one Σ for which h types *)

(* Show uniqueness *)
(* We are lucky because there are no restrictions on the context! <3 *)

Fixpoint v_ann_unique Γ1 Γ2 v A A1 A2 v1 v2
  (tys1: has_vtype Γ1 v A1) (tys2: has_vtype Γ2 v A2)
  (ann1: v_ann Γ1 v A1 tys1 v1) (ann2: v_ann Γ2 v A2 tys2 v2) {struct ann1}:
  vsubtype A1 A -> vsubtype A2 A ->
  v1 = v2

with c_ann_unique Γ1 Γ2 c C C1 C2 c1 c2
  (tys1: has_ctype Γ1 c C1) (tys2: has_ctype Γ2 c C2)
  (ann1: c_ann Γ1 c C1 tys1 c1) (ann2: c_ann Γ2 c C2 tys2 c2) {struct ann1}:
  csubtype C1 C -> csubtype C2 C ->
  c1 = c2

with h_ann_unique Γ Γ1 Γ2 h Σ Σ1 Σ2 D D1 D2 h1 h2
  (tys1: has_htype Γ1 h Σ1 D1) (tys2: has_htype Γ2 h Σ2 D2)
  (ann1: h_ann Γ1 h Σ1 D1 tys1 h1) (ann2: h_ann Γ2 h Σ2 D2 tys2 h2) {struct ann1}:
  has_htype Γ h Σ D ->
  sig_subtype Σ Σ1 -> sig_subtype Σ Σ2 ->
  csubtype D1 D -> csubtype D2 D ->
  h1 = h2.

Proof.
all: rename v_ann_unique into VL.
all: rename c_ann_unique into CL.
all: rename h_ann_unique into HL.
{
intros sty1 sty2. destruct ann1.
Focus 11. (* Subtyping on left *)
  eapply VL. eauto. eauto. 2: eauto.
  eapply vsubtype_trans. all: eauto.

+ eapply inv_ann_Var in ann2; eauto.
+ apply inv_ann_Unit in ann2; auto.
+ eapply inv_ann_Int in ann2; eauto.
+ eapply shape_pair_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s[t1 t2]]]]. subst.
  apply inv_ann_Pair in ann2.
  destruct ann2 as [v1''[v2''[A''[B''[p1''[p2'' othr]]]]]].
  destruct othr as [stya[styb[ann2_1[ann2_2 id]]]].
  subst. f_equal. 
  - inv sty1. inv sty2. eapply VL; eauto.
    eapply vsubtype_trans; eauto.
  - inv sty1. inv sty2. eapply VL; eauto. 
    eapply vsubtype_trans; eauto.
+ eapply shape_inl_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s t]]]. subst.
  apply inv_ann_Inl in ann2.
  destruct ann2 as [v''[A''[p''[stya[ann2 id]]]]].
  subst. f_equal.
  inv sty1. eapply VL; eauto. inv sty2.
  eapply vsubtype_trans; eauto.
+ eapply shape_inr_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s t]]]. subst.
  apply inv_ann_Inr in ann2.
  destruct ann2 as [v''[B''[p''[styb[ann2 id]]]]].
  subst. f_equal.
  inv sty1. eapply VL; eauto. inv sty2.
  eapply vsubtype_trans; eauto.
+ eapply inv_ann_ListNil in ann2. auto.
+ eapply shape_list_cons_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[s[t1 t2]]]. subst.
  apply inv_ann_ListCons in ann2.
  destruct ann2 as [v1''[v2''[A''[p1''[p2''[stya[t1'[t2' id]]]]]]]].
  subst. f_equal.
  - inv sty1. inv sty2. eapply VL; eauto.
    eapply vsubtype_trans; eauto.
  - inv sty1. inv sty2. eapply VL; eauto.
    all: apply SubtypeTyList. eauto. eapply vsubtype_trans; eauto.
+ eapply shape_fun_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[C'[s t]]]. subst.
  apply inv_ann_Fun in ann2.
  destruct ann2 as [c''[A''[C''[p''[stya[styc[ann2 id]]]]]]].
  subst. f_equal.
  inv sty1. inv sty2. eapply CL; eauto.
  eapply csubtype_trans; eauto.
+ eapply shape_handler_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[Σ'[E'[D'[Σ''[D''[s[ct[ht[r[ssty csty]]]]]]]]]]]. subst.
  apply inv_ann_Handler in ann2.
  destruct ann2 as [c''[h''[A'''[Σ'''[E'''[D'''[pc'[ph' othr]]]]]]]].
  destruct othr as [csty'[dsty'[cann[hann s]]]].
  subst. f_equal.
  - inv sty1. inv sty2. inv H3. inv H6. eapply CL; eauto.
    eapply csubtype_trans; eauto.
  - inv sty1. inv sty2. inv H3. inv H6. eapply HL. eauto. eauto.
    instantiate (2:=Σ0). 2: eauto.
    3: eapply sig_subtype_trans; eauto.
  exact ph.
    inv csty'. eapply sig_subtype_trans; eauto. eapply csubtype_trans; eauto.
}{
intros sty1 sty2. clear HL. destruct ann1.
Focus 11. (* Subtyping on left *)
  eapply CL. eauto. eauto. 2: eauto.
  eapply csubtype_trans. all: eauto.

+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ destruct C2 as [A2 Σ2 E2].
  eapply shape_op_full in tys2 as shape; try reflexivity.
  destruct shape as [Aop'[Bop'[gets'[vty' cty']]]].
  eapply inv_ann_Op in ann2.
  destruct ann2 as [vop'[cop'[Aop''[Bop''[A''[Σ''[E'' othr]]]]]]].
  destruct othr as [p1[p2[styc[gets''[vann2[cann2 s]]]]]].
  inv sty1. inv sty2.
  assert (sig_subtype Σ'' Σ') as stytrans.
  { inv styc. eapply sig_subtype_trans; eauto. }
  eapply sig_subtype_get_Some in stytrans as styop. 2: eauto.
  destruct styop as [a[b[sget1[sa sb]]]].
  eapply sig_subtype_get_Some in H6 as styop. 2: eauto.
  destruct styop as [a'[b'[sget2[sa' sb']]]].
  rewrite sget2 in sget1. inv sget1. clear sget2.
  subst. f_equal.
  - clear VL CL.
    apply skeletons_ignore_vsubtype in sa. rewrite sa. clear sa.
    apply skeletons_ignore_vsubtype. auto.
  - clear VL CL.
    apply skeletons_ignore_vsubtype in sb. rewrite <-sb. clear sb.
    symmetry. apply skeletons_ignore_vsubtype. auto.
  - eapply VL; eauto.
  - eapply CL. eauto. eauto.
    eapply SubtypeCTy; eauto.
    eapply csubtype_trans; eauto. eapply SubtypeCTy; eauto.
}{
intros htys sty1 sty2 csty1 csty2. clear VL. destruct ann1.
inv ann2. auto.
inv ann2. f_equal.
+ clear CL. inv htys. inv H3. eapply HL; eauto; clear HL.
  - eapply sig_subtype_reduce_both; eauto. inv H1. auto.
  - eapply sig_subtype_reduce_both; eauto. inv H1. auto.
+ clear CL HL. inv htys. inv H3.
  assert (get_op_type (SigU Σ2 op Aop Bop) op = Some (Aop, Bop)) as gets.
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply sig_subtype_get_Some in sty1; eauto.
  eapply sig_subtype_get_Some in sty2; eauto.
  destruct sty1 as [A1[B1[gets1[sty1 _]]]].
  destruct sty2 as [A2[B2[gets2[sty2 _]]]].
  simpl in *. destruct (op==op). 2: destruct n; auto.
  inv gets. inv gets1. inv gets2.
  apply skeletons_ignore_vsubtype in sty1.
  apply skeletons_ignore_vsubtype in sty2.
  rewrite <-sty1. auto.
+ clear CL HL. inv htys. inv H3.
  assert (get_op_type (SigU Σ2 op Aop Bop) op = Some (Aop, Bop)) as gets.
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply sig_subtype_get_Some in sty1; eauto.
  eapply sig_subtype_get_Some in sty2; eauto.
  destruct sty1 as [A1[B1[gets1[_ sty1]]]].
  destruct sty2 as [A2[B2[gets2[_ sty2]]]].
  simpl in *. destruct (op==op). 2: destruct n; auto.
  inv gets. inv gets1. inv gets2.
  apply skeletons_ignore_vsubtype in sty1.
  apply skeletons_ignore_vsubtype in sty2.
  rewrite sty1. auto.
+ clear HL. inv htys. inv H3. eapply CL; eauto.
}













(* Show uniqueness *)

Fixpoint v_ann_unique Γ Γ1 Γ2 v A A1 A2 v1 v2
  (tys1: has_vtype Γ1 v A1) (tys2: has_vtype Γ2 v A2)
  (ann1: v_ann Γ1 v A1 tys1 v1) (ann2: v_ann Γ2 v A2 tys2 v2) {struct ann1}:
  vsubtype A1 A -> vsubtype A2 A ->
  ctx_subtype Γ Γ1 -> ctx_subtype Γ Γ2 ->
  v1 = v2
with c_ann_unique Γ Γ1 Γ2 c C C1 C2 c1 c2
  (tys1: has_ctype Γ1 c C1) (tys2: has_ctype Γ2 c C2)
  (ann1: c_ann Γ1 c C1 tys1 c1) (ann2: c_ann Γ2 c C2 tys2 c2) {struct ann1}:
  csubtype C1 C -> csubtype C2 C ->
  ctx_subtype Γ Γ1 -> ctx_subtype Γ Γ2 ->
  c1 = c2
with h_ann_unique Γ Γ1 Γ2 h Σ Σ1 Σ2 D D1 D2 h1 h2
  (tys1: has_htype Γ1 h Σ1 D1) (tys2: has_htype Γ2 h Σ2 D2)
  (ann1: h_ann Γ1 h Σ1 D1 tys1 h1) (ann2: h_ann Γ2 h Σ2 D2 tys2 h2) {struct ann1}:
  has_htype Γ h Σ D ->
  sig_subtype Σ Σ1 -> sig_subtype Σ Σ2 ->
  csubtype D1 D -> csubtype D2 D ->
  ctx_subtype Γ Γ1 -> ctx_subtype Γ Γ2 ->
  h1 = h2.
Proof.
all: rename v_ann_unique into VL.
all: rename c_ann_unique into CL.
all: rename h_ann_unique into HL.
{
intros sty1 sty2 sctx1 sctx2. destruct ann1.
Focus 11. (* Subtyping on left *)
  eapply VL. eauto. eauto. 2: eauto.
  eapply vsubtype_trans. all: eauto.

+ eapply inv_ann_Var in ann2; eauto.
+ apply inv_ann_Unit in ann2; auto.
+ eapply inv_ann_Int in ann2; eauto.
+ eapply shape_pair_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s[t1 t2]]]]. subst.
  apply inv_ann_Pair in ann2.
  destruct ann2 as [v1''[v2''[A''[B''[p1''[p2'' othr]]]]]].
  destruct othr as [stya[styb[ann2_1[ann2_2 id]]]].
  subst. f_equal. 
  - inv sty1. inv sty2. eapply VL; eauto.
    eapply vsubtype_trans; eauto.
  - inv sty1. inv sty2. eapply VL; eauto. 
    eapply vsubtype_trans; eauto.
+ eapply shape_inl_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s t]]]. subst.
  apply inv_ann_Inl in ann2.
  destruct ann2 as [v''[A''[p''[stya[ann2 id]]]]].
  subst. f_equal.
  inv sty1. eapply VL; eauto. inv sty2.
  eapply vsubtype_trans; eauto.
+ eapply shape_inr_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[B'[s t]]]. subst.
  apply inv_ann_Inr in ann2.
  destruct ann2 as [v''[B''[p''[styb[ann2 id]]]]].
  subst. f_equal.
  inv sty1. eapply VL; eauto. inv sty2.
  eapply vsubtype_trans; eauto.
+ eapply inv_ann_ListNil in ann2. auto.
+ eapply shape_list_cons_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[s[t1 t2]]]. subst.
  apply inv_ann_ListCons in ann2.
  destruct ann2 as [v1''[v2''[A''[p1''[p2''[stya[t1'[t2' id]]]]]]]].
  subst. f_equal.
  - inv sty1. inv sty2. eapply VL; eauto.
    eapply vsubtype_trans; eauto.
  - inv sty1. inv sty2. eapply VL; eauto.
    all: apply SubtypeTyList. eauto. eapply vsubtype_trans; eauto.
+ eapply shape_fun_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[C'[s t]]]. subst.
  apply inv_ann_Fun in ann2.
  destruct ann2 as [c''[A''[C''[p''[stya[styc[ann2 id]]]]]]].
  subst. f_equal.
  inv sty1. inv sty2. eapply CL; eauto.
  - eapply csubtype_trans; eauto.
  - eapply SubtypeCtxU; eauto.
  - apply SubtypeCtxU. auto. eapply vsubtype_trans; eauto.
+ eapply shape_handler_full in tys2 as shape. 2: reflexivity.
  destruct shape as [A'[Σ'[E'[D'[Σ''[D''[s[ct[ht[r[ssty csty]]]]]]]]]]]. subst.
  apply inv_ann_Handler in ann2.
  destruct ann2 as [c''[h''[A'''[Σ'''[E'''[D'''[pc'[ph' othr]]]]]]]].
  destruct othr as [csty'[dsty'[cann[hann s]]]].
  subst. f_equal.
  - inv sty1. inv sty2. inv H3. inv H6. eapply CL; eauto.
    * eapply csubtype_trans; eauto.
    * eapply SubtypeCtxU; eauto.
    * apply SubtypeCtxU. auto. inv csty'. eapply vsubtype_trans; eauto.
  - admit.
    (* inv sty1. inv sty2. inv H3. inv H6. eapply HL; eauto. *)
    (* inv csty'. eapply sig_subtype_trans; eauto. eapply csubtype_trans; eauto. *)
}{
intros sty1 sty2 sctx1 sctx2. clear HL. destruct ann1.
Focus 11. (* Subtyping on left *)
  eapply CL. eauto. eauto. 2: eauto.
  eapply csubtype_trans. all: eauto.

+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ destruct C2 as [A2 Σ2 E2].
  eapply shape_op_full in tys2 as shape; try reflexivity.
  destruct shape as [Aop'[Bop'[gets'[vty' cty']]]].
  eapply inv_ann_Op in ann2.
  destruct ann2 as [vop'[cop'[Aop''[Bop''[A''[Σ''[E'' othr]]]]]]].
  destruct othr as [p1[p2[styc[gets''[vann2[cann2 s]]]]]].
  inv sty1. inv sty2.
  assert (sig_subtype Σ'' Σ') as stytrans.
  { inv styc. eapply sig_subtype_trans; eauto. }
  eapply sig_subtype_get_Some in stytrans as styop. 2: eauto.
  destruct styop as [a[b[sget1[sa sb]]]].
  eapply sig_subtype_get_Some in H6 as styop. 2: eauto.
  destruct styop as [a'[b'[sget2[sa' sb']]]].
  rewrite sget2 in sget1. inv sget1. clear sget2.
  subst. f_equal.
  - clear VL CL.
    apply skeletons_ignore_vsubtype in sa. rewrite sa. clear sa.
    apply skeletons_ignore_vsubtype. auto.
  - clear VL CL.
    apply skeletons_ignore_vsubtype in sb. rewrite <-sb. clear sb.
    symmetry. apply skeletons_ignore_vsubtype. auto.
  - eapply VL; eauto.
  - eapply CL. eauto. eauto.
    eapply SubtypeCTy; eauto.
    eapply csubtype_trans; eauto. eapply SubtypeCTy; eauto.
    all: eapply SubtypeCtxU; eauto.
}{
intros htys sty1 sty2 csty1 csty2 sctx1 sctx2. clear VL. destruct ann1.
inv ann2. auto.
inv ann2. f_equal.
+ clear CL. inv htys. inv H3. eapply HL; eauto; clear HL.
  - eapply sig_subtype_reduce_both; eauto. inv H1. auto.
  - eapply sig_subtype_reduce_both; eauto. inv H1. auto.
+ clear CL HL. inv htys. inv H3.
  assert (get_op_type (SigU Σ2 op Aop Bop) op = Some (Aop, Bop)) as gets.
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply sig_subtype_get_Some in sty1; eauto.
  eapply sig_subtype_get_Some in sty2; eauto.
  destruct sty1 as [A1[B1[gets1[sty1 _]]]].
  destruct sty2 as [A2[B2[gets2[sty2 _]]]].
  simpl in *. destruct (op==op). 2: destruct n; auto.
  inv gets. inv gets1. inv gets2.
  apply skeletons_ignore_vsubtype in sty1.
  apply skeletons_ignore_vsubtype in sty2.
  rewrite <-sty1. auto.
+ clear CL HL. inv htys. inv H3.
  assert (get_op_type (SigU Σ2 op Aop Bop) op = Some (Aop, Bop)) as gets.
  { simpl. destruct (op==op). auto. destruct n. auto. }
  eapply sig_subtype_get_Some in sty1; eauto.
  eapply sig_subtype_get_Some in sty2; eauto.
  destruct sty1 as [A1[B1[gets1[_ sty1]]]].
  destruct sty2 as [A2[B2[gets2[_ sty2]]]].
  simpl in *. destruct (op==op). 2: destruct n; auto.
  inv gets. inv gets1. inv gets2.
  apply skeletons_ignore_vsubtype in sty1.
  apply skeletons_ignore_vsubtype in sty2.
  rewrite sty1. auto.
+ clear HL. inv htys. inv H3. eapply CL; eauto; clear CL.
  instantiate (1:=(CtxU (CtxU Γ Aop) (TyFun Bop D))).
  - assert (get_op_type (SigU Σ2 op Aop Bop) op = Some (Aop, Bop)) as gets.
    { simpl. destruct (op==op). auto. destruct n. auto. }
    eapply sig_subtype_get_Some in sty1; eauto.
    destruct sty1 as [A1[B1[gets1[stya styb]]]].
    simpl in *. destruct (op==op). 2: destruct n; auto.
    inv gets. inv gets1.
    do 2 try apply SubtypeCtxU; auto.
    apply SubtypeTyFun;

}