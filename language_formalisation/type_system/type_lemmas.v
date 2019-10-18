Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\operational_semantics".
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\operational_semantics". *)
Require Export syntax declarational substitution
  subs_lemmas type_aux_lemmas operational_semantics.


Ltac inv H := inversion H; clear H; subst.

Fixpoint v_sub_out_typesafe
  (Γ:ctx) (v:val) (A:vtype) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype (CtxU Γ A_s) v A -> has_vtype Γ v_s A_s ->
  has_vtype Γ (v_sub_out v v_s) A
with c_sub_out_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype (CtxU Γ A_s) c C -> has_vtype Γ v_s A_s ->
  has_ctype Γ (c_sub_out c v_s) C
with h_sub_out_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (v_s:val) (A_s:vtype) {struct h}:
  has_htype (CtxU Γ A_s) h Σ D -> has_vtype Γ v_s A_s ->
  has_htype Γ (h_sub_out h v_s) Σ D.
Proof.
{
intros orig sub. unfold v_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply v_negshift_typesafe.
eapply v_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption. inv sub. assumption.
apply v_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold c_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply c_negshift_typesafe.
eapply c_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption. inv sub. assumption.
apply c_no_var_sub. apply v_shift_makes_no_var.
}{
intros orig sub. unfold h_sub_out.
assert (Γ = ctx_remove_var (CtxU Γ A_s) 0) by auto.
rewrite H. apply h_negshift_typesafe.
eapply h_subs_typesafe. assumption. simpl. reflexivity.
apply v_shift_typesafe. assumption. inv sub. assumption.
apply h_no_var_sub. apply v_shift_makes_no_var.
}
Qed.

Lemma preservation Γ c c' C:
  has_ctype Γ c C -> step c c' -> has_ctype Γ c' C.
Proof.
intros orig step. revert C orig. 
induction step; intros C orig; inv orig; inv H1.
+ unfold c_sub2_out.
  eapply c_sub_out_typesafe.
  eapply c_sub_out_typesafe. exact H9.
  apply v_shift_typesafe.
  - inv H8. inv H3. assumption. 
    
+ inv H9. inv H3.
  eapply c_sub_out_typesafe. exact H10. assumption.
+ inv H9. inv H3.
  eapply c_sub_out_typesafe. exact H11. assumption.
+ inv H5. inv H3.
  eapply c_sub_out_typesafe. exact H6. assumption.
+ eapply c_sub_out_typesafe. exact H9.
  apply TypeV. assumption. inv H9. inv H1. assumption. 
  apply TypeFun. apply TypeC.
  - inv H8. inv H1. assumption.
  - inv H8. assumption.
  - eapply TypeLetRec. 2: exact H8.
    assert (CtxU (CtxU (CtxU Γ A) A) (TyFun A C0) 
      = ctx_insert_var (CtxU (CtxU Γ A) (TyFun A C0)) A 2)
    as insertion.
    { simpl. destruct Γ; auto. }
    rewrite insertion.
    apply c_insert_typesafe. assumption.
    inv H8. inv H1. inv H6. assumption.
+ apply TypeC. assumption. assumption.
  eapply TypeDoBind. 2: exact H8. auto.
+ eapply c_sub_out_typesafe. exact H8. inv H7. inv H3. assumption.
+ inv H7. inv H3. apply TypeC. assumption. assumption.
  eapply TypeOp. exact H9. assumption.
  apply TypeC. inv H15. assumption. assumption.
  eapply TypeDoBind. exact H15. 
  assert (CtxU (CtxU Γ B_op) A = ctx_insert_var (CtxU Γ A) B_op 1).
  { simpl. destruct Γ; auto. }
  rewrite H3. apply c_insert_typesafe. assumption.
  inv H15. inv H4. assumption.
+ apply TypeC. assumption. assumption.
  eapply TypeHandle. exact H5. apply IHstep. assumption.
+ inv H5. inv H3. eapply c_sub_out_typesafe. 
  - exact H8.
  - inv H7. inv H5. assumption.
+ unfold c_sub2_out. inv H2. inv H10. inv H6.
  eapply c_sub_out_typesafe.
  instantiate (1 := TyFun B_op (CTy A Σ E)).
  - assert (forall h C Σ,
      find_op_case h op_id = Some (x_op, k_op, c_op) ->
      get_op_type Σ op_id = Some (A_op, B_op) ->
      has_htype Γ h Σ C ->
      has_ctype (CtxU Γ (TyFun B_op C))
        (c_sub_out c_op (Sub.v_shift v_arg 1 0)) C).
    -- intros h' C. induction h'; intros Σ' finds gets types.
      * simpl in finds. discriminate.
      * simpl in finds. inv types. inv H10. simpl in gets.
        destruct (op_id==o).
        ++ injection finds. injection gets. intros. subst. 
          eapply c_sub_out_typesafe. exact H24.
          apply v_shift_typesafe. assumption.
          inv H24. inv H10. inv H18. assumption.
        ++ eapply IHh'. assumption. exact gets. assumption.
    -- eapply H6. exact H. exact H14. inv H8. inv H10. assumption.
  - apply TypeV. assumption. 
    * apply WfFun. inv H16. inv H6. assumption. apply WfCty; assumption.
    * apply TypeFun. apply TypeC.
      { inv H16. assumption. }
      { apply WfCty; assumption. }
      inv H8. eapply TypeHandle.
      apply v_shift_typesafe.
      { apply TypeV. assumption. exact H7. assumption. }
      { inv H16. inv H8. assumption. }
      assumption.
Qed.

Lemma progress c C:
  has_ctype CtxØ c C ->
  (exists v, c = Ret v) \/ (exists o v y c', c = Op o v y c') \/
  (exists c', step c c'). 
Proof.
revert C. induction c; intros C orig.
+ left. exists v. reflexivity.
+ right. right. inv orig. inv H1. inv H7. inv H3.
  - simpl in H1. discriminate.
  - eexists. apply Step_ΠMatch.
+ right. right. rename v0 into x. rename v1 into y.
  inv orig. inv H1. inv H9; inv H3.
  - simpl in H1. discriminate.
  - eexists. apply Step_ΣMatch_Inl.
  - eexists. apply Step_ΣMatch_Inr.
+ right. right. inv orig. inv H1. inv H5; inv H3.
  - simpl in H1. discriminate.
  - eexists. apply Step_App.
+ right. left. exists o. exists v. exists v0. exists c. reflexivity.
+ right. right. rename v into f. rename v0 into x.
  eexists. apply Step_LetRec.
+ right. right. rename v into x. inv orig. inv H1.
  apply IHc1 in H7. destruct H7 as [h1 | [h2 | h3]].
  - destruct h1. rewrite H1 in *. eexists. apply Step_DoBind_Ret.
  - destruct h2. destruct H1. destruct H1. destruct H1. rewrite H1 in *.
    eexists. apply Step_DoBind_Op.
  - destruct h3. eexists. apply Step_DoBind_step. exact H1.
+ right. right. inv orig. inv H1. inv H5. inv H3. { simpl in H4. discriminate. }
  apply IHc in H7 as IH. destruct IH as [h1 | [h2 | h3]].
  - destruct h1. rewrite H3 in *. eexists. apply Step_Handle_Ret.
  - destruct h2. destruct H3. destruct H3. destruct H3. rewrite H3 in *.
    rename x0 into o. rename x1 into v_arg. rename x2 into y. rename x3 into k. 
    inv H7. inv H6. 
    specialize (h_has_case CtxØ h Σ C o A_op B_op H10 H12) as gets.
    destruct gets. destruct H3. destruct H3.
    eexists. eapply Step_Handle_Op. exact H3.
  - destruct h3 as [c' h3].
    eexists. eapply Step_Handle_Step. exact h3.
Qed.
