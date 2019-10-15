(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\substitution". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\substitution".

Require Export syntax syntax_lemmas declarational substitution Omega Logic.
Require Export subs_lemmas wellfounded_lemmas.

Ltac inv H := inversion H; clear H; subst.


Lemma extend_get_proof Γ A i Ai:
  get_vtype Γ i = Some Ai-> get_vtype (CtxU Γ A) (i + 1) = Some Ai.
Proof.
assert (i + 1 = S i) by omega.
induction Γ; rewrite H; auto.
Defined.


Fixpoint v_insert_typesafe Γ v A A_ins i {struct v} :
  has_vtype Γ v A -> wf_vtype A_ins ->
  has_vtype (ctx_insert_var Γ A_ins i) (Sub.v_shift v 1 i) A
with c_insert_typesafe Γ c C A_ins i {struct c} :
  has_ctype Γ c C -> wf_vtype A_ins ->
  has_ctype (ctx_insert_var Γ A_ins i) (Sub.c_shift c 1 i) C
with h_insert_typesafe Γ h Σ D A_ins i {struct h} :
  has_htype Γ h Σ D -> wf_vtype A_ins ->
  has_htype (ctx_insert_var Γ A_ins i) (Sub.h_shift h 1 i) Σ D.
Proof.
{
clear v_insert_typesafe.
revert A i. induction v; intros A i orig wf_Ains; simpl; 
inv orig; inv H1; apply TypeV; try (assumption || apply ctx_insert_wf; assumption).
+ simpl. assert (
    (if i <=? num then (name, num + 1) else (name, num))
      = (name, if i <=? num then num + 1 else num) ) 
  as same by (destruct (i<=?num); reflexivity).
  rewrite same. apply TypeVar. simpl. 
  simpl. destruct (i<=?num) eqn:cmp.
  - erewrite <-get_ctx_insert_changed.
    * assumption.
    * apply leb_complete in cmp. omega.
  - erewrite <-get_ctx_insert_unchanged.
    * assumption.
    * apply leb_iff_conv in cmp. omega.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv; assumption.
+ apply TypeInr. apply IHv; assumption.
+ apply TypePair; try apply IHv1 || apply IHv2; assumption.
+ apply TypeFun. rewrite ctx_insert_extend. auto.
+ apply TypeHandler; auto. rewrite ctx_insert_extend. auto.
}{
clear c_insert_typesafe.
revert Γ C i. induction c; intros Γ C i orig wfAins; simpl;
inv orig; inv H1; apply TypeC; try (assumption || apply ctx_insert_wf; assumption).
+ apply TypeRet. apply v_insert_typesafe; assumption.
+ eapply TypeΠMatch.
  - eapply v_insert_typesafe. exact H7. assumption.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. auto.
+ eapply TypeΣMatch.
  - apply v_insert_typesafe. exact H9. assumption.
  - rewrite ctx_insert_extend. auto.
  - rewrite ctx_insert_extend. auto.
+ eapply TypeApp.
  - apply v_insert_typesafe. exact H5. assumption.
  - auto.
+ eapply TypeOp. exact H8. auto.
  rewrite ctx_insert_extend. auto.
+ eapply TypeLetRec.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. apply IHc1. exact H8. assumption.
  - rewrite ctx_insert_extend. auto.
+ eapply TypeDoBind.
  - apply IHc1. exact H7. assumption.
  - rewrite ctx_insert_extend. auto.
+ eapply TypeHandle.
  - apply v_insert_typesafe. exact H5. assumption.
  - auto.
}{
clear h_insert_typesafe.
revert Γ Σ D i. induction h; intros Γ Σ D i orig wf_Ains; simpl; 
inv orig; inv H0; inv H1; apply TypeH; try (apply ctx_insert_wf; assumption); 
try apply WfSigØ || apply WfCty || apply WfSigU; try assumption.
+ apply TypeCasesØ.
+ inv H2.
+ inv H2.
+ inv H2. apply TypeCasesU; auto.
  - assert (forall h,
      find_op_case h op = None ->
      find_op_case (Sub.h_shift h 1 i) op = None).
    * intros h' orig. induction h'; auto.
      simpl in *. destruct (op==o). discriminate. auto.
    * apply H1. assumption.
  - rewrite ctx_insert_extend. rewrite ctx_insert_extend.
    assert (i+1+1=i+2) by omega. rewrite H1. auto.
}
Defined.

Fixpoint v_shift_typesafe
  (Γ:ctx) (A0:vtype) v A {struct v} :
  has_vtype Γ v A -> wf_vtype A0 ->
  has_vtype (CtxU Γ A0) (Sub.v_shift v 1 0) A

with c_shift_typesafe
  (Γ:ctx) (A0:vtype) c C {struct c} :
  has_ctype Γ c C -> wf_vtype A0 ->
  has_ctype (CtxU Γ A0) (Sub.c_shift c 1 0) C

with h_shift_typesafe
  (Γ:ctx) (A0:vtype) h Σ D {struct h} :
  has_htype Γ h Σ D -> wf_vtype A0 ->
  has_htype (CtxU Γ A0) (Sub.h_shift h 1 0) Σ D.
Proof.
all: intro orig;
assert (ctx_insert_var Γ A0 0 = CtxU Γ A0) by (destruct Γ; auto);
rewrite <-H; inv orig.
apply v_insert_typesafe. apply TypeV; assumption.
apply c_insert_typesafe. apply TypeC; assumption.
apply h_insert_typesafe. apply TypeH; assumption.
Defined.


Fixpoint v_negshift_typesafe
  (Γ:ctx) v A i {struct v} :
  has_vtype Γ v A ->
  v_no_var_j v i ->
  has_vtype (ctx_remove_var Γ i) (Sub.v_negshift v 1 i) A

with c_negshift_typesafe
  (Γ:ctx) c C i {struct c} :
  has_ctype Γ c C ->
  c_no_var_j c i ->
  has_ctype (ctx_remove_var Γ i) (Sub.c_negshift c 1 i) C

with h_negshift_typesafe
  (Γ:ctx) h Σ D i {struct h} :
  has_htype Γ h Σ D ->
  h_no_var_j h i ->
  has_htype (ctx_remove_var Γ i) (Sub.h_negshift h 1 i) Σ D.
Proof.
{
clear v_negshift_typesafe.
revert Γ A i. induction v; intros Γ A i orig no_var; simpl; 
inv orig; inv H1; apply TypeV; simpl in no_var; 
try (apply ctx_remove_wf; assumption); try assumption.
+ simpl. assert (
    (if i <=? num then (name, num - 1) else (name, num))
      = (name, if i <=? num then num - 1 else num) ) 
  as same by (destruct (i<=?num); reflexivity).
  rewrite same. apply TypeVar. destruct (i<=?num) eqn:cmp.
  - erewrite <-get_ctx_remove_changed; apply leb_complete in cmp.
    * destruct num. destruct no_var. omega.
      simpl. assert (num-0=num) by omega. rewrite H1. assumption.
    * omega.
  - erewrite <-get_ctx_remove_unchanged. assumption.
    apply leb_iff_conv in cmp. omega.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. eapply IHv. exact H4. assumption.
+ apply TypeInr. eapply IHv. exact H4. assumption.
+ apply TypePair; destruct no_var.
  - eapply IHv1. exact H5. assumption.
  - eapply IHv2. exact H7. assumption.
+ apply TypeFun. rewrite ctx_remove_extend.
  apply c_negshift_typesafe; assumption.
+ apply TypeHandler; destruct no_var.
  - rewrite ctx_remove_extend. apply c_negshift_typesafe; assumption.
  - apply h_negshift_typesafe; assumption.
}{
clear c_negshift_typesafe.
revert Γ C i. induction c; intros Γ C i orig no_var; inv orig; inv H1; inv H0;
simpl in no_var; try destruct no_var; apply TypeC; simpl; 
try (apply ctx_remove_wf; assumption); try (apply WfCty; assumption).
+ apply TypeRet. apply v_negshift_typesafe; assumption.
+ eapply TypeΠMatch.
  - apply v_negshift_typesafe. exact H7. assumption.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H5. apply IHc; assumption.
+ eapply TypeΣMatch; destruct H4.
  - apply v_negshift_typesafe. exact H9. assumption.
  - rewrite ctx_remove_extend. apply IHc1; assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ eapply TypeApp; apply v_negshift_typesafe.
  exact H5. all: assumption.
+ eapply TypeOp. exact H8.
  - apply v_negshift_typesafe; assumption.
  - rewrite ctx_remove_extend. apply IHc; assumption.
+ eapply TypeLetRec.
  - rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H5. apply IHc1. exact H8. assumption.
  - rewrite ctx_remove_extend. apply IHc2; assumption.
+ eapply TypeDoBind.
  - apply IHc1. exact H7. assumption.
  - rewrite ctx_remove_extend. auto.
+ eapply TypeHandle.
  - apply v_negshift_typesafe. exact H5. assumption.
  - apply IHc; assumption.
}{
clear h_negshift_typesafe.
revert Γ Σ i. induction h; intros Γ Σ i orig no_var; inv orig; inv H0; inv H2;
inv H1; apply TypeH; auto; simpl in no_var; try destruct no_var;
try (apply ctx_remove_wf; assumption); try (apply WfCty; assumption).
- apply WfSigØ.
- apply TypeCasesØ.
- apply WfSigU; assumption.
- apply TypeCasesU.
  assert (forall h, find_op_case h op = None 
    -> find_op_case (Sub.h_negshift h 1 i) op = None).
  + intro h'. induction h'; intro orig; auto.
    simpl. simpl in orig. destruct (op==o); auto. discriminate.
  + apply H8. assumption.
  + auto.
  + rewrite ctx_remove_extend. rewrite ctx_remove_extend.
    assert (i+1+1=i+2) by omega. rewrite H8.
    apply c_negshift_typesafe; assumption.
}
Defined.


Fixpoint v_subs_typesafe
  (Γ:ctx) (v:val) (A:vtype) (i:nat) (v_s:val) (A_s:vtype) {struct v}:
  has_vtype Γ v A -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_vtype Γ (Sub.v_sub v (i, v_s)) A
with c_subs_typesafe
  (Γ:ctx) (c:comp) (C:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct c}:
  has_ctype Γ c C -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_ctype Γ (Sub.c_sub c (i, v_s)) C
with h_subs_typesafe
  (Γ:ctx) (h:hcases) (Σ:sig) (D:ctype) (i:nat) (v_s:val) (A_s:vtype) {struct h}:
  has_htype Γ h Σ D -> get_vtype Γ i = Some A_s ->
  has_vtype Γ v_s A_s ->
  has_htype Γ (Sub.h_sub h (i, v_s)) Σ D.
Proof.
{
clear v_subs_typesafe.
revert Γ A i. induction v; intros Γ A i orig in_ctx vstyped;
simpl; inv orig; inv H1; apply TypeV; auto.
+ simpl in *. destruct (num=?i) eqn:cmp.
  * apply Nat.eqb_eq in cmp. rewrite <-cmp in in_ctx.
    rewrite H4 in in_ctx. injection in_ctx. intro samety.
    rewrite samety. inv vstyped. assumption.
  * apply TypeVar. assumption.
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. apply IHv; auto.
+ apply TypeInr. apply IHv; auto.
+ apply TypePair; try apply IHv1 || apply IHv2; auto.
+ apply TypeFun. eapply c_subs_typesafe.
  - assumption.
  - assert (i+1=S i) by omega. rewrite H1. simpl.
    exact in_ctx.
  - apply v_shift_typesafe. assumption. inv H0. assumption.
+ apply TypeHandler.
  - eapply c_subs_typesafe.
    * assumption.
    * assert (i+1=S i) by omega. rewrite H1. simpl. exact in_ctx.
    * apply v_shift_typesafe. assumption. inv H0. inv H3. assumption.
  - eapply h_subs_typesafe.
    * assumption.
    * exact in_ctx.
    * assumption.
}{
clear c_subs_typesafe.
assert (forall i, i+1=S i) as Si by (intro; omega).
assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
revert Γ C i v_s. induction c; intros Γ C i v_s orig in_ctx vstyped;
simpl; inv orig; inv H1; apply TypeC; auto.
+ apply TypeRet. eapply v_subs_typesafe. 2 : exact in_ctx. all: assumption.
+ eapply TypeΠMatch.
  - eapply v_subs_typesafe. exact H7. exact in_ctx. assumption.
  - apply IHc. assumption.
    * rewrite SSi. assumption.
    * rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
      all: (inv H7; inv H2; assumption).
+ eapply TypeΣMatch.
  { eapply v_subs_typesafe. exact H9. exact in_ctx. assumption. }
  all: try apply IHc1 || apply IHc2; try apply v_shift_typesafe; auto.
  all: try (rewrite Si; assumption).
  all: inv H9; inv H2; assumption.
+ eapply TypeApp.
  - eapply v_subs_typesafe. exact H5. exact in_ctx. assumption.
  - eapply v_subs_typesafe. auto. exact in_ctx. assumption.
+ eapply TypeOp. exact H8.
  - eapply v_subs_typesafe. 2: exact in_ctx. assumption. assumption.
  - apply IHc; auto.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption. inv H0.
      eapply get_op_type_wf. exact H5. exact H8.
+ eapply TypeLetRec.
  - apply IHc1. exact H8.
    * rewrite SSi. assumption.
    * rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
      ++ inv H9. inv H1. inv H7. assumption.
      ++ inv H9. inv H1. assumption.
  - apply IHc2. assumption.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption.
      inv H9. inv H1. assumption.
+ eapply TypeDoBind.
  - apply IHc1. exact H7. assumption. assumption.
  - apply IHc2.
    * assumption.
    * rewrite Si. assumption.
    * apply v_shift_typesafe. assumption. inv H7. inv H2. assumption.
+ eapply TypeHandle.
  - eapply v_subs_typesafe. exact H5. exact in_ctx. assumption.
  - apply IHc; auto.
}{
clear h_subs_typesafe.
assert (forall i, i+1=S i) as Si by (intro; omega).
assert (forall i, i+2=S(S i)) as SSi by (intro; omega).
revert Γ Σ D i v_s. induction h; intros Γ Σ D i v_s orig in_ctx vstyped;
simpl; inv orig; inv H2; apply TypeH; auto.
+ apply TypeCasesØ.
+ apply TypeCasesU.
  assert (forall h,
    find_op_case h o = None ->
    find_op_case (Sub.h_sub h (i, v_s)) o = None).
  * intros h' cantfind. induction h'. auto.
    simpl. simpl in cantfind. destruct (o==o0). discriminate.
    apply IHh'. exact cantfind.
  * apply H2. assumption.
  * auto.
  * rewrite SSi. eapply c_subs_typesafe; auto.
    - simpl. exact in_ctx.
    - rewrite <-(v_shift_shift 1 1 0).
      apply v_shift_typesafe. apply v_shift_typesafe. assumption.
}
Defined.

Lemma h_has_case Γ h Σ D op A_op B_op:
  has_htype Γ h Σ D ->
  get_op_type Σ op = Some (A_op, B_op) ->
  exists x k c_op, find_op_case h op = Some (x, k, c_op).
Proof.
revert Γ Σ. induction h; intros Γ Σ typed gets;
inv typed; inv H1; inv H2.
+ simpl in gets. discriminate.
+ simpl in *. destruct (op==o).
  - injection gets. intros. subst.
    exists v. exists v0. exists c. reflexivity.
  - apply IHh in H14; assumption.
Defined.