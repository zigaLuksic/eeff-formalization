Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional Omega Logic.

Ltac inv H := inversion H; clear H; subst.


Lemma val_emptyctx_substitution_lemma
  (prog : val) (A : vtype)
  (x : var_id) (v : val) (α : vtype) :
  vcheck (CtxU x α CtxØ) prog A ->
  vcheck CtxØ v α ->
  vcheck CtxØ (vsubst (x, v) prog) A.
Proof.
  revert A.
  induction prog; intros A typed_original typed_v.
  - induction (s == x). simpl.
    + inv typed_original. inv H. simpl in H2.
      induction (x == x).
      * inv H2.
        assumption.
      * destruct b.
        reflexivity.
    + inv typed_original. inv H. simpl in H2.
      destruct (s==x) in H2.
      * destruct b. exact e.
      * discriminate.
  - inv typed_original. inv H.
    exact (CheckVBySynth CtxØ Unit _ _ (SynthUnit CtxØ) (eq_refl _)).
  - inv typed_original. inv H.
    exact (CheckVBySynth CtxØ (Int t) _ _ (SynthInt CtxØ t) (eq_refl _)).
  - simpl. inv typed_original.
    + inv H.
    + apply IHprog in H1.
      exact (CheckInl CtxØ _ α0 β H1).
      assumption.
  - simpl. inv typed_original.
    + inv H.
    + apply IHprog in H1.
      exact (CheckInr CtxØ _ α0 β H1).
      assumption.
  - 
      
Qed.