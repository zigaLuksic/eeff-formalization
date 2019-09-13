Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Export syntax bidirectional Omega Logic.

Ltac inv H := inversion H; clear H; subst.

Lemma val_ctx_shadowing
  (x : var_id) (α : vtype) (β : vtype)
  (Γ : ctx) (v : val) (A : vtype) :
  vcheck (CtxU x α (CtxU x β Γ)) v A ->
  vcheck (CtxU x α Γ) v A 
with comp_ctx_shadowing
  (x : var_id) (α : vtype) (β : vtype)
  (Γ : ctx) (c : comp) (C : ctype) :
  ccheck (CtxU x α (CtxU x β Γ)) c C ->
  ccheck (CtxU x α Γ) c C 
with hcases_ctx_shadowing
  (x : var_id) (α : vtype) (β : vtype)
  (Γ : ctx) (h : hcases) (Σ : sig) (D : ctype) :
  hcheck (CtxU x α (CtxU x β Γ)) h Σ D ->
  hcheck (CtxU x α Γ) h Σ D.
Proof.
  {(* VALUES *)
  destruct v; intro big_ctx.
  (* Var *)
  - inv big_ctx. inv H. simpl in H2.
    induction (s==x) in H2.
    + cut (vsynth (CtxU x α Γ) (Var s) α').
      * intro synth.
        exact (CheckVBySynth _ (Var s) α' α' synth (eq_refl _)).
      * injection H2. intro sametype. rewrite sametype.
        cut (get_vtype (CtxU x α' Γ) s = Some α').
        intro get. exact (SynthVar (CtxU x α' Γ) s α' get).
        rewrite a. simpl.
        induction (x==x).
        -- rewrite sametype in H2. assumption.
        -- destruct b. reflexivity.
    + cut (get_vtype (CtxU x α Γ) s = Some α').
      * intro get_works.
        cut (vsynth (CtxU x α Γ) (Var s) α').
        -- intro synth.
           exact (CheckVBySynth _ (Var s) _ _ synth (eq_refl _)).
        -- exact (SynthVar _ s α' get_works).
      * simpl. induction (s==x).
        -- destruct b. assumption.
        -- assumption.
  (* Unit *)
  - inv big_ctx. inv H.
    cut (vsynth (CtxU x α Γ) Unit TyUnit).
    + intro synth. exact (CheckVBySynth _ Unit _ _ synth (eq_refl _)).
    + exact (SynthUnit _).
  (* Int *)
  - inv big_ctx. inv H.
    cut (vsynth (CtxU x α Γ) (Int t) TyInt).
    + intro synth. exact (CheckVBySynth _ (Int t) _ _ synth (eq_refl _)).
    + exact (SynthInt _ t).
  (* Inl *)
  - inv big_ctx. inv H.
    apply val_ctx_shadowing in H1.
    exact (CheckInl _ v α0 β0 H1).
  (* Inr *)
  - inv big_ctx. inv H.
    apply val_ctx_shadowing in H1.
    exact (CheckInr _ v α0 β0 H1).
  (* Pair *)
  - inv big_ctx. inv H.
    + cut (vcheck (CtxU x α (CtxU x β Γ)) v1 α0).
      cut (vcheck (CtxU x α (CtxU x β Γ)) v2 β0).
      * intros ch2 ch1.
        apply val_ctx_shadowing in ch1.
        apply val_ctx_shadowing in ch2.
        exact (CheckPair _ v1 v2 _ _ ch1 ch2).
      * exact (CheckVBySynth _ v2 _ _ H5 (eq_refl _)).
      * exact (CheckVBySynth _ v1 _ _ H3 (eq_refl _)).
    + apply val_ctx_shadowing in H2.
      apply val_ctx_shadowing in H4.
      exact (CheckPair _ v1 v2 _ _ H2 H4).
  (* Fun *)
  - inv big_ctx. inv H.
    cut (ccheck (CtxU v α0 (CtxU x α Γ)) c C).
    + intro cchecks.
      exact (CheckFun _ v c α0 C cchecks).
    +  


      } 

Lemma val_emptyctx_substitution_lemma
  (vprog : val) (A : vtype)
  (x : var_id) (v : val) (α : vtype) :
  vcheck (CtxU x α CtxØ) vprog A ->
  vcheck CtxØ v α ->
  vcheck CtxØ (vsubst (x, v) vprog) A
with comp_emptyctx_substitution_lemma
  (cprog : comp) (C : ctype)
  (x : var_id) (v : val) (α : vtype) :
  ccheck (CtxU x α CtxØ) cprog C ->
  vcheck CtxØ v α ->
  ccheck CtxØ (csubst (x, v) cprog) C.
Proof.
  (* VALUES *)
  revert A.
  induction vprog; intros A typed_original typed_v.
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
    + apply IHvprog in H1.
      exact (CheckInl CtxØ _ α0 β H1).
      assumption.
  - simpl. inv typed_original. inv H.
    + apply IHvprog in H1.
      exact (CheckInr CtxØ _ α0 β H1).
      assumption.
  - simpl. inv typed_original. inv H.
    + cut (vcheck (CtxU x α CtxØ) vprog1 α0). 
      cut (vcheck (CtxU x α CtxØ) vprog2 β).
      * intros ch2 ch1.
        apply IHvprog1 in ch1. 
        apply IHvprog2 in ch2.
        all: try assumption.
        exact (CheckPair CtxØ _ _ α0 β ch1 ch2).
      * exact (CheckVBySynth _ vprog2 _ _ H5 (eq_refl _)).
      * exact (CheckVBySynth _ vprog1 _ _ H3 (eq_refl _)).
    + apply IHvprog1 in H2. 
      apply IHvprog2 in H4.
      all: try assumption.
      exact (CheckPair CtxØ _ _ α0 β H2 H4).
  - simpl. inv typed_original; induction (v0 == x); try inv H.
    + 
Qed.