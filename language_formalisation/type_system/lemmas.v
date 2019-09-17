Add Rec LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation".
(* Add Rec LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation". *)
Require Export syntax bidirectional substitution Omega Logic.

Ltac inv H := inversion H; clear H; subst.


Lemma vsub_safe
  (Γ : ctx) (v : val) (A : vtype)
  (v_s : val) (α : vtype) :
  vcheck (CtxU Γ α) v A ->
  vcheck (CtxU Γ α) v_s α ->
  vcheck (CtxU Γ α) (Sub.v_sub v v_s) A


Lemma vsub_lemma 
  (Γ : ctx) (v : val) (A : vtype)
  (v_s : val) (α : vtype) :
  vcheck (CtxU Γ α) v A ->
  vcheck Γ v_s α ->
  vcheck Γ (vsub_out v v_s) A
with csub_lemma 
  (Γ : ctx) (c : comp) (C : ctype)
  (v_s : val) (α : vtype) :
  ccheck (CtxU Γ α) c C ->
  vcheck Γ v_s α ->
  ccheck Γ (csub_out c v_s) C
with hsub_lemma 
  (Γ : ctx) (h : hcases) (Σ : sig) (D : ctype)
  (v_s : val) (α : vtype) :
  hcheck (CtxU Γ α) h Σ D ->
  vcheck Γ v_s α ->
  hcheck Γ (hsub_out h v_s) Σ D.
Proof.
{
clear vsub_lemma.
revert Γ A.
induction v; intros Γ A orig ty_v_s.
- inv orig. inv H. unfold vsub_out. simpl.
  destruct v as (name, db_i). simpl.
  induction db_i; simpl.
  + simpl in H2.
    rewrite (vshifts_cancel 0 v_s).
    injection H2. intro sametype.
    rewrite <-sametype. assumption.
  + simpl in H2.
    assert (vsynth Γ (Var (name, db_i - 0)) A)
    by exact (SynthVar Γ _ A H2).
    exact (CheckVBySynth Γ _ A H).
- inv orig. inv H. unfold vsub_out. simpl.
  assert (vsynth Γ Unit TyUnit) by exact (SynthUnit _).
  exact (CheckVBySynth _ _ _ H).
- inv orig. inv H. unfold vsub_out. simpl.
  assert (vsynth Γ (Int t) TyInt) by exact (SynthInt _ _).
  exact (CheckVBySynth _ _ _ H).
- inv orig. inv H. unfold vsub_out. simpl.
  specialize (IHv Γ α0).
  apply IHv in H1.
  unfold vsub_out in H1.
  exact (CheckInl Γ _ α0 β H1).
  assumption.
- inv orig. inv H. unfold vsub_out. simpl.
  specialize (IHv Γ β).
  apply IHv in H1.
  unfold vsub_out in H1.
  exact (CheckInr Γ _ α0 β H1).
  assumption.
- inv orig. 
  + inv H. unfold vsub_out. simpl.
    specialize (IHv1 Γ α0).
    assert (vcheck (CtxU Γ α) v1 α0)
    by exact (CheckVBySynth _ _ _ H3).
    apply IHv1 in H.
    specialize (IHv2 Γ β).
    assert (vcheck (CtxU Γ α) v2 β)
    by exact (CheckVBySynth _ _ _ H5).
    apply IHv2 in H0.
    exact (CheckPair Γ _ _ α0 β H H0).
    assumption. assumption.
  + unfold vsub_out. simpl.
    specialize (IHv1 Γ α0).
    apply IHv1 in H2.
    specialize (IHv2 Γ β).
    apply IHv2 in H4.
    exact (CheckPair Γ _ _ α0 β H2 H4).
    assumption. assumption.
- inv orig. inv H.
  unfold vsub_out. simpl.



    }

Qed.
