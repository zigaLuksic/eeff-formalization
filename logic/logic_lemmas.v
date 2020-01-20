Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics".
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution". *)
(* Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics". *)

Require Export syntax_lemmas substitution_lemmas type_lemmas.

Lemma operational_in_logic Γ c c' C:
  has_ctype Γ c C -> step c c'-> ceq C Γ c c'. 
Proof.
intros tys steps.
assert (has_ctype Γ c' C) as tys' by (eapply preservation; eauto).
revert C tys tys'. induction steps; intros C tys tys'; apply Ceq.
all: assumption || (inv tys; assumption) || auto.
+ eapply βΠMatch.
+ eapply βΣMatch_Inl.
+ eapply βΣMatch_Inr.
+ eapply βApp.
+ eapply βLetRec.
+ destruct C as [A Σ E]. eapply shape_dobind_full in tys.
  3: reflexivity. 2: reflexivity. destruct tys as [A' [ty1 ty2]].
  eapply CeqDoBind.
  - eapply IHsteps. eauto. eapply preservation; eauto.
  - apply Ceq; try (inv ty2; eassumption) || assumption.
    apply CeqRefl. reflexivity.
+ eapply βDoBind_Ret.
+ eapply βDoBind_Op. 
+ eapply shape_handle in tys. destruct tys as [C' [tyh tyc]].
  eapply CeqHandle. 
  - apply Veq; try (inv tyh; eassumption) || assumption.
    apply VeqRefl. reflexivity.
  - apply IHsteps. assumption. eapply preservation; eauto.
+ eapply βHandle_Ret.
+ eapply βHandle_Op. eauto.
Qed.


Fixpoint veq_subs_logicsafe_weak
  Γ Γ' A v i v_s v_s' A_s (orig: has_vtype Γ' v A) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  veq A Γ (v_subs v v_s i) (v_subs v v_s' i)

with ceq_subs_logicsafe_weak
  Γ Γ' C c i v_s v_s' A_s (orig: has_ctype Γ' c C) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c v_s i) (c_subs c v_s i)

with heq_subs_logicsafe_weak
  Γ Γ' Σ D h i v_s v_s' A_s (orig: has_htype Γ' h Σ D) {struct orig} :
  veq A_s Γ v_s v_s' -> Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h v_s i) (h_subs h v_s i).

Proof.
all: intros vseq ctxs clen.
all: rename veq_subs_logicsafe_weak into VEQ.
all: rename ceq_subs_logicsafe_weak into CEQ.
all: rename heq_subs_logicsafe_weak into HEQ.
{
apply Veq; try (inv orig; eassumption). inv vseq. auto.
eapply v_subs_typesafe; inv vseq; eauto. 
eapply v_subs_typesafe; inv vseq; eauto.
destruct orig. destruct H1.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqInt. reflexivity.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. 
  destruct (n=?i) eqn: ni; simpl.
  - rewrite v_negshift_shift, v_negshift_shift, v_shift_0, v_shift_0.
    apply Nat.eqb_eq in ni. subst. rewrite get_ctx_insert_new in H1. inv H1. 
    inv vseq. assumption. all: omega || assumption.
  - destruct (i<=?n); apply VeqRefl; reflexivity.
+ clear CEQ HEQ. unfold v_subs. simpl. apply VeqPair; eapply VEQ; eauto.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ. unfold v_subs. simpl. apply VeqUnit.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
}




(* =============== TODO =============== *)
Fixpoint veq_subs_logicsafe
  Γ Γ' A v1 v2 i v_s v_s' A_s (orig: veq A Γ' v1 v2) {struct orig} :
  has_vtype Γ v_s A_s -> has_vtype Γ v_s' A_s ->
  Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  veq A Γ (v_subs v1 v_s i) (v_subs v2 v_s' i)

with ceq_subs_logicsafe
  Γ Γ' C c1 c2 i v_s v_s' A_s (orig: ceq C Γ' c1 c2) {struct orig} :
  has_vtype Γ v_s A_s -> has_vtype Γ v_s' A_s -> 
  Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  ceq C Γ (c_subs c1 v_s i) (c_subs c2 v_s i)

with heq_subs_logicsafe
  Γ Γ' Σ D h1 h2 i v_s v_s' A_s (orig: heq Σ D Γ' h1 h2) {struct orig} :
  has_vtype Γ v_s A_s -> has_vtype Γ v_s' A_s -> 
  Γ' = ctx_insert Γ A_s i -> ctx_len Γ >= i ->
  heq Σ D Γ (h_subs h1 v_s i) (h_subs h2 v_s i).
Proof.
all: intros tys tys' ctxs clen.
all: rename veq_subs_logicsafe into VEQ.
all: rename ceq_subs_logicsafe into CEQ.
all: rename heq_subs_logicsafe into HEQ.
{
destruct orig. apply Veq; auto. inv tys. auto.
eapply v_subs_typesafe; eauto. eapply v_subs_typesafe; eauto.
destruct H3.
+ clear VEQ CEQ HEQ. 
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
+ clear VEQ CEQ HEQ.
}
