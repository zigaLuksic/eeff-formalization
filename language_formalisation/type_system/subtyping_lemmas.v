Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\type_system".
Require Import syntax declarational.


Fixpoint subty_pi A B C :
  vsubtype C (TyΠ A B) -> 
  exists A' B', C = (TyΠ A' B') /\ vsubtype A' A /\ vsubtype B' B.
Proof.
intro orig.
inv orig. exists A0. exists B0.
constructor. reflexivity. constructor; assumption.
Qed.


Fixpoint subty_pair Γ v1 v2 A B :
has_vtype Γ (Pair v1 v2) (TyΠ A B) ->
has_vtype Γ v1 A /\ has_vtype Γ v2 B.
Proof.
intro orig. inv orig. inv H1. constructor; assumption.
induction H3.


intro orig. inv orig. inv H1. constructor; assumption.
apply subty_pi in H3. destruct H3. destruct H1. destruct H1.
subst. apply subty_pair in H2.
destruct H2. destruct H3. constructor.
- apply TypeV. assumption. inv H0. assumption.
  eapply TypeVSubtype. exact H1. assumption.
- apply TypeV. assumption. inv H0. assumption.
  eapply TypeVSubtype. exact H2. assumption.
Qed.