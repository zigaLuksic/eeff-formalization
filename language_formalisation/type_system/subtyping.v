(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax". *)
Add LoadPath "E:\Ziga_Podatki\faks\PHD\language_formalisation\syntax".
Require Import syntax.


Inductive vsubtype : vtype -> vtype -> Prop :=
| VsubtyUnit : vsubtype TyUnit TyUnit
| VsubtyInt : vsubtype TyInt TyInt
| VsubtyTyØ : vsubtype TyØ TyØ
| VsubtyTyΣ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΣ A B) (TyΣ A' B')
| VsubtyTyΠ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΠ A B) (TyΠ A' B')
| VsubtyFun A A' C C' : 
    vsubtype A' A -> csubtype C C' -> vsubtype (TyFun A C) (TyFun A' C')
| VsubtyHandler C C' D D': 
    csubtype C' C -> csubtype D D' -> vsubtype (TyHandler C D) (TyHandler C' D')

with csubtype : ctype -> ctype -> Prop  :=
| Csubty A A' Σ Σ' E : 
    vsubtype A A' -> sig_subtype Σ Σ' -> csubtype (CTy A Σ E) (CTy A' Σ' E)

with sig_subtype : sig -> sig -> Prop :=
| SigØsubty : sig_subtype SigØ SigØ
| SigUsubty Σ Σ' op A B A' B' : 
    sig_subtype Σ Σ' -> vsubtype A' A -> vsubtype B B' ->
    sig_subtype (SigU Σ op A B) (SigU Σ' op A' B')
.

Inductive ctx_subtype : ctx -> ctx -> Prop :=
| CtxØsubty : ctx_subtype CtxØ CtxØ
| CtxUsubty Γ Γ' A A' : 
    ctx_subtype Γ Γ' -> vsubtype A A' -> ctx_subtype (CtxU Γ A) (CtxU Γ' A')
.

Ltac inv H := inversion H; clear H; subst.

(* Weird notation for SPEED! *)
Fixpoint vsubtype_trans A1 A2 A3 
  (A12 : vsubtype A1 A2) {struct A12} : vsubtype A2 A3 -> vsubtype A1 A3
with vsubtype_trans_rev A1 A2 A3
  (A21 : vsubtype A2 A1) {struct A21} : vsubtype A3 A2 -> vsubtype A3 A1
with csubtype_trans C1 C2 C3
  (C12 : csubtype C1 C2) {struct C12} : csubtype C2 C3 -> csubtype C1 C3
with csubtype_trans_rev C1 C2 C3 
  (C21 : csubtype C2 C1) {struct C21} : csubtype C3 C2 -> csubtype C3 C1
with sig_subtype_trans Σ1 Σ2 Σ3 
  (S12 : sig_subtype Σ1 Σ2) {struct S12} : sig_subtype Σ2 Σ3 -> 
  sig_subtype Σ1 Σ3
with sig_subtype_trans_rev Σ1 Σ2 Σ3
  (S21 : sig_subtype Σ2 Σ1) (S32 : sig_subtype Σ3 Σ2) {struct S21} : 
  sig_subtype Σ3 Σ1.
Proof.
{
clear sig_subtype_trans sig_subtype_trans_rev.
intros A23; destruct A12; try assumption; inv A23.
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans. exact A12_1. assumption.
  - eapply vsubtype_trans. exact A12_2. assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans. exact A12_1. assumption.
  - eapply vsubtype_trans. exact A12_2. assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans_rev. exact A12. assumption. 
  - eapply csubtype_trans. exact H. assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans_rev. exact H. assumption. 
  - eapply csubtype_trans. exact H0. assumption.
}{
clear sig_subtype_trans sig_subtype_trans_rev.
intros A32; destruct A21; try assumption; inv A32.
+ apply VsubtyTyΣ.
  - eapply vsubtype_trans_rev. exact A21_1. assumption.
  - eapply vsubtype_trans_rev. exact A21_2. assumption.
+ apply VsubtyTyΠ.
  - eapply vsubtype_trans_rev. exact A21_1. assumption.
  - eapply vsubtype_trans_rev. exact A21_2. assumption.
+ apply VsubtyFun.
  - eapply vsubtype_trans. exact A21. assumption. 
  - eapply csubtype_trans_rev. exact H. assumption.
+ apply VsubtyHandler.
  - eapply csubtype_trans. exact H. assumption. 
  - eapply csubtype_trans_rev. exact H0. assumption.
}{
clear vsubtype_trans_rev csubtype_trans csubtype_trans_rev sig_subtype_trans_rev.
intros C23; destruct C12. inv C23.
apply Csubty.
- eapply vsubtype_trans. exact H. assumption.
- eapply sig_subtype_trans. exact H0. assumption.
}{
clear vsubtype_trans csubtype_trans csubtype_trans_rev sig_subtype_trans.
intros C32; destruct C21. inv C32.
apply Csubty.
- eapply vsubtype_trans_rev. exact H. assumption.
- eapply sig_subtype_trans_rev. exact H0. assumption.
}{
clear csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans_rev.
intros S23. destruct S12. inv S23.
apply SigØsubty.
inv S23. apply SigUsubty. 
+ eapply sig_subtype_trans. exact S12. assumption.
+ eapply vsubtype_trans_rev. exact H. assumption.
+ eapply vsubtype_trans. exact H0. assumption.
}{
clear csubtype_trans csubtype_trans_rev.
clear sig_subtype_trans.
destruct S21. inv S32.
apply SigØsubty.
inv S32. apply SigUsubty. 
+ eapply sig_subtype_trans_rev. exact S21. assumption.
+ eapply vsubtype_trans. exact H. assumption.
+ eapply vsubtype_trans_rev. exact H0. assumption.
}
Qed.


Lemma vsubty_refl v : vsubtype v v
with csubty_refl c : csubtype c c
with sigsubty_refl Σ : sig_subtype Σ Σ
with ctx_subty_refl Γ : ctx_subtype Γ Γ.
Proof.
{induction v.
+ apply VsubtyUnit.
+ apply VsubtyInt.
+ apply VsubtyTyØ.
+ apply VsubtyTyΣ; assumption.
+ apply VsubtyTyΠ; assumption.
+ apply VsubtyFun. assumption. apply csubty_refl.
+ apply VsubtyHandler; apply csubty_refl.
}{ destruct c. apply Csubty.
apply vsubty_refl. apply sigsubty_refl.
}{ induction Σ.
+ apply SigØsubty.
+ apply SigUsubty; try assumption || apply vsubty_refl.
}{induction Γ.
+ apply CtxØsubty.
+ apply CtxUsubty. assumption. apply vsubty_refl.
}
Qed.