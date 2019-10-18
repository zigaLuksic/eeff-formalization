Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import syntax.


Inductive vsubtype : vtype -> vtype -> Prop :=
| VsubtyUnit : vsubtype TyUnit TyUnit
| VsubtyInt : vsubtype TyInt TyInt
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
    vsubtype A A' -> sigsubtype Σ Σ' -> csubtype (CTy A Σ E) (CTy A' Σ' E)

with sigsubtype : sig -> sig -> Prop :=
| Σsubty Σ Σ':
    (forall op A B A' B', (get_op_type Σ op = Some (A, B) -> 
      (get_op_type Σ' op = Some (A', B')) /\ vsubtype A' A /\ vsubtype B B'))
    -> sigsubtype Σ Σ'
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
with sigsubtype_trans Σ1 Σ2 Σ3 
  (S12 : sigsubtype Σ1 Σ2) {struct S12} : sigsubtype Σ2 Σ3 -> sigsubtype Σ1 Σ3
with sigsubtype_trans_rev Σ1 Σ2 Σ3
  (S21 : sigsubtype Σ2 Σ1) {struct S21} : sigsubtype Σ3 Σ2-> sigsubtype Σ3 Σ1.
Proof.
{
clear sigsubtype_trans sigsubtype_trans_rev.
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
clear sigsubtype_trans sigsubtype_trans_rev.
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
clear vsubtype_trans_rev csubtype_trans csubtype_trans_rev sigsubtype_trans_rev.
intros C23; destruct C12. inv C23.
apply Csubty.
- eapply vsubtype_trans. exact H. assumption.
- eapply sigsubtype_trans. exact H0. assumption.
}{
clear vsubtype_trans csubtype_trans csubtype_trans_rev sigsubtype_trans.
intros C32; destruct C21. inv C32.
apply Csubty.
- eapply vsubtype_trans_rev. exact H. assumption.
- eapply sigsubtype_trans_rev. exact H0. assumption.
}{
clear vsubtype_trans vsubtype_trans_rev.
clear csubtype_trans csubtype_trans_rev.
clear sigsubtype_trans sigsubtype_trans_rev.
intros S23; destruct S12. inv S23.
apply Σsubty. intros.
apply H0. eapply H in H1. destruct H1. exact H1.
}{
clear vsubtype_trans vsubtype_trans_rev.
clear csubtype_trans csubtype_trans_rev.
clear sigsubtype_trans sigsubtype_trans_rev.
intros S32; destruct S21. inv S32.
apply Σsubty. intros.
apply H. eapply H0 in H1. destruct H1. exact H1.
}
Qed.
