Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\PHD\language_formalisation\syntax".
Require Import syntax Relation_Definitions.


Inductive vsubtype : vtype -> vtype -> Prop :=
| VsubtyRefl A : vsubtype A A
| VsubtyTrans A1 A2 A3: vsubtype A1 A2 -> vsubtype A2 A3 -> vsubtype A1 A3
| VsubtyStruc A B : vsubtype A B -> vsubtype A B
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




(*
Inductive vsubtype : vtype -> vtype -> Prop :=
| VsubtyRefl A : vsubtype A A
| VsubtyTrans A1 A2 A3 : vsubtype A1 A2 -> vsubtype A2 A3 -> vsubtype A1 A3
| VsubtyTyΣ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΣ A B) (TyΣ A' B')
| VsubtyTyΠ A A' B B' : 
    vsubtype A A' -> vsubtype B B' -> vsubtype (TyΠ A B) (TyΠ A' B')
| VsubtyFun A A' C C' : 
    vsubtype A' A -> csubtype C C' -> vsubtype (TyFun A C) (TyFun A' C')
| VsubtyHandler C C' D D': 
    csubtype C' C -> csubtype D D' -> vsubtype (TyHandler C D) (TyHandler C' D')

with csubtype : ctype -> ctype -> Prop  :=
| CsubtyRefl C : csubtype C C
| CsubtyTrans C1 C2 C3 : csubtype C1 C2 -> csubtype C2 C3 -> csubtype C1 C3
| Csubty A A' Σ Σ' E : 
    vsubtype A A' -> sigsubtype Σ Σ' -> csubtype (CTy A Σ E) (CTy A' Σ' E)

with sigsubtype : sig -> sig -> Prop :=
| ΣsubtyRefl Σ : sigsubtype Σ Σ
| ΣsubtyTrans Σ1 Σ2 Σ3 : sigsubtype Σ1 Σ2 -> sigsubtype Σ2 Σ3 -> sigsubtype Σ1 Σ3
| Σsubty Σ Σ':
    (forall op A B A' B', (get_op_type Σ op = Some (A, B) -> 
      (get_op_type Σ' op = Some (A', B')) /\ vsubtype A' A /\ vsubtype B B'))
    -> sigsubtype Σ Σ'
. *)