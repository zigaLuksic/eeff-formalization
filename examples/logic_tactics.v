(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\syntax". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\type_system". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\substitution". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\operational_semantics". *)
(* Add LoadPath "C:\Users\Ziga\Documents\Ziga_podatki\repositories\eeff-formalization\logic". *)
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\syntax".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\type_system".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\substitution".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\operational_semantics".
Add LoadPath "E:\Ziga_Podatki\faks\eeff-formalization\logic".

Require Export type_lemmas logic_lemmas.


Ltac simpl_c_subs := 
unfold c_subs2_out; unfold c_subs_out; unfold c_subs; simpl.

Ltac obvious := 
   apply WfCtxØ || (apply WfCtxU; obvious) 
|| apply WfTCtxØ  || (apply WfTCtxU; obvious) 
|| apply WfEqsØ || apply WfSigØ || (apply WfSigU; obvious)
|| apply WfTyUnit || apply WfTyInt || (apply WfTyHandler; obvious)
|| (apply WfTyFun; obvious) || (apply WfTySum; obvious)
|| (apply WfTyProd; obvious) || (apply WfCTy; obvious)
|| auto.

Ltac obvious_vtype := (
(apply TypeV; (
   (apply TypeUnit; obvious)
|| (apply TypeInt; obvious)
|| (apply TypeLeft; obvious_vtype)
|| (apply TypeRight; obvious_vtype)
|| (apply TypePair; obvious_vtype)
|| (apply TypeVar; simpl in *; obvious)
|| obvious)
)
|| obvious).

Ltac vtype_step := (
(apply TypeV; (
   (apply TypeUnit; obvious)
|| (apply TypeInt; obvious)
|| (apply TypeLeft; obvious)
|| (apply TypeRight; obvious)
|| (apply TypePair; obvious)
|| (apply TypeFun; obvious)
|| (apply TypeVar; simpl in *; obvious)
|| obvious)
)
|| obvious).


Ltac obvious_ctype := (
(apply TypeC; (
  (apply TypeRet; obvious_vtype)
|| (eapply TypeApp; obvious_vtype)
|| (eapply TypeSumMatch; obvious_vtype)
|| obvious)
)
|| obvious).

Ltac ctype_step := (
(apply TypeC; (
  (apply TypeRet; obvious)
|| (eapply TypeApp; obvious)
|| (eapply TypeSumMatch; obvious)
|| obvious)
)
|| obvious).
