Definition v_switch210_vars v := (v_switch_vars (v_switch_vars v 1 0) 2 1).
Definition c_switch210_vars c := (c_switch_vars (c_switch_vars c 1 0) 2 1).
Definition h_switch210_vars h := (h_switch_vars (h_switch_vars h 1 0) 2 1).





Fixpoint v_switch_vars (v:val) (i:nat) (j:nat) :=
match v with
| Var (name, num) =>
    if num =? i then Var (name, j)
    else if num =? j then Var (name, i)
    else Var (name, num)
| Unit => Unit
| Int n => Int n
| Inl v' => Inl (v_switch_vars v' i j)
| Inr v' => Inr (v_switch_vars v' i j)
| Pair v1 v2 => Pair (v_switch_vars v1 i j) (v_switch_vars v2 i j)
| Fun x c => Fun x (c_switch_vars c (i+1) (j+1))
| Handler x c_ret h =>
    Handler x (c_switch_vars c_ret (i+1) (j+1)) (h_switch_vars h i j)
end
with c_switch_vars (c:comp) (i:nat) (j:nat) :=
match c with
| Ret v => Ret (v_switch_vars v i j)
| Absurd v => Absurd (v_switch_vars v i j)
| ΠMatch v (x, y) c =>
    ΠMatch (v_switch_vars v i j) (x,y) (c_switch_vars c (i+2) (j+2))
| ΣMatch v xl cl xr cr =>
    ΣMatch (v_switch_vars v i j) xl (c_switch_vars cl (i+1) (j+1)) 
      xr (c_switch_vars cr (i+1) (j+1))
| App v1 v2 => App (v_switch_vars v1 i j) (v_switch_vars v2 i j)
| Op op v_arg y c => 
    Op op (v_switch_vars v_arg i j) y (c_switch_vars c (i+1) (j+1))
| LetRec f x c1 c2 =>
    LetRec f x (c_switch_vars c1 (i+2) (j+2)) (c_switch_vars c2 (i+1) (j+1))
| DoBind x c1 c2 => 
    DoBind x (c_switch_vars c1 i j) (c_switch_vars c2 (i+1) (j+1))
| Handle v c' => Handle (v_switch_vars v i j) (c_switch_vars c' i j)
end
with h_switch_vars (h:hcases) (i:nat) (j:nat) :=
match h with
| CasesØ => CasesØ
| CasesU h op x k c =>
    CasesU (h_switch_vars h i j) op x k (c_switch_vars c (i+2) (j+2))
end.



Lemma change_j_get_k Γ j k Aj :
  j <> k -> get_vtype Γ k = get_vtype (ctx_change_var Γ j Aj) k.
Proof.
revert j k. induction Γ; intros j k neq_jk; auto.
destruct k; destruct j; auto.
+ omega.
+ simpl. apply IHΓ. omega.
Qed.

Lemma change_j_get_j Γ j Aj_orig Aj 
  (p_j : get_vtype Γ j = Some Aj_orig) :
  get_vtype (ctx_change_var Γ j Aj) j = Some Aj.
Proof.
revert j p_j. induction Γ; intros j p_j; simpl in p_j.
+ discriminate.
+ destruct j; auto. simpl. apply IHΓ. assumption.
Qed.


Lemma v_switch_ii v i : v_switch_vars v i i = v
with c_switch_ii c i : c_switch_vars c i i = c
with h_switch_ii h i : h_switch_vars h i i = h.
Proof.
{
revert i. induction v; intros i; simpl; try reflexivity;
try f_equal; try apply IHv || apply IHv1 || apply IHv2.
+ destruct v as (name, num). destruct (num=?i) eqn:cmp.
  apply Nat.eqb_eq in cmp. rewrite cmp. reflexivity. reflexivity.
+ apply c_switch_ii.
+ apply c_switch_ii.
+ apply h_switch_ii.
}{
revert i. induction c; intros i; simpl; try reflexivity; try destruct p;
try f_equal; try apply v_switch_ii; try apply IHc || apply IHc1 || apply IHc2.
}{
revert i. induction h; intros i; simpl; try reflexivity.
f_equal. apply IHh. apply c_switch_ii.
}
Qed.

Lemma v_switchswitch v i j:
  v_switch_vars (v_switch_vars v i j) i j = v
with c_switchswitch c i j:
  c_switch_vars (c_switch_vars c i j) i j = c
with h_switchswitch h i j:
  h_switch_vars (h_switch_vars h i j) i j = h.
Proof.
all: revert i j.
{
induction v; intros i j; simpl; try reflexivity; try f_equal;
try apply IHv || apply IHv1 || apply IHv2;
try apply c_switchswitch || apply h_switchswitch.

destruct v as (name, num).
destruct (num=?i) eqn:cmpi;
destruct (num=?j) eqn:cmpj; simpl.
+ apply Nat.eqb_eq in cmpi. apply Nat.eqb_eq in cmpj. rewrite cmpi in *.
  rewrite cmpj. rewrite <-beq_nat_refl. auto.
+ apply Nat.eqb_eq in cmpi. rewrite cmpi in *. rewrite Nat.eqb_neq in cmpj.
  apply not_eq_sym in cmpj. rewrite <-Nat.eqb_neq in cmpj.
  rewrite cmpj. rewrite <-beq_nat_refl. reflexivity.
+ apply Nat.eqb_eq in cmpj. rewrite cmpj in *. rewrite Nat.eqb_neq in cmpi.
  apply not_eq_sym in cmpi. rewrite <-Nat.eqb_neq in cmpi.
  rewrite cmpi. rewrite <-beq_nat_refl. reflexivity.
+ rewrite cmpi. rewrite cmpj. reflexivity.
}{
induction c; intros i j; try destruct p; simpl; f_equal;
try apply v_switchswitch || apply IHc || apply IHc1 || apply IHc2.
}{
induction h; intros i j; simpl.
reflexivity. f_equal. apply IHh. apply c_switchswitch.
}
Qed.

Lemma v_switch_sym v i j :
  v_switch_vars v i j = v_switch_vars v j i
with c_switch_sym c i j :
  c_switch_vars c i j = c_switch_vars c j i
with h_switch_sym h i j :
  h_switch_vars h i j = h_switch_vars h j i.
Proof.
{
induction v; simpl;
try f_equal; try apply IHv || apply IHv1 || apply IHv2;
try apply h_switch_sym || apply c_switch_sym; try reflexivity.
destruct v as (name, num).
destruct (num=?i) eqn:cmpi. destruct (num=?j) eqn:cmpj.
apply Nat.eqb_eq in cmpi. apply Nat.eqb_eq in cmpj.
rewrite cmpj, cmpi in *. all: auto.
}{
revert i j. induction c; intros i j; try destruct p; simpl;
try f_equal; try apply IHc || apply IHc1 || apply IHc2;
apply v_switch_sym.
}{
induction h; simpl; f_equal; try auto || apply IHh.
}
Qed.

Lemma switch_ij_get_k Γ k i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  i <> k -> j <> k ->
  get_vtype Γ k = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) k.
Proof.
revert k i j p_i p_j. induction Γ;
intros k i j p_i p_j neq_ik neq_jk. auto.
revert i j p_i p_j neq_ik neq_jk. destruct k;
intros i j p_i p_j neq_ik neq_jk.
+ destruct i.
  - omega.
  - simpl. destruct j; auto. omega.
+ destruct i; destruct j; simpl; auto.
  - apply change_j_get_k. omega.
  - apply change_j_get_k. omega.
  - unfold ctx_switch_vars in IHΓ. apply IHΓ; auto; omega.
Qed.
      
Lemma switch_ij_get_j Γ i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  get_vtype Γ i = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) j.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_i. rewrite p_i.
  apply (change_j_get_j Γ j Aj). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma switch_ij_get_i Γ i j Ai Aj
  (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) :
  get_vtype Γ j = get_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) i.
Proof.
revert i j p_i p_j. induction Γ; intros i j p_i p_j.
auto.
destruct i; destruct j; auto; simpl.
+ apply eq_sym. simpl in p_j. rewrite p_j.
  apply (change_j_get_j Γ i Ai). auto.
+ unfold ctx_switch_vars in IHΓ. apply IHΓ. auto. auto.
Qed.

Lemma ctx_switch_extend1 Γ A i j Ai Aj
    (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) 
    (pp_i : get_vtype (CtxU Γ A) (i+1) = Some Ai)
    (pp_j : get_vtype (CtxU Γ A) (j+1) = Some Aj) :
  CtxU (ctx_switch_vars Γ i j Ai Aj p_i p_j) A
    = 
  (ctx_switch_vars (CtxU Γ A) (i+1) (j+1) Ai Aj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; auto.
+ rename v into G. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (ctx_change_var Γ' j Ai) A
      =
    ctx_change_var (CtxU Γ' A) (j + 1) Ai).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+1 = S j) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ G) i Aj)).
    rewrite H. f_equal.
    destruct i; auto; simpl.
    assert (i+1 = S i) by omega; rewrite H0; auto.
Qed.

Lemma ctx_switch_extend2 Γ B A i j Ai Aj
    (p_i : get_vtype Γ i = Some Ai) (p_j : get_vtype Γ j = Some Aj) 
    (pp_i : get_vtype (CtxU (CtxU Γ B) A) (i+2) = Some Ai)
    (pp_j : get_vtype (CtxU (CtxU Γ B) A) (j+2) = Some Aj) :
  CtxU (CtxU (ctx_switch_vars Γ i j Ai Aj p_i p_j) B) A
    = 
  (ctx_switch_vars (CtxU (CtxU Γ B) A) (i+2) (j+2) Ai Aj pp_i pp_j).
Proof.
revert i j p_i p_j pp_i pp_j. induction Γ; intros i j p_i p_j pp_i pp_j.
+ destruct i; destruct j; simpl in *; discriminate.
+ rename v into G. unfold ctx_switch_vars.
  assert (forall Γ',
    CtxU (CtxU (ctx_change_var Γ' j Ai) B) A
      =
    ctx_change_var (CtxU (CtxU Γ' B) A) (j + 2) Ai).
  * intro. simpl. destruct i; auto; simpl;
    assert (j+2 = S (S j)) by omega; rewrite H; auto.
  * specialize (H (ctx_change_var (CtxU Γ G) i Aj)).
    rewrite H. f_equal.
    destruct i; auto; simpl.
    assert (i+2 = S (S i)) by omega; rewrite H0; auto.
Qed.


Lemma find_op_None_switch h i j op:
  find_op_case h op = None -> find_op_case (h_switch_vars h i j) op = None.
Proof.
intro orig. induction h; auto.
simpl. simpl in *.
destruct (op==o).
+ discriminate.
+ apply IHh. assumption.
Qed.

Lemma find_op_Some_switch h i j op x_op k_op c_op:
  find_op_case h op = Some (x_op, k_op, c_op) ->
  find_op_case (h_switch_vars h i j) op
    =
  Some (x_op, k_op, c_switch_vars c_op (i+2) (j+2)).
Proof.
intro orig.
induction h; auto; simpl; simpl in *.
+ discriminate.
+ destruct (op==o).
  - f_equal. inv orig. auto.
  - apply IHh. auto.
Qed.

Lemma v_no_var_switch_i_j v i j:
  v_no_var v j -> v_no_var (v_switch_vars v j i) i
with c_no_var_switch_i_j c i j:
  c_no_var c j -> c_no_var (c_switch_vars c j i) i
with h_no_var_switch_i_j h i j:
  h_no_var h j -> h_no_var (h_switch_vars h j i) i.
Proof.
{
clear v_no_var_switch_i_j.
revert i j; induction v; intros i j orig; simpl; auto;
try constructor; try destruct orig; simpl; auto.
destruct v as (name, num).
destruct (num=?j) eqn:cmpj.
+ simpl in orig. destruct orig. apply Nat.eqb_eq in cmpj. auto.
+ destruct (num=?i) eqn:cmpi; simpl.
  * apply Nat.eqb_eq in cmpi. rewrite cmpi in *. simpl in orig. auto.
  * apply Nat.eqb_neq in cmpi. auto.
}{
clear c_no_var_switch_i_j.
revert i j; induction c; intros i j orig; try destruct p; simpl; auto;
try constructor; try destruct orig; simpl; auto.
constructor; destruct H0; auto.
}{
clear h_no_var_switch_i_j.
revert i j; induction h; intros i j orig; simpl; auto;
try constructor; try destruct orig; simpl; auto.
}
Qed.



Fixpoint ctx_change_var (Γ:ctx) (i:nat) (A:vtype) :=
  match Γ, i with
  | CtxØ, _ => CtxØ
  | CtxU Γ' A', 0 => CtxU Γ' A
  | CtxU Γ' A', S i' => CtxU (ctx_change_var Γ' i' A) A'
  end.


Definition ctx_switch_vars (Γ : ctx) (i:nat) (j:nat) (A:vtype) (B:vtype)
  (proof_i : get_vtype Γ i = Some A) (proof_j: get_vtype Γ j = Some B) : ctx
:=
  ctx_change_var (ctx_change_var Γ i B) j A.




Lemma extend_get_proof Γ A i Ai:
  get_vtype Γ i = Some Ai-> get_vtype (CtxU Γ A) (i + 1) = Some Ai.
Proof.
assert (i + 1 = S i) by omega.
induction Γ; rewrite H; auto.
Qed.

Lemma c_switch210_shift_1_0 c :
  c_switch210_vars (Sub.c_shift c 1 0) = Sub.c_shift c 1 2.
Proof.
  apply c_switch_SSi_Si_i_shift_1.
Qed.


Lemma v_switch_shift v i j d cut:
  cut <= i -> cut <= j ->
  v_switch_vars (Sub.v_shift v d cut) (i + d) (j + d) 
    =
  Sub.v_shift (v_switch_vars v i j) d cut
with c_switch_shift c i j d cut:
  cut <= i -> cut <= j ->
  c_switch_vars (Sub.c_shift c d cut) (i + d) (j + d) 
    =
  Sub.c_shift (c_switch_vars c i j) d cut
with h_switch_shift h i j d cut:
  cut <= i -> cut <= j ->
  h_switch_vars (Sub.h_shift h d cut) (i + d) (j + d) 
    =
  Sub.h_shift (h_switch_vars h i j) d cut.
Proof.
all: revert i j.
{
induction v; intros i j cuti cutj; simpl; try f_equal; try reflexivity; simpl;
try apply IHv || apply IHv1 || apply IHv2 || apply h_switch_shift; try omega.
{
destruct v as (name, n). simpl.

destruct (cut<=?n) eqn:cut_n;
destruct (n=?i) eqn:n_i; simpl;
apply leb_correct in cutj; try rewrite cutj; simpl.
+ apply Nat.eqb_eq in n_i. rewrite n_i. rewrite <-beq_nat_refl. auto.
+ assert (n+d =? i+d = false).
  - apply Nat.eqb_neq. apply Nat.eqb_neq in n_i. omega.
  - rewrite H.
    destruct (n=?j) eqn:n_j; simpl.
    * apply Nat.eqb_eq in n_j. rewrite n_j. rewrite <-beq_nat_refl.
      assert (cut <=? i = true).
      { apply leb_correct. assumption. }
      rewrite H0. reflexivity.
    * assert (n+d =? j+d = false).
      -- apply Nat.eqb_neq. apply Nat.eqb_neq in n_j. omega.
      -- rewrite H0. rewrite cut_n. reflexivity.
+ apply Nat.eqb_eq in n_i. rewrite n_i.
  destruct (d=?0) eqn:d0.
  - apply Nat.eqb_eq in d0. rewrite d0.
    assert (i =? i+0 = true).
    { apply Nat.eqb_eq. omega. }
    rewrite H. reflexivity.
  - rewrite n_i in cut_n. apply leb_correct in cuti.
    rewrite cuti in cut_n. discriminate.
+ destruct (n=?j) eqn:nj.
  - apply Nat.eqb_eq in nj. rewrite <-nj in cutj.
    rewrite cutj in cut_n. discriminate.
  - destruct (n=?j+d) eqn:njd.
    * apply Nat.eqb_eq in njd. rewrite njd in cut_n.
      apply leb_complete in cutj.
      assert ((cut <=? j + d) = true).
      apply leb_correct. omega.
      rewrite H in cut_n. discriminate.
    * destruct (n=?i+d) eqn:nid.
      ** apply Nat.eqb_eq in nid. rewrite nid in cut_n.
        assert ((cut <=? i + d) = true).
        apply leb_correct. omega.
        rewrite H in cut_n. discriminate.
      ** simpl. rewrite cut_n. reflexivity.
}
all: assert (i+d+1=i+1+d) by omega.
all: assert (j+d+1=j+1+d) by omega;
rewrite H, H0; apply c_switch_shift; omega.
}{
revert cut.
induction c; intros cut i j cuti cutj; try destruct p as (name, num); simpl;
try f_equal; try apply IHc || apply v_switch_shift || apply IHc1; try omega.
all:
  assert (i+d+1=i+1+d) as id1 by omega;
  assert (j+d+1=j+1+d) as jd1 by omega;
  assert (i+d+2=i+2+d) as id2 by omega;
  assert (j+d+2=j+2+d) as jd2 by omega;
  try rewrite id1, jd1; try rewrite id2, jd2;
  try apply IHc || apply IHc1 || apply IHc2; omega.
}{
revert cut. induction h; intros cut i j cuti cutj; simpl.
reflexivity.
f_equal.
+ apply IHh; omega.
+ assert (i+d+2=i+2+d) as id2 by omega.
  assert (j+d+2=j+2+d) as jd2 by omega.
  rewrite id2, jd2. apply c_switch_shift; omega.
}
Qed.

Lemma v_sub_switch v v_s i j:
  Sub.v_sub (v_switch_vars v i j) (i, v_s)
    =
  v_switch_vars (Sub.v_sub v (j, v_switch_vars v_s i j)) i j
with c_sub_switch c v_s i j:
  Sub.c_sub (c_switch_vars c i j) (i, v_s)
    =
  c_switch_vars (Sub.c_sub c (j, v_switch_vars v_s i j)) i j
with h_sub_switch h v_s i j:
  Sub.h_sub (h_switch_vars h i j) (i, v_s)
    =
  h_switch_vars (Sub.h_sub h (j, v_switch_vars v_s i j)) i j.
Proof.
all: revert i j.
{
clear v_sub_switch. induction v; intros i j; simpl; try reflexivity;
try f_equal; try apply IHv || apply IHv1 || apply IHv2.
+ destruct v as (name, num). simpl.
  destruct (num=?i) eqn:cmpi.
  - apply Nat.eqb_eq in cmpi. rewrite cmpi. simpl.
    destruct (j=?i) eqn:cmp.
    * apply Nat.eqb_eq in cmp. rewrite cmp. rewrite <-beq_nat_refl.
      rewrite v_switch_ii. rewrite v_switch_ii. reflexivity.
    * rewrite Nat.eqb_neq in cmp.
      apply not_eq_sym in cmp. rewrite <-Nat.eqb_neq in cmp.
      rewrite cmp. simpl. rewrite <-beq_nat_refl. reflexivity.
  - simpl. destruct (num=?j) eqn:cmpj.
    * simpl. rewrite <-beq_nat_refl. rewrite v_switchswitch. reflexivity.
    * simpl. rewrite cmpi. rewrite cmpj. reflexivity.
+ specialize (c_sub_switch c (Sub.v_shift v_s 1 0) (i+1) (j+1)).
  rewrite c_sub_switch. f_equal. f_equal. f_equal. apply v_switch_shift; omega.
+ specialize(c_sub_switch c (Sub.v_shift v_s 1 0) (i+1) (j+1)).
  rewrite c_sub_switch. f_equal. f_equal. f_equal. apply v_switch_shift; omega.
+ apply h_sub_switch.
}
{
clear c_sub_switch.
revert v_s. induction c; intros v_s i j; try destruct p as (name, num); 
simpl; f_equal; try apply v_sub_switch || apply IHc || apply IHc1;
try rewrite IHc || rewrite IHc1 || rewrite IHc2;
f_equal; f_equal; f_equal; apply v_switch_shift; omega.
}{
clear h_sub_switch.
induction h; intros i j; simpl; f_equal; try auto.
rewrite c_sub_switch. f_equal. f_equal. f_equal.
apply v_switch_shift; omega.
}
Qed.

Lemma v_switch_Si_i_shift_1 v i:
  v_switch_vars (Sub.v_shift v 1 (S i)) (S i) i = Sub.v_shift v 1 i
with c_switch_Si_i_shift_1 c i:
  c_switch_vars (Sub.c_shift c 1 (S i)) (S i) i = Sub.c_shift c 1 i
with h_switch_Si_i_shift_1 h i:
  h_switch_vars (Sub.h_shift h 1 (S i)) (S i) i = Sub.h_shift h 1 i.
Proof.
{
clear v_switch_Si_i_shift_1.
revert i. induction v; intros i; simpl.
{
destruct v as (name, n). simpl.
destruct n; simpl.
+ destruct i; auto.
+ destruct (i <=? n) eqn:cmp; simpl.
  - apply leb_complete in cmp.
    assert (n + 1 <> i) by omega.
    rewrite <-Nat.eqb_neq in H. rewrite H.
    assert (i <= S n) by omega. apply leb_correct in H0. rewrite H0.
    destruct i; auto.
    assert (n + 1 <> i) by omega.
    rewrite <-Nat.eqb_neq in H1. rewrite H1. auto.
  - apply leb_iff_conv in cmp.
    assert (n<>i) by omega. rewrite <-Nat.eqb_neq in H. rewrite H.
    destruct (i =? S n) eqn:iSn. 
    * rewrite Nat.eqb_eq in iSn.
      assert (i<=S n) by omega. apply leb_correct in H0. rewrite H0.
      rewrite iSn. assert (true = (n =? n)) by apply beq_nat_refl.
      rewrite <-H1. f_equal. f_equal. omega.
    * rewrite Nat.eqb_neq in iSn.
      assert (i > S n) by omega. apply leb_iff_conv in H0. rewrite H0.
      destruct i; auto.
      assert (n<>i) by omega. apply Nat.eqb_neq in H1. rewrite H1. auto.
}
all: f_equal; auto.
}{
clear c_switch_Si_i_shift_1.
revert i. induction c; intros i; try destruct p; simpl; f_equal; auto.
}{
clear h_switch_Si_i_shift_1.
revert i. induction h; intros i; simpl; f_equal; auto.
}
Qed.

 
Lemma v_switch_SSi_Si_i_shift_1 v i:
  (v_switch_vars (v_switch_vars (Sub.v_shift v 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.v_shift v 1 (S (S i))
with c_switch_SSi_Si_i_shift_1 c i:
  (c_switch_vars (c_switch_vars (Sub.c_shift c 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.c_shift c 1 (S (S i))
with h_switch_SSi_Si_i_shift_1 h i:
  (h_switch_vars (h_switch_vars (Sub.h_shift h 1 i) (S i) i) (S (S i)) (S i)) 
    =
  Sub.h_shift h 1 (S (S i)).
Proof.
{
clear v_switch_SSi_Si_i_shift_1.
revert i. induction v; intros i; simpl.
{
destruct v as (name, n). simpl.
destruct (i <=? n) eqn:cmp; simpl.
+ destruct (n+1=?S i) eqn:eqSnSi; simpl.
  - apply Nat.eqb_eq in eqSnSi.
    assert (n+1=S n) by omega. rewrite H in eqSnSi.
    assert (i=n) by omega. rewrite H0.
    assert (n <> S (S n)) by omega. apply Nat.eqb_neq in H1. rewrite H1.
    assert (n <> S n) by omega. apply Nat.eqb_neq in H2. rewrite H2.
    destruct n; auto.
    destruct n; auto.
    assert (n < S (S n)) by omega. apply leb_iff_conv in H3. rewrite H3. auto.
  - apply leb_complete in cmp.
    assert (n+1 <> i) by omega. apply Nat.eqb_neq in H. rewrite H. simpl.
    destruct (n+1=?S(S i)) eqn:eqSnSSi; simpl.
    * apply Nat.eqb_eq in eqSnSSi.
      assert (n+1= S n) by omega. rewrite H0 in eqSnSSi. injection eqSnSSi.
      intro eq. rewrite eq. rewrite eq in *.
      destruct i. auto.
      assert (S i > i) by omega. apply leb_iff_conv in H1. rewrite H1. auto.
    * rewrite eqSnSi. destruct n.
      ++ assert (i=0) by omega. rewrite H0 in *. simpl in *. discriminate.
      ++ destruct n.
        ** apply Nat.eqb_neq in eqSnSi.
           assert (i = 0) by omega. rewrite H0 in *. simpl in *. discriminate.
        ** apply Nat.eqb_neq in eqSnSi. apply Nat.eqb_neq in eqSnSSi.
           assert (i<=n) by omega. apply leb_correct in H0. rewrite H0. auto.
+ apply leb_iff_conv in cmp.
  assert (n <> i) by omega. apply Nat.eqb_neq in H as Hneq.
  assert (n <> S i) by omega. apply Nat.eqb_neq in H0 as HSneq.
  assert (n <> S (S i)) by omega. apply Nat.eqb_neq in H1 as HSSneq.
  rewrite Hneq, HSneq. simpl. rewrite HSneq, HSSneq. f_equal.
  destruct n; auto. destruct n; auto.
  assert (i > n) by omega. apply leb_iff_conv in H2. rewrite H2. auto.
}
all: f_equal; auto.
}{
clear c_switch_SSi_Si_i_shift_1.
revert i. induction c; intros i; try destruct p; simpl; f_equal; auto.
}{
clear h_switch_SSi_Si_i_shift_1.
revert i. induction h; intros i; simpl; f_equal; auto.
}
Qed.

Lemma c_switch10_shift_1_0 c :
  c_switch_vars (Sub.c_shift c 1 0) 1 0 = Sub.c_shift c 1 1.
Proof.
  rewrite <-(c_switchswitch (Sub.c_shift c 1 1) 1 0).
  rewrite (c_switch_Si_i_shift_1 c 0). auto.
Qed.


Lemma v_negshift_1_switch_Si_i v i:
  v_no_var v i ->
  Sub.v_negshift (v_switch_vars v (S i) i) 1 (S i) 
    = Sub.v_negshift v 1 i
with c_negshift_1_switch_Si_i c i:
  c_no_var c i ->
  Sub.c_negshift (c_switch_vars c (S i) i) 1 (S i) 
    = Sub.c_negshift c 1 i
with h_negshift_1_switch_Si_i h i:
  h_no_var h i ->
  Sub.h_negshift (h_switch_vars h (S i) i) 1 (S i) 
    = Sub.h_negshift h 1 i.
Proof.
{
specialize (v_negshift_1_switch_Si_i v 0).
clear v_negshift_1_switch_Si_i.
revert i. induction v; intros i no_var; simpl.
{
destruct v as (name, n). simpl.
destruct n; simpl.
+ destruct i; auto.
+ destruct (i <=? S n) eqn:cmp; simpl.
  - apply leb_complete in cmp. simpl in no_var.
    assert (n-0=n) as nzero by omega. rewrite nzero.
    destruct (n=?i) eqn:ni.
    * simpl. apply Nat.eqb_eq in ni. rewrite ni.
      destruct i; auto. assert (S i > i) by omega. apply leb_iff_conv in H.
      rewrite H. reflexivity.
    * destruct i. { simpl. rewrite nzero. reflexivity. }
      assert (n<>i) by omega. apply Nat.eqb_neq in H. rewrite H.
      simpl. destruct n.
      ** assert (i=0) by omega. rewrite H0 in no_var. destruct no_var. auto.
      ** apply Nat.eqb_neq in ni.
         assert (i <= n) by omega. apply leb_correct in H0. rewrite H0. f_equal.
  - simpl in no_var. apply leb_iff_conv in cmp.
    assert (n<>i) by omega. apply Nat.eqb_neq in H. rewrite H.
    destruct i. omega.
    assert (n<>i) by omega. apply Nat.eqb_neq in H0. rewrite H0.
    simpl. destruct n; auto.
    apply Nat.eqb_neq in H. assert (n<i) by omega. apply leb_iff_conv in H1.
    rewrite H1. reflexivity.
}
all: f_equal; auto; try destruct no_var; auto.
}{
clear c_negshift_1_switch_Si_i.
revert i. induction c; intros i no_var; simpl in no_var; try destruct no_var;
try destruct p; simpl; f_equal; auto; try destruct no_var; auto;
try destruct H0; auto.
}{
clear h_negshift_1_switch_Si_i.
revert i. induction h; intros i no_var; simpl; simpl in no_var; auto.
f_equal; destruct no_var; auto.
}
Qed.


Lemma c_negshift_1_0_switch10 c :
  c_no_var c 1 ->
  Sub.c_negshift (c_switch_vars c 1 0) 1 0 = Sub.c_negshift c 1 1.
Proof.
  intro novar.
  rewrite <-(c_negshift_1_switch_Si_i).
  rewrite c_switchswitch. reflexivity.
  apply c_no_var_switch_i_j. assumption.
Qed.

(* Switch lemmas *)
Fixpoint v_switch_typesafe
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (v:val) (A:vtype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj) 
  {struct v} :
  has_vtype Γ v A ->
  has_vtype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (v_switch_vars v i j) A

with c_switch_typesafe 
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (c:comp) (C:ctype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj)
  {struct c}:
  has_ctype Γ c C -> 
  has_ctype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (c_switch_vars c i j) C

with h_switch_typesafe
  (Γ:ctx) i (Ai:vtype) j (Aj:vtype) (h:hcases) (Σ:sig) (D:ctype)
  (p_i : get_vtype_i Γ i = Some Ai) (p_j : get_vtype_i Γ j = Some Aj)
  {struct h}:
  has_htype Γ h Σ D ->
  has_htype (ctx_switch_vars Γ i j Ai Aj p_i p_j) (h_switch_vars h i j) Σ D.
Proof.
{
clear v_switch_typesafe.
revert Γ i j Ai Aj A p_i p_j; induction v; intros Γ i j Ai Aj A p_i p_j orig.
all: inv orig; try inv H; simpl.
{ (* relevant case *)
  destruct v as (name, num).
  destruct (num =? i) eqn:cmpi; simpl.
  + apply TypeVar. simpl.
    simpl in *. apply Nat.eqb_eq in cmpi.
    rewrite cmpi in H1. rewrite <-H1. apply eq_sym.
    apply switch_ij_get_j.
  + destruct (num =? j) eqn:cmpj.
    * simpl in *. apply Nat.eqb_eq in cmpj.
      rewrite cmpj in H1. apply TypeVar. rewrite <-H1. apply eq_sym.
      apply switch_ij_get_i.
    * rewrite (gets_same Γ (name,num) num) in H1. apply TypeVar.
      rewrite <-H1. apply eq_sym. apply switch_ij_get_k.
      - apply Nat.eqb_neq in cmpi. auto.
      - apply Nat.eqb_neq in cmpj. auto.
      - simpl. apply eq_sym. apply beq_nat_refl.
}
+ apply TypeUnit.
+ apply TypeInt.
+ apply TypeInl. auto.
+ apply TypeInr. auto.
+ apply TypePair; auto.
+ apply TypeFun. auto.
  apply (extend_get_proof _ A0) in p_i as pp_i.
  apply (extend_get_proof _ A0) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ A0 i j Ai Aj p_i p_j pp_i pp_j).
  auto.
+ apply TypeHandler; auto.
  apply (extend_get_proof _ A0) in p_i as pp_i.
  apply (extend_get_proof _ A0) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ A0 i j Ai Aj p_i p_j pp_i pp_j).
  auto.
+ apply TypeVAnnot. auto.
}{
clear c_switch_typesafe.
revert Γ i j Ai Aj C p_i p_j; induction c;
intros Γ i j Ai Aj C p_i p_j orig; inv orig; try inv H.
+ apply TypeRet. auto.
+ eapply TypeΠMatch.
  - apply v_switch_typesafe. exact H4.
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ B) in pp_i.
    apply (extend_get_proof _ B) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply IHc. assumption.
+ eapply TypeΣMatch. 
  - apply v_switch_typesafe; exact H6.
  - apply (extend_get_proof _ A) in p_i as pp_i;
    apply (extend_get_proof _ A) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ A i j Ai Aj p_i p_j pp_i pp_j).
    apply IHc1. assumption.
  - apply (extend_get_proof _ B) in p_i as pp_i;
    apply (extend_get_proof _ B) in p_j as pp_j.
    rewrite (ctx_switch_extend1 Γ B i j Ai Aj p_i p_j pp_i pp_j).
    apply IHc2. assumption.
+ eapply TypeApp.
  - apply v_switch_typesafe. exact H2.
  - apply v_switch_typesafe. assumption.
+ eapply TypeOp. exact H5. auto.
  apply (extend_get_proof _ B_op) in p_i as pp_i.
  apply (extend_get_proof _ B_op) in p_j as pp_j.
  rewrite (ctx_switch_extend1 Γ B_op i j Ai Aj p_i p_j pp_i pp_j).
  apply IHc. assumption.
+ apply TypeLetRec.
  - apply (extend_get_proof _ A) in p_i as pp_i.
    apply (extend_get_proof _ A) in p_j as pp_j.
    apply (extend_get_proof _ (TyFun A C0)) in pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in pp_j.
    assert (i+1+1=i+2) by omega. rewrite H in pp_i.
    assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
    rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
    apply IHc1. assumption.
  - apply (extend_get_proof _ (TyFun A C0)) in p_i as pp_i.
    apply (extend_get_proof _ (TyFun A C0)) in p_j as pp_j.
    rewrite (ctx_switch_extend1 _ _ _ _ _ _  p_i p_j pp_i pp_j).
    apply IHc2. assumption.
+ eapply TypeHandle.
  - apply v_switch_typesafe. exact H2.
  - apply IHc. assumption.
+ apply TypeCAnnot. apply IHc. assumption.
}{
clear h_switch_typesafe.
revert Γ i j Ai Aj Σ D p_i p_j; induction h;
intros Γ i j Ai Aj Σ D p_i p_j orig; inv orig; try inv H; simpl.
apply TypeCasesØ.
apply TypeCasesU.
+ apply find_op_None_switch. assumption.
+ apply IHh. assumption.
+ apply (extend_get_proof _ (TyFun B_op D)) in p_i as pp_i.
  apply (extend_get_proof _ (TyFun B_op D)) in p_j as pp_j.
  apply (extend_get_proof _ A_op) in pp_i.
  apply (extend_get_proof _ A_op) in pp_j.
  assert (i+1+1=i+2) by omega. rewrite H in pp_i.
  assert (j+1+1=j+2) by omega. rewrite H0 in pp_j.
  rewrite (ctx_switch_extend2 _ _ _ _ _ _ _ p_i p_j pp_i pp_j).
  apply c_switch_typesafe. assumption.
}
Qed.

(* Switch lemmas *)
Fixpoint v_switch10_typesafe
  (Γ:ctx) (A1:vtype) (A0:vtype) (v:val) (A:vtype)
  {struct v} :
  has_vtype (CtxU (CtxU Γ A1) A0) v A ->
  has_vtype (CtxU (CtxU Γ A0) A1) (v_switch_vars v 1 0) A

with c_switch10_typesafe 
  (Γ:ctx) (A1:vtype) (A0:vtype) (c:comp) (C:ctype)
  {struct c}:
  has_ctype (CtxU (CtxU Γ A1) A0) c C -> 
  has_ctype (CtxU (CtxU Γ A0) A1) (c_switch_vars c 1 0) C

with h_switch10_typesafe
  (Γ:ctx) (A1:vtype) (A0:vtype) (h:hcases) (Σ:sig) (D:ctype)
  {struct h}:
  has_htype (CtxU (CtxU Γ A1) A0) h Σ D ->
  has_htype (CtxU (CtxU Γ A0) A1) (h_switch_vars h 1 0) Σ D.
Proof.
all: intro orig; remember (CtxU (CtxU Γ A1) A0) as Γ'.
all: assert (get_vtype_i Γ' 1 = Some A1) as p_1.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ' 0 = Some A0) as p_0.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (ctx_switch_vars Γ' 1 0 A1 A0 p_1 p_0 = CtxU (CtxU Γ A0) A1).
all: try (unfold ctx_switch_vars; rewrite HeqΓ'; simpl; f_equal).
all: rewrite <-H.
+ apply v_switch_typesafe. assumption.
+ apply c_switch_typesafe. assumption.
+ apply h_switch_typesafe. assumption.
Qed.

(* Switch lemmas *)
Fixpoint v_switch210_typesafe
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (v:val) (A:vtype)
  {struct v} :
  has_vtype (CtxU (CtxU (CtxU Γ A2) A1) A0) v A ->
  has_vtype (CtxU (CtxU (CtxU Γ A0) A2) A1) (v_switch210_vars v) A

with c_switch210_typesafe 
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (c:comp) (C:ctype)
  {struct c}:
  has_ctype (CtxU (CtxU (CtxU Γ A2) A1) A0) c C -> 
  has_ctype (CtxU (CtxU (CtxU Γ A0) A2) A1) (c_switch210_vars c) C

with h_switch210_typesafe
  (Γ:ctx) (A2 : vtype) (A1:vtype) (A0:vtype) (h:hcases) (Σ:sig) (D:ctype)
  {struct h}:
  has_htype (CtxU (CtxU (CtxU Γ A2) A1) A0) h Σ D ->
  has_htype (CtxU (CtxU (CtxU Γ A0) A2) A1) (h_switch210_vars h) Σ D.
Proof.
all: intro orig; remember (CtxU (CtxU (CtxU Γ A2) A1) A0) as Γ'.
all: remember (CtxU (CtxU (CtxU Γ A2) A0) A1) as Γ''.
all: remember (CtxU (CtxU (CtxU Γ A0) A2) A1) as Γ'''.
all: assert (get_vtype_i Γ' 0 = Some A0) as p_0.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ' 1 = Some A1) as p_1.
all: try (rewrite HeqΓ'; simpl; f_equal).
all: assert (get_vtype_i Γ'' 1 = Some A0) as p'_0.
all: try (rewrite HeqΓ''; simpl; f_equal).
all: assert (get_vtype_i Γ'' 2 = Some A2) as p'_2.
all: try (rewrite HeqΓ''; simpl; f_equal).
all: assert (ctx_switch_vars Γ' 1 0 A1 A0 p_1 p_0 = Γ'').
all: try (unfold ctx_switch_vars; rewrite HeqΓ'; rewrite HeqΓ''; simpl; f_equal).
all: assert (ctx_switch_vars Γ'' 2 1 A2 A0 p'_2 p'_0 = Γ''').
all: try (unfold ctx_switch_vars; rewrite HeqΓ''; rewrite HeqΓ'''; simpl; f_equal).
all: rewrite <-H0.
+ apply v_switch_typesafe. rewrite <-H.
  apply v_switch_typesafe. assumption.
+ apply c_switch_typesafe. rewrite <-H.
  apply c_switch_typesafe. assumption.
+ apply h_switch_typesafe. rewrite <-H.
  apply h_switch_typesafe. assumption.
Qed. 



Lemma v_shift_0 cut v : Sub.v_shift v 0 cut = v
with c_shift_0 cut c : Sub.c_shift c 0 cut = c
with h_shift_0 cut h : Sub.h_shift h 0 cut = h.
Proof.
{
clear v_shift_0.
revert cut. induction v; intros cut;
simpl; try (specialize (IHv cut)); try rewrite IHv; try reflexivity.
+ destruct v. simpl. destruct (cut <=? v0); try reflexivity.
  assert (v0 + 0 = v0) by omega.
  rewrite H; reflexivity.
+ rewrite IHv1, IHv2. reflexivity.
+ rewrite c_shift_0. reflexivity.
+ f_equal; try apply c_shift_0 || apply h_shift_0.
}{
clear c_shift_0.
revert cut. induction c; intros cut; simpl;
try destruct p; f_equal;
try apply v_shift_0 || apply IHc || apply IHc1 || apply IHc2.
}{
clear h_shift_0.
revert cut. induction h; intros cut; simpl; f_equal.
reflexivity. apply IHh. apply c_shift_0.
}
Qed.


Lemma v_negshift_0 (cut:nat) (v:val) :
  Sub.v_negshift v 0 cut = v
with c_negshift_0 (cut:nat) (c:comp) :
  Sub.c_negshift c 0 cut = c
with h_negshift_0 (cut:nat) (h:hcases) :
  Sub.h_negshift h 0 cut = h.
Proof.
{
clear v_negshift_0.
revert cut. induction v; intros cut; simpl; f_equal; auto.
unfold Sub.id_down. destruct v. destruct (cut<=?v0).
+ assert (v0 - 0 = v0) by omega. rewrite H. reflexivity.
+ reflexivity.
}{
clear c_negshift_0.
revert cut. induction c; intros cut; simpl; try destruct p; f_equal;
try apply v_negshift_0 || apply IHc || apply IHc1 || apply IHc2.
}{
clear h_negshift_0.
revert cut. induction h; intros cut; simpl; f_equal. 
reflexivity. apply IHh. apply c_negshift_0.
}
Qed.


Lemma v_negshift_shift (n:nat) (m:nat) (cut:nat) (v:val) :
  (m <= n) ->
  Sub.v_negshift (Sub.v_shift v n cut) m cut = (Sub.v_shift v (n - m) cut)

with c_negshift_shift (n:nat) (m:nat) (cut:nat) (c:comp) :
  (m <= n) ->
  Sub.c_negshift (Sub.c_shift c n cut) m cut = (Sub.c_shift c (n - m) cut)

with h_negshift_shift (n:nat) (m:nat) (cut:nat) (h:hcases) :
  (m <= n) ->  
  Sub.h_negshift (Sub.h_shift h n cut) m cut = (Sub.h_shift h (n - m) cut).
Proof.
{
clear v_negshift_shift.  
revert cut. induction v; intros cut m_le_n; simpl; f_equal.
{ (* The only relevant case. *)
  destruct v as (name, db_i). simpl.
  induction (cut <=? db_i) eqn:cmp; simpl.
  - apply (leb_complete _ _) in cmp.
    assert (cut <= db_i + 1) by omega.
    assert (cut <= db_i + n) by omega.
    apply (leb_correct _ _) in H0. rewrite H0.
    f_equal. omega.
  - rewrite cmp. reflexivity. }
all : try reflexivity || apply IHv || apply IHv1 || apply IHv2.
all : try apply c_negshift_shift || apply h_negshift_shift; assumption.
}{
clear c_negshift_shift.
revert cut. induction c; intros cut m_le_n; try destruct p; simpl; f_equal;
try apply v_negshift_shift || apply IHc || apply IHc1 || apply IHc2; assumption.
}{
clear h_negshift_shift.
revert cut. induction h; intros cut m_le_n; simpl; f_equal.
reflexivity. apply IHh. assumption. apply c_negshift_shift. assumption.
}
Qed.