Require Import ZArith Psatz Classes.SetoidClass.
Open Scope Z_scope.

Class Group (G: Set) (op: G -> G -> G) : Type := {
  #[global]
  g_setoid :: Setoid G;
  id : G;
  inv : G -> G;
  #[global]
  op_proper :: Proper (equiv ==> equiv ==> equiv) op;
  #[global]
  inv_proper :: Proper (equiv ==> equiv) inv;
  assoc : forall x y z, op (op x y) z == op x (op y z);
  ident_l : forall x, op id x == x;
  ident_r : forall x, op x id == x;
  inverses_l : forall x, op (inv x) x == id;
  inverses_r : forall x, op x (inv x) == id;
}.

Ltac intros_refl x H :=
  match goal with
  | _ : Group _ _ |- _ =>
      assert (H: x == x); [reflexivity | ..]
  | _ => fail "must be done within group context"
  end.

Ltac op_left x H :=
  match goal with
  | _ : Group _ _ |- _ =>
      let Hrefl := fresh in
      intros_refl x Hrefl;
      apply (op_proper x x Hrefl) in H;
      clear Hrefl
  | _ => fail "must be done within group context"
  end.

Ltac op_right x H :=
  match goal with
  | _ : Group _ _ |- _ =>
      let Hrefl := fresh in
      intros_refl x Hrefl;
      apply (op_proper _ _ H) in Hrefl;
      clear H;
      rename Hrefl into H
  | _ => fail "must be done within group context"
  end.

Lemma unique_id_l
  : forall G op (Grp: Group G op) id',
    (forall x, op id' x == x) ->
    id' == id.
Proof.
  intros * Hid'.
  intros_refl id H.
  rewrite <- Hid' in H at 1.
  rewrite ident_r in H.
  exact H.
Qed.

Lemma unique_id_r
  : forall G op (Grp: Group G op) id',
    (forall x, op x id' == x) ->
    id' == id.
Proof.
  intros * Hid'.
  intros_refl id H.
  rewrite <- Hid' in H at 1.
  rewrite ident_l in H.
  exact H.
Qed.

Lemma unique_inv_l
  : forall G op (Grp: Group G op) x inv',
    op inv' x == id ->
    inv' == inv x.
Proof.
  intros * H.
  op_right (inv x) H.
  rewrite assoc in H.
  rewrite inverses_r, ident_l, ident_r in H.
  exact H.
Qed.

Lemma unique_inv_r
  : forall G op (Grp: Group G op) x inv',
    op x inv' == id ->
    inv' == inv x.
Proof.
  intros * H.
  op_left (inv x) H.
  rewrite <- assoc in H.
  rewrite inverses_l, ident_r, ident_l in H.
  exact H.
Qed.

Lemma cancel_l
  : forall G op (Grp: Group G op) a x y,
    op a x == op a y ->
    x == y.
Proof.
  intros * Haxy.
  op_left (inv a) Haxy.
  rewrite <- 2 assoc in Haxy.
  rewrite inverses_l in Haxy.
  rewrite 2 ident_l in Haxy.
  exact Haxy.
Qed.

Lemma cancel_r
  : forall G op (Grp: Group G op) a x y,
  op x a == op y a ->
  x == y.
  intros * Haxy.
  op_right (inv a) Haxy.
  rewrite -> 2 assoc in Haxy.
  rewrite inverses_r in Haxy.
  rewrite 2 ident_r in Haxy.
  exact Haxy.
Qed.

Lemma inv_id
  : forall G op (Grp: Group G op),
    inv id == id.
Proof.
  intros *.
  intros_refl id H.
  rewrite <- (inverses_l id) in H at 1.
  rewrite ident_r in H.
  apply H.
Qed.

Lemma inv_inv
  : forall G op (Grp: Group G op) x,
    inv (inv x) == x.
Proof.
  intros *.
  intros_refl id H.
  rewrite <- (inverses_l x) in H at 2.
  rewrite <- (inverses_r (inv x)) in H at 1.
  apply cancel_l in H.
  exact H.
Qed.

Lemma inv_op
  : forall G op (Grp: Group G op) x y,
    inv (op x y) == op (inv y) (inv x).
Proof.
  intros *.
  intros_refl id H.
  rewrite <- (inverses_l (op x y)) in H at 1.
  rewrite <- (inverses_l y) in H.
  rewrite <- (ident_l y) in H at 4.
  rewrite <- (inverses_l x) in H.
  rewrite (assoc (inv x)) in H.
  rewrite <- (assoc (inv y)) in H.
  apply cancel_r in H.
  exact H.
Qed.

Fixpoint pow' {G: Set} {op: G -> G -> G} {Grp: Group G op}
  (a: G) (n: nat) :=
  match n with
  | O => id
  | S n' => op a (pow' a n')
  end.

Definition pow {G: Set} {op: G -> G -> G} {Grp: Group G op}
  (a: G) (n: Z) :=
  if n <? 0 then
    pow' (inv a) (Z.to_nat (-n))
  else
    pow' a (Z.to_nat n).

Declare Scope group_scope.
Notation "a ^ n" := (pow a n) : group_scope.
Notation "a ^^ n" := (pow' a n)
  (at level 30, right associativity)
  : group_scope.
Open Scope group_scope.

Lemma pow_pos_unfold
  : forall G op (Grp: Group G op) a n,
    n >= 0 ->
    a^n == pow' a (Z.to_nat n).
Proof.
  intros * Hpos.
  unfold pow.
  destruct (n <? 0) eqn:E; [lia | reflexivity].
Qed.

Lemma pow_neg_unfold
  : forall G op (Grp: Group G op) a n,
    n < 0 ->
    a^n == pow' (inv a) (Z.to_nat (-n)).
Proof.
  intros * Hneg.
  unfold pow.
  destruct (n <? 0) eqn:E; [reflexivity | lia].
Qed.

#[global]
Instance pow'_proper
  : forall G op (Grp: Group G op),
    Proper (equiv ==> eq ==> equiv) pow'.
Proof.
  intros * a a' Haa' n.
  induction n; intros; subst.
  - reflexivity.
  - simpl.
    apply op_proper; auto.
Qed.

#[global]
Instance pow_proper
  : forall G op (Grp: Group G op),
    Proper (equiv ==> Z.eq ==> equiv) pow.
Proof.
  intros * a a' Haa' n n' Hnn'.
  destruct (Z_lt_ge_dec n 0).
  - rewrite <- Hnn', 2 pow_neg_unfold, Haa'; auto.
    reflexivity.
  - rewrite <- Hnn', 2 pow_pos_unfold, Haa'; auto.
    reflexivity.
Qed.

Lemma pow_zero
  : forall G op (Grp: Group G op) a,
    a^0 == id.
Proof.
  intros *.
  unfold pow.
  reflexivity.
Qed.

Lemma pow_one
  : forall G op (Grp: Group G op) a,
    a^1 == a.
Proof.
  intros *.
  unfold pow.
  simpl.
  apply ident_r.
Qed.

Lemma pow_neg_one
  : forall G op (Grp: Group G op) a,
    a^(-1) == inv a.
Proof.
  intros *.
  unfold pow.
  simpl.
  apply ident_r.
Qed.

Lemma pow_neg
  : forall G op (Grp: Group G op) a n,
    a^(-n) == (inv a)^n.
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0); [|destruct n].
  - rewrite pow_neg_unfold with (n := n); auto.
    rewrite inv_inv.
    rewrite pow_pos_unfold; [reflexivity | lia].
  - simpl. apply pow_zero.
  - rewrite pow_neg_unfold; [|lia].
    rewrite Z.opp_involutive.
    reflexivity.
  - contradiction.
Qed.

Lemma pow'_swap
  : forall G op (Grp: Group G op) a n,
    op a (a^^n) == op (a^^n) a.
Proof.
  intros *.
  induction n.
  - simpl.
    rewrite ident_l, ident_r.
    reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- assoc.
    rewrite IHn.
    reflexivity.
Qed.

Lemma pow'_swap_inv
  : forall G op (Grp: Group G op) a n,
    op (inv a) (a^^n) == op (a^^n) (inv a).
Proof.
  intros *.
  induction n.
  - simpl.
    rewrite ident_l, ident_r.
    reflexivity.
  - simpl.
    rewrite assoc.
    rewrite <- IHn.
    rewrite <- 2 assoc.
    rewrite inverses_l, inverses_r.
    reflexivity.
Qed.

Lemma pow_swap
  : forall G op (Grp: Group G op) a n,
    op a (a^n) == op (a^n) a.
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0).
  - rewrite pow_neg_unfold; [|assumption].
    rewrite <- inv_inv with (x := a) at 1.
    rewrite <- inv_inv with (x := a) at 4.
    apply pow'_swap_inv.
  - rewrite pow_pos_unfold; [|assumption].
    apply pow'_swap.
Qed.

Lemma op_pow
  : forall G op (Grp: Group G op) a n,
    op a (a^n) == a^(Z.succ n).
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0);
    destruct (Z_lt_ge_dec (Z.succ n) 0).
  - rewrite pow_neg_unfold with (n := n); [|assumption].
    rewrite (Zsucc_pred (-n)).
    rewrite Z2Nat.inj_succ; [|lia].
    simpl.
    rewrite <- assoc, inverses_r, ident_l.
    rewrite <- Z.opp_succ.
    rewrite <- pow_neg_unfold; [|assumption].
    reflexivity.
  - assert (H: n = -1) by lia. rewrite H.
    simpl.
    rewrite pow_zero, pow_neg_one.
    apply inverses_r.
  - assert (H: False) by lia. contradiction.
  - rewrite pow_pos_unfold with (n := Z.succ n);
      [|assumption].
    rewrite Z2Nat.inj_succ; [|lia].
    simpl.
    rewrite pow_pos_unfold; [reflexivity|assumption].
Qed.

Lemma pow_op
  : forall G op (Grp: Group G op) a n,
    op (a^n) a == a^(Z.succ n).
Proof.
  intros *.
  rewrite <- pow_swap.
  apply op_pow.
Qed.

Lemma inv_op_pow
  : forall G op (Grp: Group G op) a n,
    op (inv a) (a^n) == a^(Z.pred n).
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0);
    destruct (Z_lt_ge_dec (Z.pred n) 0).
  - rewrite pow_neg_unfold with (n := Z.pred n);
      [|assumption].
    rewrite Z.opp_pred.
    rewrite Z2Nat.inj_succ; [|lia].
    simpl.
    rewrite <- pow_neg_unfold; [reflexivity|lia].
  - assert (H: False) by lia. contradiction.
  - assert (H: n = 0) by lia. subst.
    reflexivity.
  - rewrite pow_pos_unfold; [|assumption].
    destruct (Z.to_nat n) eqn:E.
    { assert (H: False) by lia. contradiction. }
    simpl.
    rewrite <- assoc, inverses_l, ident_l.
    assert (H: n0 = Z.to_nat (Z.pred n)) by lia.
    rewrite H.
    symmetry.
    apply pow_pos_unfold.
    auto.
Qed.

Lemma pow'_add
  : forall G op (Grp: Group G op) a n m,
    op (a^^n) (a^^m) == a^^(n+m).
Proof.
  intros *.
  induction n.
  - simpl.
    apply ident_l.
  - simpl.
    rewrite assoc.
    rewrite IHn.
    reflexivity.
Qed.

Lemma inv_op_pow'
  : forall G op (Grp: Group G op) a n,
    (n > 0)%nat ->
    op (inv a) (a^^n) == a^^(n - 1).
Proof.
  intros * Hn0.
  induction n; [|destruct n].
  - inversion Hn0.
  - simpl.
    rewrite ident_r.
    apply inverses_l.
  - simpl.
    rewrite <- assoc, inverses_l.
    apply ident_l.
Qed.

Lemma pow'_sub_pos
  : forall G op (Grp: Group G op) a n m,
    (n <= m)%nat ->
    op (inv a ^^n) (a^^m) == a^^(m-n).
Proof.
  intros * Hnm.
  induction n.
  - simpl.
    rewrite Nat.sub_0_r.
    apply ident_l.
  - simpl.
    rewrite assoc.
    rewrite IHn; [|lia].
    rewrite inv_op_pow' with (n := (m - n)%nat); [|lia].
    assert (H: (m - n - 1)%nat = (m - S n)%nat) by lia.
    rewrite H.
    reflexivity.
Qed.

Lemma pow'_sub_neg
  : forall G op (Grp: Group G op) a n m,
    (n >= m)%nat ->
    op (inv a ^^n) (a^^m) == inv a^^(n-m).
Proof.
  intros * Hnm.
  induction m.
  - simpl.
    rewrite Nat.sub_0_r.
    apply ident_r.
  - simpl.
    rewrite pow'_swap, <- assoc.
    rewrite IHm; [|lia].
    rewrite <- inv_inv with (x := a) at 2.
    rewrite <- pow'_swap_inv.
    rewrite inv_op_pow' with (n := (n - m)%nat); [|lia].
    assert (H: (n - m - 1)%nat = (n - S m)%nat) by lia.
    rewrite H.
    reflexivity.
Qed.

Lemma pow_add
  : forall G op (Grp: Group G op) a n m,
  op (a^n) (a^m) == a^(n+m).
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0); destruct (Z_lt_ge_dec m 0).
  - rewrite 3 pow_neg_unfold; [|lia..].
    rewrite Z.opp_add_distr.
    rewrite pow'_add.
    rewrite Z2Nat.inj_add; [reflexivity|lia..].
  - destruct (Z_lt_ge_dec m (-n)).
    + rewrite pow_neg_unfold with (n := n),
        pow_pos_unfold with (n := m),
        pow_neg_unfold with (n := n + m);
        [|lia..].
      rewrite pow'_sub_neg; [|lia].
      rewrite <- Z2Nat.inj_sub; [|lia].
      rewrite Z.opp_add_distr, Z.add_opp_r.
      reflexivity.
    + rewrite pow_neg_unfold with (n := n),
        pow_pos_unfold with (n := m),
        pow_pos_unfold with (n := n + m);
        [|lia..].
      rewrite pow'_sub_pos; [|lia].
      rewrite <- Z2Nat.inj_sub; [|lia].
      rewrite Z.sub_opp_r, Z.add_comm.
      reflexivity.
  - destruct (Z_lt_ge_dec n (-m)).
    + rewrite pow_pos_unfold with (n := n),
        pow_neg_unfold with (n := m),
        pow_neg_unfold with (n := n + m);
        [|lia..].
      rewrite <- inv_inv with (x := a) at 1.
      rewrite pow'_sub_pos; [|lia].
      rewrite <- Z2Nat.inj_sub; [|lia].
      rewrite Z.add_comm, Z.opp_add_distr, Z.add_opp_r.
      reflexivity.
    + rewrite pow_pos_unfold with (n := n),
        pow_neg_unfold with (n := m),
        pow_pos_unfold with (n := n + m);
        [|lia..].
      rewrite <- inv_inv with (x := a) at 1.
      rewrite pow'_sub_neg; [|lia].
      rewrite <- Z2Nat.inj_sub; [|lia].
      rewrite Z.sub_opp_r.
      rewrite inv_inv.
      reflexivity.
  - rewrite 3 pow_pos_unfold; [|lia..].
    rewrite Z2Nat.inj_add; [|lia..].
    apply pow'_add.
Qed.

Lemma pow_comm
  : forall G op (Grp: Group G op) a n m,
    op (a^n) (a^m) == op (a^m) (a^n).
Proof.
  intros *.
  rewrite pow_add.
  rewrite Z.add_comm.
  rewrite <- pow_add.
  reflexivity.
Qed.

Lemma pow'_inv
  : forall G op (Grp: Group G op) a n,
    (inv a)^^n == inv (a^^n).
Proof.
  intros *.
  induction n.
  - simpl.
    symmetry.
    apply inv_id.
  - simpl.
    rewrite inv_op.
    rewrite pow'_swap.
    rewrite IHn.
    reflexivity.
Qed.

Lemma pow_inv
  : forall G op (Grp: Group G op) a n,
    (inv a)^n == inv (a^n).
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0).
  - rewrite 2 pow_neg_unfold; [|lia..].
    apply pow'_inv.
  - rewrite 2 pow_pos_unfold; [|lia..].
    apply pow'_inv.
Qed.

Lemma pow'_pow'
  : forall G op (Grp: Group G op) a n m,
    (a^^n)^^m == a^^(n*m).
Proof.
  intros *.
  induction m.
  - rewrite Nat.mul_0_r.
    reflexivity.
  - rewrite Nat.mul_succ_r.
    rewrite Nat.add_comm.
    simpl.
    rewrite <- pow'_add.
    rewrite IHm.
    reflexivity.
Qed.

Lemma pow_pow
  : forall G op (Grp: Group G op) a n m,
    (a^n)^m == a^(n*m).
Proof.
  intros *.
  destruct (Z_lt_ge_dec n 0); destruct (Z_lt_ge_dec m 0).
  - rewrite pow_neg_unfold with (n := n),
      pow_neg_unfold with (n := m),
      pow_pos_unfold with (n := n * m);
      [|lia..].
      Fail rewrite inv_pow.
      Fail rewrite pow'_pow'.
Admitted.


Lemma inv_pos
  : forall G op (Grp: Group G op) a n,
    inv (a^n) == a^(-n).
Proof.
  intros *.
Admitted.


Inductive Subgroup {G: Set} {op: G -> G -> G}
  (P: G -> Prop) (Grp: Group G op)
  : Prop :=
  subgroup {
    sg_closed : forall x y, P x -> P y -> P (op x y);
    sg_id : P id;
    sg_inv : forall x, P x -> P (inv x);
  }.

Notation "H <= G" := (Subgroup H G) : type_scope.

Definition TrivialSubgroup {G op} {Grp: Group G op}
  (x: G) := x == id.

Definition ImproperSubgroup {G op} {Grp: Group G op}
  (x: G) := True.

Lemma trivial_subgroup
  : forall G op (Grp: Group G op),
    TrivialSubgroup <= Grp.
Proof.
  intros *.
  split; unfold TrivialSubgroup in *.
  - intros * Sx Sy.
    rewrite Sx, Sy, ident_l.
    reflexivity.
  - reflexivity.
  - intros * Sx.
    rewrite Sx.
    apply inv_id.
Qed.

Lemma improper_subgroup
  : forall G op (Grp: Group G op),
    ImproperSubgroup <= Grp.
Proof.
  intros *.
  split; unfold ImproperSubgroup in *; intros; auto.
Qed.

Definition CyclicSubgroup {G op} {Grp: Group G op}
  (a: G) (x: G) :=
  exists n, x == a^n.

Lemma cyclic_subgroup
  : forall G op (Grp: Group G op) a,
    CyclicSubgroup a <= Grp.
Proof.
  intros *.
  split; unfold CyclicSubgroup in *; intros *.
  - intros [n Hx] [m Hy].
    exists (n + m).
    rewrite Hx, Hy.
    apply pow_add.
  - exists 0.
    symmetry.
    apply pow_zero.
  - intros [n Hx].
    exists (-n).
    rewrite Hx.
    (*
    destruct Hx; [right | left]; rewrite H;
      rewrite pow_inv.
    + reflexivity.
    + apply inv_inv.
Qed.
     *)
Admitted.



Inductive Cyclic {G op} (Grp: Group G op)
  : Prop := cyclic (a: G)
    : (forall x, exists n, x == a^n) -> Cyclic Grp.

