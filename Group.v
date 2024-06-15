Require Import Coq.Classes.SetoidClass.

Definition Associative {A: Set}
  (R: A -> A -> Prop)
  (op: A -> A -> A)
  : Prop :=
  forall (x y z : A),
    R (op (op x y) z) (op x (op y z)).

Definition Commutative {A: Set}
  (R: A -> A -> Prop)
  (op: A -> A -> A)
  : Prop :=
  forall (x y : A), R (op x y) (op y x).

Class Group (A: Set) (op: A -> A -> A) : Type := {
  #[global]
  g_setoid :: Setoid A;
  id : A;
  inv : A -> A;
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
Admitted. (* TODO *)


