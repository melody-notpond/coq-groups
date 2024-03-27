Definition Associative {A: Set}
  (op: A -> A -> A)
  : Prop :=
  forall (x y z : A), op (op x y) z = op x (op y z).

Definition IdentityL {A: Set}
  (op: A -> A -> A)
  (id: A)
  : Prop :=
  forall (x: A), op id x = x.

Definition IdentityR {A: Set}
  (op: A -> A -> A)
  (id: A)
  : Prop :=
  forall (x: A), op x id = x.

Definition Identity {A: Set}
  (op: A -> A -> A)
  (id: A)
  : Prop :=
  IdentityL op id /\ IdentityR op id.

Definition InversesL {A: Set}
  (op: A -> A -> A)
  (id: A)
  (inv: A -> A)
  : Prop :=
  forall (x: A), op (inv x) x = id.

Definition InversesR {A: Set}
  (op: A -> A -> A)
  (id: A)
  (inv: A -> A)
  : Prop :=
  forall (x: A), op x (inv x) = id.

Definition Inverses {A: Set}
  (op: A -> A -> A)
  (id: A)
  (inv: A -> A)
  : Prop :=
  InversesL op id inv /\ InversesR op id inv.

Definition Commutative {A: Set}
  (op: A -> A -> A)
  : Prop :=
  forall (x y : A), op x y = op y x.

Definition IsGroup {A: Set}
  (op: A -> A -> A)
  (id: A)
  (inv: A -> A)
  : Prop :=
  Associative op /\
  Identity op id /\
  Inverses op id inv.

Lemma apply_op_l
  : forall (A: Set) (op: A -> A -> A) (x y : A),
    x = y -> forall z, op z x = op z y.
Proof.
  intros A op x y Heq z.
  rewrite Heq.
  reflexivity.
Qed.

Lemma apply_op_r
  : forall (A: Set) (op: A -> A -> A) (x y : A),
    x = y -> forall z, op x z = op y z.
Proof.
  intros A op x y Heq z.
  rewrite Heq.
  reflexivity.
Qed.

Lemma unique_id
  : forall (A: Set) (op: A -> A -> A) (id: A) (id': A),
    Identity op id ->
    Identity op id' ->
    id = id'.
Proof.
  unfold Identity.
  unfold IdentityL.
  unfold IdentityR.
  intros A op id id' Hid Hid'.
  destruct Hid as [Hid _].
  destruct Hid' as [_ Hid'].
  specialize Hid with (x := id').
  specialize Hid' with (x := id).
  rewrite Hid' in Hid.
  apply Hid.
Qed.

Lemma unique_inv
  : forall (A: Set) (op: A -> A -> A) (id: A)
      (inv: A -> A) (inv': A -> A),
    Associative op ->
    Identity op id ->
    Inverses op id inv ->
    Inverses op id inv' ->
    forall (x: A), inv x = inv' x.
Proof.
  unfold Associative.
  unfold Identity.
  unfold IdentityL.
  unfold IdentityR.
  unfold Inverses.
  unfold InversesL.
  unfold InversesR.
  intros A op id inv inv'.
  intros Hassoc Hident Hinv Hinv' x.
  destruct Hident as [Hident_l Hident_r].
  destruct Hinv as [Hinv _].
  destruct Hinv' as [_ Hinv'].
  (* a'aa'' = a' = a'' *)
  specialize Hinv with (x := x) as H.
  apply apply_op_r with (op := op) (z := inv' x) in H.
  rewrite Hident_l in H.
  rewrite Hassoc in H.
  rewrite Hinv' in H.
  rewrite Hident_r in H.
  apply H.
Qed.

Ltac unfold_isgroup HGroup
  Hassoc Hident_l Hident_r Hinv_l Hinv_r :=
  unfold IsGroup in HGroup;
  unfold Associative in HGroup;
  unfold Identity in HGroup;
  unfold IdentityL in HGroup;
  unfold IdentityR in HGroup;
  unfold Inverses in HGroup;
  unfold InversesL in HGroup;
  unfold InversesR in HGroup;
  destruct HGroup as
    [Hassoc [
    [Hident_l Hident_r]
    [Hinv_l Hinv_r]]].

Lemma cancel_l
  : forall (A: Set) (op: A -> A -> A) (id: A) (inv: A -> A),
    IsGroup op id inv ->
    forall (a x y : A), op a x = op a y -> x = y.
Proof.
  intros A op id inv HGroup a x y H.
  unfold_isgroup HGroup
    Hassoc Hident_l Hident_r Hinv_l Hinv_r.
  apply apply_op_l with (op := op) (z := inv a) in H.
  repeat rewrite <- Hassoc in H.
  repeat rewrite Hinv_l in H.
  repeat rewrite Hident_l in H.
  apply H.
Qed.

Lemma cancel_r
  : forall (A: Set) (op: A -> A -> A) (id: A) (inv: A -> A),
    IsGroup op id inv ->
    forall (a x y : A), op x a = op y a -> x = y.
Proof.
  intros A op id inv HGroup a x y H.
  unfold_isgroup HGroup
    Hassoc Hident_l Hident_r Hinv_l Hinv_r.
  apply apply_op_r with (op := op) (z := inv a) in H.
  repeat rewrite Hassoc in H.
  repeat rewrite Hinv_r in H.
  repeat rewrite Hident_r in H.
  apply H.
Qed.

Lemma inv_inv
  : forall (A: Set) (op: A -> A -> A) (id: A) (inv: A -> A),
    IsGroup op id inv ->
    forall (x: A), inv (inv x) = x.
Proof.
  intros A op id inv HGroup x.
  unfold_isgroup HGroup
    Hassoc Hident_l Hident_r Hinv_l Hinv_r.
  specialize Hinv_r with (x := inv x) as H.
  apply apply_op_l with (op := op) (z := x) in H.
  rewrite <- Hassoc in H.
  rewrite Hinv_r in H.
  rewrite Hident_l in H.
  rewrite Hident_r in H.
  apply H.
Qed.

(*
Require Import Nat.

Inductive cyclic : nat -> Set :=
  | CZ : forall {n: nat}, cyclic (S n)
  | CS : forall {n: nat}, cyclic n -> cyclic (S n).

Check CZ : cyclic 1.
Check CS CZ : cyclic 2.
Check CS (CS CZ) : cyclic 3.
Check CZ : cyclic 3.
Fail Check CS CZ : cyclic 1.
Check @CZ.
Check @CS.


Fixpoint cyclic_op
  {n: nat}
  (x y : cyclic n)
  : cyclic n :=
  match x, y with
  | CZ, y => y
  | CS x', y => CS (cyclic_op x' y)

Definition cyclic_inv
  (n: nat)
  (x: nat)
  : nat :=
  modulo (n - (modulo x n)) n.

Lemma cyclic_group
  : forall (n: nat), IsGroup (cyclic_op n)

Fixpoint repeat {A: Set}
  (op: A -> A -> A)
  (id: A)
  (n: nat)
  (x: A)
  : A :=
  match n with
  | O => id
  | S n' => op x (repeat op id n' x)
  end.

Definition Closure {A: Set}
  (op: A -> A -> A)
  (mem: A -> Prop)
  : Prop :=
  forall (x y: A), mem x -> mem y -> mem (op x y).

Definition HasInverses {A: Set}
  (inv: A -> A)
  (mem: A -> Prop)
  : Prop :=
  forall (x: A), mem x -> mem (inv x).

Definition IsSubgroup {A: Set}
  (op: A -> A -> A)
  (id: A)
  (inv: A -> A)
  (mem: A -> Prop)
  : Prop :=
  Closure op mem /\ mem id /\ HasInverses inv mem.

 *)

