Require Import ZArith.
Require Import Sets.Ensembles.
Require Import Omega.

Open Scope Z_scope.

Definition mkRange (s e: Z) :=
  fun p : Z => s <= p /\ p <= e.

Definition range := Z -> Prop.

Definition mkRectangle (horizontalRange verticalRange : range) :=
  fun p : Z => In Z horizontalRange p /\ In Z verticalRange p.

Definition rectangle := Z -> Prop.

Definition noOverlap (r1 r2 : rectangle) :=
  Intersection Z r1 r2 = Empty_set Z.

Theorem trivial_1 :
  In Z (mkRange 0 20) 13.
Proof.
  unfold In; unfold mkRange; omega.
Qed.

