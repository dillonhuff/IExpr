Require Import ZArith.
Require Import Sets.Ensembles.
Require Import Omega.
Require Import Bool.

Open Scope Z_scope.

Definition mkRange (s e: Z) :=
  fun p : Z => s <= p /\ p <= e.

Definition range := Z -> Prop.

Definition mkRectangle (horizontalRange verticalRange : range) :=
  fun pnt : prod Z Z => In Z horizontalRange (fst pnt) /\ In Z verticalRange (snd pnt).

Definition rectangle := prod Z Z -> Prop.

Definition noOverlap (r1 r2 : rectangle) :=
  Intersection (prod Z Z) r1 r2 = Empty_set (prod Z Z).

Theorem trivial_1 :
  In Z (mkRange 0 20) 13.
Proof.
  unfold In; unfold mkRange; omega.
Qed.
