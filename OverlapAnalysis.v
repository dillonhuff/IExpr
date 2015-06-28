Require Import IExpr.
Require Import IExprOverlap.
Require Import IntOverlap.

Fixpoint toIntRectangle (r : irectangle) : option rectangle :=
  match foldIRectangleConstants r with
    | IRectangle (IConst rs) (IConst re) (IConst cs) (IConst ce) =>
      Some (mkRectangle (mkRange rs re) (mkRange cs ce))
    | _ => None
  end.

Fixpoint conservativeOverlap (r1 r2 : irectangle) : Prop :=
  match toIntRectangle r1 with
    | Some ir1 =>
      match toIntRectangle r2 with
        | Some ir2 => ~(noOverlap ir1 ir2)
        | None => False
      end
    | None => False
  end.

(*Theorem conservativeOverlap_correct_for_constant_rectangles :
  forall r1 r2 : irectangle,
    isConstIRectangle r1 = true ->
    isConstIRectangle r2 = true ->
    conservativeOverlap r1 r2 = noOverlap r1 r2.*)

