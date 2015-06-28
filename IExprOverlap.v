Require Import IExpr.
Require Import ZArith.

Inductive irectangle : Set :=
| IRectangle : iexpr -> iexpr -> iexpr -> iexpr -> irectangle.

Fixpoint foldIRectangleConstants (r : irectangle) : irectangle :=
  match r with
    | IRectangle rs re cs ce =>
      IRectangle (tryFoldConstantsRec rs)
                 (tryFoldConstantsRec re)
                 (tryFoldConstantsRec cs)
                 (tryFoldConstantsRec ce)
  end.

Fixpoint isConstIRectangle (r : irectangle) : Prop :=
  match foldIRectangleConstants r with
    | IRectangle (IConst _) (IConst _) (IConst _) (IConst _) => True
    | _ => False
  end.

Open Scope Z_scope.

Check (exists i : Z, i + 2 = 3).

Check ex.

Check ex_intro.

Check (exists k : Z, k + 2 = 4).

Fixpoint mkExists (b : iexpr) (P : Prop) : Prop :=
  exists b : iexpr, P.

