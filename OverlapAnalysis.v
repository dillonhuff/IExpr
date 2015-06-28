Require Import IExpr.

Inductive irectangle : Set :=
| IRectangle : iexpr -> iexpr -> iexpr -> iexpr -> irectangle.

