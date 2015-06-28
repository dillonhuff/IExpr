Require Import IExpr.
Require Import IExprOverlap.
Require Import ZArith.

Open Scope Z_scope.

Definition sub := iexpr -> option iexpr.

Definition nullSub (i : iexpr) : sub :=
  fun x : iexpr => None.

Fixpoint sameIVar (i j : iexpr) : bool :=
  match i with
    | IVar v1 => 
      match j with
        | IVar v2 =>
          match Z.compare v1 v2 with
            | Eq => true
            | _ => false
          end
        | _ => false
      end
    | _ => false
  end.

Fixpoint addSub (s : sub) (target : iexpr) (result : iexpr) : sub :=
  fun x : iexpr => match sameIVar x target with
                     | true => Some result
                     | false => s x
                   end.