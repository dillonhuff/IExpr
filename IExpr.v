Require Import Bool ZArith.

Open Scope Z_scope.

Ltac app :=
  match goal with
    | [H0 : ?a, H1 : ?a -> ?b |- _] => apply H1 in H0
  end.

Inductive iexpr : Set :=
| IConst : Z -> iexpr
| IVar : Z -> iexpr
| IAdd : iexpr -> iexpr -> iexpr
| IMul : iexpr -> iexpr -> iexpr.

Fixpoint isConst (i : iexpr) : bool :=
  match i with
    | IConst _ => true
    | _ => false
  end.

Fixpoint constVal (i : iexpr) : option Z :=
  match i with
    | IConst c => Some c
    | _ => None
  end.

Fixpoint isSome (A : Type) (v : option A) : bool :=
  match v with
    | Some _ => true
    | None => false
  end.

Theorem isSome_imp_v :
  forall (A : Type) (v : option A),
    isSome A v = true ->
    exists b : A, v = Some b.
Proof.
  intros; destruct v; [eapply ex_intro; reflexivity | discriminate].
Qed.

Fixpoint optionApply (A B : Type) (f : A -> A -> B) (l r : option A) : option B :=
  match l with
    | Some a =>
      match r with
        | Some b => Some (f a b)
        | _ => None
      end
    | None => None
  end.

Theorem optionApply_on_somes :
  forall (A B : Type) (f : A -> A -> B) (l r : option A),
    isSome A l = true ->
    isSome A r = true ->
    exists (a b : A), optionApply A B f l r = Some (f a b).
Proof.
  intros; pose proof isSome_imp_v as H1;

  apply H1 in H0;
  inversion H0 as [m0 Hm0];
  rewrite -> Hm0;

  apply H1 in H;
  inversion H as [m Hm];
  rewrite -> Hm;

  simpl;
  repeat (eapply ex_intro); reflexivity.
Qed.

Fixpoint constValRec (i : iexpr) : option Z :=
  match i with
    | IConst a => Some a
    | IVar _ => None
    | IAdd l r =>
      let lc := constValRec l in
      let rc := constValRec r in
      optionApply Z Z Z.add lc rc
    | IMul l r =>
      let lc := constValRec l in
      let rc := constValRec r in
      optionApply Z Z Z.mul lc rc
  end.

Theorem constValRec_on_const_gives_const :
  forall i : iexpr, isConst i = true -> constValRec i = constVal i.
Proof.
  intros; destruct i; solve [trivial | simpl; discriminate].
Qed.

Fixpoint allConstants (i : iexpr) : bool :=
  match i with
    | IConst _ => true
    | IVar _ => false
    | IAdd l r => andb (allConstants l) (allConstants r)
    | IMul l r => andb (allConstants l) (allConstants r)
  end.

Theorem allConstants_add_consts :
  forall i j : iexpr,
    allConstants (IAdd i j) = true ->
    (allConstants i = true /\ allConstants j = true).
Proof.
  intros; simpl allConstants in H;
  apply andb_true_iff in H; apply H.
Qed.

Theorem allConstants_mul_consts :
  forall i j : iexpr,
    allConstants (IMul i j) = true ->
    (allConstants i = true /\ allConstants j = true).
Proof.
  intros; simpl allConstants in H;
  apply andb_true_iff in H; apply H.
Qed.  

Ltac startInduction n :=
  intros; induction n; trivial.

Theorem constValRec_works_on_allConstants :
  forall i : iexpr, allConstants i = true -> isSome Z (constValRec i) = true.
Proof.
  let start := startInduction i;
               apply allConstants_add_consts in H;
               inversion H as [Hl Hr];
               pose proof optionApply_on_somes as A in
  let finish := do 3 app; trivial;
                inversion Hl as [a Ha]; inversion Ha as [b Hb];
                simpl; rewrite -> Hb; trivial in
  let s1 := specialize (A Z Z Z.add (constValRec i1) (constValRec i2)) in
  let s2 := specialize (A Z Z Z.mul (constValRec i1) (constValRec i2)) in
  start; [s1; finish | s2; finish].
Qed.

Theorem constValRec_on_sum_of_consts :
  forall i j : iexpr,
    (exists a : Z, constValRec (IAdd i j) = Some a) ->
    ((exists b : Z, constValRec i = Some b) /\
     (exists c : Z, constValRec j = Some c)).
Proof.
  intros; inversion H as [m Hm]; simpl constValRec in Hm;
  destruct (constValRec i); destruct (constValRec j);
  split; first [discriminate | eapply ex_intro; trivial].
Qed.

Theorem constValRec_on_prod_of_consts :
  forall i j : iexpr,
    (exists a : Z, constValRec (IMul i j) = Some a) ->
    ((exists b : Z, constValRec i = Some b) /\
     (exists c : Z, constValRec j = Some c)).
Proof.
  intros; inversion H as [m Hm]; simpl constValRec in Hm;
  destruct (constValRec i); destruct (constValRec j);
  split; first [discriminate | eapply ex_intro; trivial].
Qed.

Theorem constValRec_works_imp_allConstants :
  forall i : iexpr, isSome Z (constValRec i) = true -> allConstants i = true.
Proof.
  let t := specialize (S i1 i2);
           apply isSome_imp_v in H;
           apply S in H; inversion H as [Hl Hr];
           inversion Hl as [m Hm]; inversion Hr as [n Hn];
           simpl allConstants;
           rewrite -> Hm in IHi1; simpl isSome in IHi1;
           rewrite -> Hn in IHi2; simpl isSome in IHi2;
           intuition in
   let p1 := pose proof constValRec_on_sum_of_consts as S in
   let p2 := pose proof constValRec_on_prod_of_consts as S in
   startInduction i; [p1; t | p2; t].
Qed.

Theorem constValRec_works_iff_allConstants :
  forall i : iexpr, isSome Z (constValRec i) = true <-> allConstants i = true.
Proof.
  intros; unfold iff;
  split; [apply constValRec_works_imp_allConstants |
          apply constValRec_works_on_allConstants].
Qed.

