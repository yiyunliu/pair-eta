Require Import ssreflect.
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

(* Trying my best to not write C style module_funcname *)
Module Par.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (***************** Beta ***********************)
  | Var i : R (VarTm i) (VarTm i)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (App (Abs a0) b0)  (subst_Tm (scons b1 VarTm) a1)
  | AppPair a0 a1 b0 b1 c0 c1:
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    R (App (Pair a0 b0) c0) (Pair (App a1 c1) (App b1 c1))
  | Proj1Abs a0 a1 :
    R a0 a1 ->
    R (Proj1 (Abs a0)) (Abs (Proj1 a0))
  | Proj1Pair a0 a1 b :
    R a0 a1 ->
    R (Proj1 (Pair a0 b)) a1
  | Proj2Abs a0 a1 :
    R a0 a1 ->
    R (Proj2 (Abs a0)) (Abs (Proj2 a0))
  | Proj2Pair a0 a1 b :
    R a0 a1 ->
    R (Proj2 (Pair a0 b)) a1

  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (Abs (App (ren_Tm shift a1) (VarTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (Pair a1 a1)

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (Abs a0) (Abs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (App a0 b0) (App a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (Pair a0 b0) (Pair a1 b1)
  | Proj1Cong a0 a1 :
    R a0 a1 ->
    R (Proj1 a0) (Proj1 a1)
  | Proj2Cong a0 a1 :
    R a0 a1 ->
    R (Proj2 a0) (Proj2 a1).
End Par.

(***************** Beta rules only ***********************)
Module RPar.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (***************** Beta ***********************)
  | Var i : R (VarTm i) (VarTm i)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (App (Abs a0) b0)  (subst_Tm (scons b1 VarTm) a1)
  | AppPair a0 a1 b0 b1 c0 c1:
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    R (App (Pair a0 b0) c0) (Pair (App a1 c1) (App b1 c1))
  | Proj1Abs a0 a1 :
    R a0 a1 ->
    R (Proj1 (Abs a0)) (Abs (Proj1 a0))
  | Proj1Pair a0 a1 b :
    R a0 a1 ->
    R (Proj1 (Pair a0 b)) a1
  | Proj2Abs a0 a1 :
    R a0 a1 ->
    R (Proj2 (Abs a0)) (Abs (Proj2 a0))
  | Proj2Pair a0 a1 b :
    R a0 a1 ->
    R (Proj2 (Pair a0 b)) a1

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (Abs a0) (Abs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (App a0 b0) (App a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (Pair a0 b0) (Pair a1 b1)
  | Proj1Cong a0 a1 :
    R a0 a1 ->
    R (Proj1 a0) (Proj1 a1)
  | Proj2Cong a0 a1 :
    R a0 a1 ->
    R (Proj2 a0) (Proj2 a1).
End RPar.

Module EPar.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (Abs (App (ren_Tm shift a1) (VarTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (Pair a1 a1)

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (Abs a0) (Abs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (App a0 b0) (App a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (Pair a0 b0) (Pair a1 b1)
  | Proj1Cong a0 a1 :
    R a0 a1 ->
    R (Proj1 a0) (Proj1 a1)
  | Proj2Cong a0 a1 :
    R a0 a1 ->
    R (Proj2 a0) (Proj2 a1).
End EPar.

Lemma EPar_Par n (a b : Tm n) : EPar.R a b -> Par.R a b.
Proof. induction 1; hauto lq:on ctrs:Par.R. Qed.

Lemma RPar_Par n (a b : Tm n) : RPar.R a b -> Par.R a b.
Proof. induction 1; hauto lq:on ctrs:Par.R. Qed.

Lemma merge n (t a u : Tm n) :
  EPar.R t a ->
  RPar.R a u ->
  Par.R t u.
Proof.
  move => h. move : u.
  elim:t a/h.
  - move => n0 a0 a1 ha iha u hu.
    apply iha.
    inversion hu; subst.


  - hauto lq:on inv:RPar.R.
  - move => a0 a1 b0 b1 ha iha hb ihb u.
    inversion 1; subst.
    + inversion ha.

best use:EPar_Par, RPar_Par.

  best ctrs:Par.R inv:EPar.R,RPar.R use:EPar_Par, RPar_Par.
