Require Import ssreflect.
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

(* Trying my best to not write C style module_funcname *)
Module Par.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (***************** Beta ***********************)
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
  | Var i : R (VarTm i) (VarTm i)
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
  | Var i : R (VarTm i) (VarTm i)
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

  Derive Dependent Inversion inv with (forall n (a b : Tm n), R a b) Sort Prop.

  Lemma refl n (a : Tm n) : R a a.
  Proof.
    induction a; hauto lq:on ctrs:R.
  Qed.

  Lemma AppAbs' n a0 a1 (b0 b1 t : Tm n) :
    t = subst_Tm (scons b1 VarTm) a1 ->
    R a0 a1 ->
    R b0 b1 ->
    R (App (Abs a0) b0) t.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : qauto ctrs:R.
  Qed.

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
  | Var i : R (VarTm i) (VarTm i)
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

  Lemma refl n (a : Tm n) : EPar.R a a.
  Proof.
    induction a; hauto lq:on ctrs:EPar.R.
  Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a0 a1 ha iha m ξ /=.
    move /(_ _ ξ) /AppEta : iha.
    by asimpl.

    all : qauto ctrs:R.
  Qed.
End EPar.


Local Ltac com_helper :=
  split; [hauto lq:on ctrs:RPar.R use: RPar.refl, RPar.renaming
         |hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming].

Lemma commutativity n (a b0 b1 : Tm n) : EPar.R a b0 -> RPar.R a b1 -> exists c, RPar.R b0 c /\ EPar.R b1 c.
Proof.
  move => h. move : b1.
  elim : n a b0 / h.
  - move => n a b0 ha iha b1 hb.
    move : iha (hb) => /[apply].
    move => [c [ih0 ih1]].
    exists (Abs (App (ren_Tm shift c) (VarTm var_zero))); com_helper.
  - move => n a b0 hb0 ihb0 b1 /[dup] hb1 {}/ihb0.
    move => [c [ih0 ih1]].
    exists (Pair c c); com_helper.
  - hauto lq:on ctrs:RPar.R, EPar.R inv:RPar.R.
  - hauto lq:on ctrs:RPar.R, EPar.R inv:RPar.R.
  - move => n a0 a1 b0 b1 ha iha hb ihb b2.
    elim /RPar.inv => //=.


Admitted.

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
