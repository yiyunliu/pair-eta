Require Import ssreflect.
From stdpp Require Import relations (rtc (..)).
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
    R a0 (Pair (Proj1 a1) (Proj2 a1))

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
    R a0 (Pair (Proj1 a1) (Proj2 a1))

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

  Derive Dependent Inversion inv with (forall n (a b : Tm n), R a b) Sort Prop.
End EPar.


Local Ltac com_helper :=
  split; [hauto lq:on ctrs:RPar.R use: RPar.refl, RPar.renaming
         |hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming].

Module RPars.

  Lemma AbsCong n (a b : Tm (S n)) :
    rtc RPar.R a b ->
    rtc RPar.R (Abs a) (Abs b).
  Proof. induction 1; hauto l:on ctrs:RPar.R, rtc. Qed.

  Lemma AppCong n (a0 a1 b : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (App a0 b) (App a1 b).
  Proof.
    move => h. move : b.
    elim : a0 a1 /h.
    - qauto ctrs:RPar.R, rtc.
    - move => x y z h0 h1 ih b.
      apply rtc_l with (y := App y b) => //.
      hauto lq:on ctrs:RPar.R use:RPar.refl.
  Qed.

  Lemma PairCong n (a0 a1 b0 b1 : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (Pair a0 b0) (Pair a1 b1).
  Proof.
    move => h. move : b0 b1.
    elim : a0 a1 /h.
    - move => x b0 b1 h.
      elim : b0 b1 /h.
      by auto using rtc_refl.
      move => x0 y z h0 h1 h2.
      apply : rtc_l; eauto.
      by eauto using RPar.refl, RPar.PairCong.
    - move => x y z h0 h1 ih b0 b1 h.
      apply : rtc_l; eauto.
      by eauto using RPar.refl, RPar.PairCong.
  Qed.


  Lemma renaming n (a0 a1 : Tm n) m (ξ : fin n -> fin m) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (ren_Tm ξ a0) (ren_Tm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using RPar.renaming, rtc_l.
  Qed.

  Lemma Abs_inv n (a : Tm (S n)) b :
    rtc RPar.R (Abs a) b -> exists a', b = Abs a' /\ rtc RPar.R a a'.
  Proof.
    move E : (Abs a) => b0 h. move : a E.
    elim : b0 b / h.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc inv:RPar.R, rtc.
  Qed.
End RPars.

Lemma Abs_EPar n a (b : Tm n) :
  EPar.R (Abs a) b ->
  (exists d, EPar.R a d /\
     rtc RPar.R (App (ren_Tm shift b) (VarTm var_zero)) d) /\
         (exists d,
         EPar.R a d /\
         rtc RPar.R (Proj1 b) (Abs (Proj1 d)) /\
         rtc RPar.R (Proj2 b) (Abs (Proj2 d))).
Proof.
  move E : (Abs a) => u h.
  move : a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha b ?. subst.
    specialize iha with (1 := eq_refl).
    move : iha => [[d [ih0 ih1]] _].
    split; exists d.
    + split => //.
      apply : rtc_l.
      apply RPar.AppAbs; eauto => //=.
      apply RPar.refl.
      by apply RPar.refl.
      move :ih1; substify; by asimpl.
    + repeat split => //.
      * apply : rtc_l. apply : RPar.Proj1Abs. apply RPar.refl.
        apply : RPars.AbsCong.

(*   - move => n a0 a1 ha iha a ? c. subst. *)
(*     specialize iha with (1 := eq_refl) (c := c). *)
(*     move : iha => [d [ih0 ih1]]. *)
(*     exists (Pair (Proj1 d) (Proj2 d)). split => //. *)
(*     + move { ih1}. *)
(*       hauto lq:on ctrs:EPar.R. *)
(*     + apply : rtc_l. *)
(*       apply RPar.AppPair. *)
(*       admit. *)
(*       admit. *)
(*       apply RPar.refl. *)
(*       admit. *)
(*   - admit. *)
Admitted.


Lemma commutativity n (a b0 b1 : Tm n) :
  EPar.R a b0 -> RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ EPar.R b1 c.
Proof.
  move => h. move : b1.
  elim : n a b0 / h.
  - move => n a b0 ha iha b1 hb.
    move : iha (hb) => /[apply].
    move => [c [ih0 ih1]].
    exists (Abs (App (ren_Tm shift c) (VarTm var_zero))).
    split.
    + sfirstorder use:RPars_AbsCong, RPars_AppCong, RPars_renaming.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - move => n a b0 hb0 ihb0 b1 /[dup] hb1 {}/ihb0.
    move => [c [ih0 ih1]].
    exists (Pair (Proj1 c) (Proj2 c)). split.
    + apply RPars_PairCong; admit.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - hauto l:on ctrs:rtc inv:RPar.R.
  - move => n a0 a1 h ih b1.
    elim /RPar.inv => //= _.
    move => a2 a3 ? [*]. subst.
    hauto lq:on ctrs:rtc, RPar.R, EPar.R use:RPars_AbsCong.
  - move => n a0 a1 b0 b1 ha iha hb ihb b2.
    elim /RPar.inv => //= _.
    + move =>  a2 a3 b3 b4 h0 h1 [*]. subst.
      have {}/iha : RPar.R (Abs a2) (Abs a3) by hauto lq:on ctrs:RPar.R.
      move => [c [ih0 ih1]].

      elim /EPar.inv : ha => //= _.
      * move => a0 a4 h *. subst.
        move /ihb : h1 {ihb}.
        move => [c [hb1 hb4]].
        have {}/iha : RPar.R (Abs a2) (Abs a3) by hauto lq:on ctrs:RPar.R.
        move => [c0 [hc0 hc1]].
        eexists.
        split.
        ** apply RPar.AppAbs; eauto.
           eauto using RPar.refl.
        ** simpl.


      admit.
    + move => a2 a3 b3 b4 c0 c1 h0 h1 h2 [*]. subst.
      admit.
    + hauto lq:on ctrs:RPar.R, EPar.R.
  - hauto lq:on ctrs:RPar.R, EPar.R inv:RPar.R.
  - move => n a b0 h0 ih0 b1.
    elim /RPar.inv => //= _.
    + move => a0 a1 h [*]. subst.
      admit.
    + move => a0 ? a1 h1 [*]. subst.
      admit.
    + hauto lq:on ctrs:RPar.R, EPar.R.
  - move => n a b0 h0 ih0 b1.
    elim /RPar.inv => //= _.
    + move => a0 a1 ha [*]. subst.
      admit.
    + move => a0 a1 b2 h [*]. subst.
      admit.
    + hauto lq:on ctrs:RPar.R, EPar.R.
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
