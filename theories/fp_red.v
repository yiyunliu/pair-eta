Require Import ssreflect.
From stdpp Require Import relations (rtc (..), rtc_once).
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
  | ProjAbs p a0 a1 :
    R a0 a1 ->
    R (Proj p (Abs a0)) (Abs (Proj p a1))
  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (Proj p (Pair a0 b0)) (if p is PL then a1 else b1)

  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (Abs (App (ren_Tm shift a1) (VarTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (Pair (Proj PL a1) (Proj PR a1))

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
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (Proj p a0) (Proj p a1).
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
  | ProjAbs p a0 a1 :
    R a0 a1 ->
    R (Proj p (Abs a0)) (Abs (Proj p a1))
  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (Proj p (Pair a0 b0)) (if p is PL then a1 else b1)


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
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (Proj p a0) (Proj p a1).

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

  Lemma ProjPair' n p (a0 a1 b0 b1 : Tm n) t :
    t = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (Proj p (Pair a0 b0)) t.
  Proof.  move => > ->. apply ProjPair. Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : qauto ctrs:R use:ProjPair'.
  Qed.

  Lemma morphing_ren n m p (ρ0 ρ1 : fin n -> Tm m) (ξ : fin m -> fin p) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((funcomp (ren_Tm ξ) ρ0) i) ((funcomp (ren_Tm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

  Lemma morphing_ext n m (ρ0 ρ1 : fin n -> Tm m) a b  :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)).
  Proof. hauto q:on inv:option. Qed.

  Lemma morphing_up n m (ρ0 ρ1 : fin n -> Tm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (up_Tm_Tm ρ0 i) (up_Tm_Tm ρ1 i)).
  Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_Tm_Tm. Qed.

  Lemma morphing n m (a b : Tm n) (ρ0 ρ1 : fin n -> Tm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_Tm ρ0 a) (subst_Tm ρ1 b).
  Proof.
    move => + h. move : m ρ0 ρ1.
    elim : n a b /h.
    - move => *.
      apply : AppAbs'; eauto using morphing_up.
      by asimpl.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:ProjPair' use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
  Qed.

  Lemma substing n m (a b : Tm n) (ρ : fin n -> Tm m) :
    R a b ->
    R (subst_Tm ρ a) (subst_Tm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.
End RPar.

Module EPar.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (Abs (App (ren_Tm shift a1) (VarTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (Pair (Proj PL a1) (Proj PR a1))

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
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (Proj p a0) (Proj p a1).

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

  Lemma AppEta' n (a0 a1 b : Tm n) :
    b = (Abs (App (ren_Tm shift a1) (VarTm var_zero))) ->
    R a0 a1 ->
    R a0 b.
  Proof. move => ->; apply AppEta. Qed.

  Lemma morphing n m (a b : Tm n) (ρ0 ρ1 : fin n -> Tm m) :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R (subst_Tm ρ0 a) (subst_Tm ρ1 b).
  Proof.
    move => h. move : m ρ0 ρ1. elim : n a b / h => n.
    - move => a0 a1 ha iha m ρ0 ρ1 hρ /=.
      apply : AppEta'; eauto. by asimpl.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
    - hauto l:on ctrs:R use:renaming inv:option.
    - hauto q:on ctrs:R.
    - hauto q:on ctrs:R.
    - hauto q:on ctrs:R.
  Qed.

  Lemma substing n a0 a1 (b0 b1 : Tm n) :
    R a0 a1 ->
    R b0 b1 ->
    R (subst_Tm (scons b0 VarTm) a0) (subst_Tm (scons b1 VarTm) a1).
  Proof.
    move => h0 h1. apply morphing => //.
    hauto lq:on ctrs:R inv:option.
  Qed.

End EPar.


Local Ltac com_helper :=
  split; [hauto lq:on ctrs:RPar.R use: RPar.refl, RPar.renaming
         |hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming].

Module RPars.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RPar.R use:RPar.refl.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : Tm (S n)) :
    rtc RPar.R a b ->
    rtc RPar.R (Abs a) (Abs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (App a0 b0) (App a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (Pair a0 b0) (Pair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (Proj p a0) (Proj p a1).
  Proof. solve_s. Qed.

  Lemma renaming n (a0 a1 : Tm n) m (ξ : fin n -> fin m) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (ren_Tm ξ a0) (ren_Tm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using RPar.renaming, rtc_l.
  Qed.

  Lemma weakening n (a0 a1 : Tm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (ren_Tm shift a0) (ren_Tm shift a1).
  Proof. apply renaming. Qed.

  Lemma Abs_inv n (a : Tm (S n)) b :
    rtc RPar.R (Abs a) b -> exists a', b = Abs a' /\ rtc RPar.R a a'.
  Proof.
    move E : (Abs a) => b0 h. move : a E.
    elim : b0 b / h.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc inv:RPar.R, rtc.
  Qed.

  Lemma morphing n m (a b : Tm n) (ρ : fin n -> Tm m) :
    rtc RPar.R a b ->
    rtc RPar.R (subst_Tm ρ a) (subst_Tm ρ b).
  Proof. induction 1; qauto l:on ctrs:rtc use:RPar.substing. Qed.

  Lemma substing n (a b : Tm (S n)) c :
    rtc RPar.R a b ->
    rtc RPar.R (subst_Tm (scons c VarTm) a) (subst_Tm (scons c VarTm) b).
  Proof. hauto lq:on use:morphing inv:option. Qed.

End RPars.

Lemma Abs_EPar n a (b : Tm n) :
  EPar.R (Abs a) b ->
  (exists d, EPar.R a d /\
     rtc RPar.R (App (ren_Tm shift b) (VarTm var_zero)) d) /\
         (exists d,
         EPar.R a d /\ forall p,
         rtc RPar.R (Proj p b) (Abs (Proj p d))).
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
    + split => // p.
      apply : rtc_l.
      apply : RPar.ProjAbs.
      by apply RPar.refl.
      eauto using RPars.ProjCong, RPars.AbsCong.
  - move => n ? a1 ha iha a0 ?. subst. specialize iha with (1 := eq_refl).
    move : iha => [_ [d [ih0 ih1]]].
    split.
    + exists (Pair (Proj PL d) (Proj PR d)).
      split; first by apply EPar.PairEta.
      apply : rtc_l.
      apply RPar.AppPair; eauto using RPar.refl.
      suff h : forall p, rtc RPar.R (App (Proj p (ren_Tm shift a1)) (VarTm var_zero)) (Proj p d) by
          sfirstorder use:RPars.PairCong.
      move => p. move /(_ p) /RPars.weakening in ih1.
      apply relations.rtc_transitive with (y := App (ren_Tm shift (Abs (Proj p d))) (VarTm var_zero)).
      by eauto using RPars.AppCong, rtc_refl.
      apply relations.rtc_once => /=.
      apply : RPar.AppAbs'; eauto using RPar.refl.
      by asimpl.
    + exists d. repeat split => //. move => p.
      apply : rtc_l; eauto.
      hauto q:on use:RPar.ProjPair', RPar.refl.
  - move => n a0 a1 ha _ ? [*]. subst.
    split.
    + exists a1. split => //.
      apply rtc_once. apply : RPar.AppAbs'; eauto using RPar.refl. by asimpl.
    + exists a1. split => // p.
      apply rtc_once. apply : RPar.ProjAbs; eauto using RPar.refl.
Qed.

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
    + hauto lq:on ctrs:rtc use:RPars.AbsCong, RPars.AppCong, RPars.renaming.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - move => n a b0 hb0 ihb0 b1 /[dup] hb1 {}/ihb0.
    move => [c [ih0 ih1]].
    exists (Pair (Proj PL c) (Proj PR c)). split.
    + apply RPars.PairCong;
      by apply RPars.ProjCong.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - hauto l:on ctrs:rtc inv:RPar.R.
  - move => n a0 a1 h ih b1.
    elim /RPar.inv => //= _.
    move => a2 a3 ? [*]. subst.
    hauto lq:on ctrs:rtc, RPar.R, EPar.R use:RPars.AbsCong.
  - move => n a0 a1 b0 b1 ha iha hb ihb b2.
    elim /RPar.inv => //= _.
    + move =>  a2 a3 b3 b4 h0 h1 [*]. subst.
      move /(_ _ ltac:(by eauto)) : ihb => [b [ihb0 ihb1]].
      have {}/iha : RPar.R (Abs a2) (Abs a3) by hauto lq:on ctrs:RPar.R.
      move => [c [ih0 /Abs_EPar [[d [ih1 ih2]] _]]].
      exists (subst_Tm (scons b VarTm) d).
      split.
      (* By substitution *)
      * move /RPars.substing  : ih2.
        move /(_ b).
        asimpl.
        eauto using relations.rtc_transitive, RPars.AppCong.
      (* By EPar morphing *)
      * by apply EPar.substing.
    + move => a2 a3 b3 b4 c0 c1 h0 h1 h2 [*]. subst.
      admit.
    + hauto lq:on ctrs:EPar.R use:RPars.AppCong.
  - hauto lq:on ctrs:EPar.R inv:RPar.R use:RPars.PairCong.
  - move => n p a b0 h0 ih0 b1.
    elim /RPar.inv => //= _.
    + move => ? a0 a1 h [*]. subst.
      move /(_ _ ltac:(by eauto using RPar.AbsCong)) : ih0 => [c [ih0 ih1]].
      move /Abs_EPar : ih1 => [_ [d [ih1 ih2]]].
      exists (Abs (Proj p d)).
      qauto l:on ctrs:EPar.R use:RPars.ProjCong, @relations.rtc_transitive.
    + move => p0 a0 a1 b2 b3 h1 h2 [*]. subst.
      move /(_ _ ltac:(by eauto using RPar.PairCong)) : ih0 => [c [ih0 ih1]].
      admit.
    + hauto lq:on ctrs:EPar.R use:RPars.ProjCong.
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
