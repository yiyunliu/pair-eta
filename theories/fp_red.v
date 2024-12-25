From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
Require Import ssreflect.
Require Import FunInd.
Require Import Arith.Wf_nat.
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
From Equations Require Import Equations.

Ltac2 spec_refl () :=
  List.iter
    (fun a => match a with
           | (i, _, _) =>
               let h := Control.hyp i in
               try (specialize $h with (1 := eq_refl))
           end)  (Control.hyps ()).

Ltac spec_refl := ltac2:(spec_refl ()).


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
    R (Proj p a0) (Proj p a1)
  | PiCong A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (Pi A0 B0) (Pi A1 B1)
  | BotCong :
    R Bot Bot.

  Lemma refl n (a : Tm n) : R a a.
    elim : n /a; hauto ctrs:R.
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

  Lemma AppEta' n (a0 a1 b : Tm n) :
    b = (Abs (App (ren_Tm shift a1) (VarTm var_zero))) ->
    R a0 a1 ->
    R a0 b.
  Proof. move => ->; apply AppEta. Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : match goal with
          | [ |- context[var_zero]] => move => *; apply : AppEta'; eauto; by asimpl
          | _ => qauto ctrs:R use:ProjPair'
          end.
  Qed.


  Lemma morphing n m (a b : Tm n) (ρ0 ρ1 : fin n -> Tm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_Tm ρ0 a) (subst_Tm ρ1 b).
  Proof.
    move => + h. move : m ρ0 ρ1. elim : n a b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ0 ρ1 hρ /=.
      eapply AppAbs' with (a1 := subst_Tm (up_Tm_Tm ρ1) a1); eauto.
      by asimpl.
      hauto l:on use:renaming inv:option.
    - hauto lq:on rew:off ctrs:R.
    - hauto l:on inv:option use:renaming ctrs:R.
    - hauto lq:on use:ProjPair'.
    - move => n a0 a1 ha iha m ρ0 ρ1 hρ /=.
      apply : AppEta'; eauto. by asimpl.
    - hauto lq:on ctrs:R.
    - sfirstorder.
    - hauto l:on inv:option ctrs:R use:renaming.
    - hauto q:on ctrs:R.
    - qauto l:on ctrs:R.
    - qauto l:on ctrs:R.
    - hauto l:on inv:option ctrs:R use:renaming.
    - sfirstorder.
  Qed.

  Lemma substing n m (a b : Tm n) (ρ : fin n -> Tm m) :
    R a b -> R (subst_Tm ρ a) (subst_Tm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

  Lemma antirenaming n m (a : Tm n) (b : Tm m) (ξ : fin n -> fin m) :
    R (ren_Tm ξ a) b -> exists b0, R a b0 /\ ren_Tm ξ b0 = b.
  Proof.
    move E : (ren_Tm ξ a) => u h.
    move : n ξ a E. elim : m u b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//=.
      move => c c0 [+ ?]. subst.
      case : c => //=.
      move => c [?]. subst.
      spec_refl.
      move : iha => [c1][ih0]?. subst.
      move : ihb => [c2][ih1]?. subst.
      eexists. split.
      apply AppAbs; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc m ξ []//=.
      move => []//= t t0 t1 [*]. subst.
      spec_refl.
      move : iha => [? [*]].
      move : ihb => [? [*]].
      move : ihc => [? [*]].
      eexists. split.
      apply AppPair; hauto. subst.
      by asimpl.
    - move => n p a0 a1 ha iha m ξ []//= p0 []//= t [*]. subst.
      spec_refl. move : iha => [b0 [? ?]]. subst.
      eexists. split. apply ProjAbs; eauto. by asimpl.
    - move => n p a0 a1 b0 b1 ha iha hb ihb m ξ []//= p0 []//= t t0[*].
      subst. spec_refl.
      move : iha => [b0 [? ?]].
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by eauto using ProjPair.
      hauto q:on.
    - move => n a0 a1 ha iha m ξ a ?. subst.
      spec_refl. move : iha => [a0 [? ?]]. subst.
      eexists. split. apply AppEta; eauto.
      by asimpl.
    - move => n a0 a1 ha iha m ξ a ?. subst.
      spec_refl. move : iha => [b0 [? ?]]. subst.
      eexists. split. apply PairEta; eauto.
      by asimpl.
    - move => n i m ξ []//=.
      hauto l:on.
    - move => n a0 a1 ha iha m ξ []//= t [*]. subst.
      spec_refl.
      move  :iha => [b0 [? ?]]. subst.
      eexists. split. by apply AbsCong; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//= t t0 [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply AppCong; eauto.
      done.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//= t t0[*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply PairCong; eauto.
      by asimpl.
    - move => n p a0 a1 ha iha m ξ []//= p0 t [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      eexists. split. by apply ProjCong; eauto.
      by asimpl.
    - move => n A0 A1 B0 B1 ha iha hB ihB m ξ []//= t t0 [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]].
      move : ihB => [c0 [? ?]]. subst.
      eexists. split. by apply PiCong; eauto.
      by asimpl.
    - hauto lq:on rew:off inv:Tm.
  Qed.

End Par.

Module Pars.
  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    rtc Par.R a b -> rtc Par.R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    induction 1; hauto lq:on ctrs:rtc use:Par.renaming.
  Qed.

  Lemma substing n m (a b : Tm n) (ρ : fin n -> Tm m) :
    rtc Par.R a b ->
    rtc Par.R (subst_Tm ρ a) (subst_Tm ρ b).
    induction 1; hauto l:on ctrs:rtc use:Par.substing.
  Qed.

  Lemma antirenaming n m (a : Tm n) (b : Tm m) (ξ : fin n -> fin m) :
    rtc Par.R (ren_Tm ξ a) b -> exists b0, rtc Par.R a b0 /\ ren_Tm ξ b0 = b.
  Proof.
    move E  :(ren_Tm ξ a) => u h.
    move : a E.
    elim : u b /h.
    - sfirstorder.
    - move => a b c h0 h1 ih1 a0 ?. subst.
      move /Par.antirenaming : h0.
      move => [b0 [h2 ?]]. subst.
      hauto lq:on rew:off ctrs:rtc.
  Qed.
End Pars.

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
    R (Proj p a0) (Proj p a1)
  | PiCong A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (Pi A0 B0) (Pi A1 B1)
  | BotCong :
    R Bot Bot.

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
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
  Qed.

  Lemma substing n m (a b : Tm n) (ρ : fin n -> Tm m) :
    R a b ->
    R (subst_Tm ρ a) (subst_Tm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

  Lemma cong n (a b : Tm (S n)) c d :
    R a b ->
    R c d ->
    R (subst_Tm (scons c VarTm) a) (subst_Tm (scons d VarTm) b).
  Proof.
    move => h0 h1. apply morphing => //=.
    qauto l:on ctrs:R inv:option.
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
    R (Proj p a0) (Proj p a1)
  | PiCong A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (Pi A0 B0) (Pi A1 B1)
  | BotCong :
    R Bot Bot.

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
    - hauto l:on ctrs:R use:renaming inv:option.
    - hauto lq:on ctrs:R.
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


Module OExp.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a :
    R a (Abs (App (ren_Tm shift a) (VarTm var_zero)))
  | PairEta a :
    R a (Pair (Proj PL a) (Proj PR a)).

  Lemma merge n (t a b : Tm n) :
    rtc R a b ->
    EPar.R t a ->
    EPar.R t b.
  Proof.
    move => h. move : t. elim : a b /h.
    - eauto using EPar.refl.
    - hauto q:on ctrs:EPar.R inv:R.
  Qed.

  Lemma commutativity n (a b c : Tm n) :
    EPar.R a b -> R a c -> exists d, R b d /\ EPar.R c d.
  Proof.
    move => h.
    inversion 1; subst.
    - hauto q:on ctrs:EPar.R, R use:EPar.renaming, EPar.refl.
    - hauto lq:on ctrs:EPar.R, R.
  Qed.

  Lemma commutativity0 n (a b c : Tm n) :
    EPar.R a b -> rtc R a c -> exists d, rtc R b d /\ EPar.R c d.
  Proof.
    move => + h. move : b.
    elim : a c / h.
    - sfirstorder.
    - hauto lq:on rew:off ctrs:rtc use:commutativity.
  Qed.

End OExp.


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

  Lemma PiCong n (a0 a1 : Tm n) b0 b1 :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (Pi a0 b0) (Pi a1 b1).
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

Lemma Pair_EPar n (a b c : Tm n) :
  EPar.R (Pair a b) c ->
  (forall p, exists d, rtc RPar.R (Proj p c) d /\ EPar.R (if p is PL then a else b) d) /\
    (exists d0 d1, rtc RPar.R (App (ren_Tm shift c) (VarTm var_zero))
                (Pair (App (ren_Tm shift d0) (VarTm var_zero))(App (ren_Tm shift d1) (VarTm var_zero))) /\
    EPar.R a d0 /\ EPar.R b d1).
Proof.
  move E : (Pair a b) => u h. move : a b E.
  elim : n u c /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    move : iha => [_ [d0 [d1 [ih0 [ih1 ih2]]]]].
    split.
    + move => p.
      exists (Abs (App (ren_Tm shift (if p is PL then d0 else d1)) (VarTm var_zero))).
      split.
      * apply : relations.rtc_transitive.
        ** apply RPars.ProjCong. apply RPars.AbsCong. eassumption.
        ** apply : rtc_l. apply RPar.ProjAbs; eauto using RPar.refl. apply RPars.AbsCong.
           apply : rtc_l. apply RPar.ProjPair; eauto using RPar.refl.
           hauto l:on.
      * hauto lq:on use:EPar.AppEta'.
    + exists d0, d1.
      repeat split => //.
      apply : rtc_l. apply : RPar.AppAbs'; eauto using RPar.refl => //=.
      by asimpl; renamify.
  - move => n a0 a1 ha iha a b ?. subst. specialize iha with (1 := eq_refl).
    split => [p|].
    + move : iha => [/(_ p) [d [ih0 ih1]] _].
      exists d. split=>//.
      apply : rtc_l. apply RPar.ProjPair; eauto using RPar.refl.
      set q := (X in rtc RPar.R X d).
      by have -> : q = Proj p a1 by hauto lq:on.
    + move  :iha => [iha _].
      move : (iha PL) => [d0 [ih0 ih0']].
      move : (iha PR) => [d1 [ih1 ih1']] {iha}.
      exists d0, d1.
      apply RPars.weakening in ih0, ih1.
      repeat split => //=.
      apply : rtc_l. apply RPar.AppPair; eauto using RPar.refl.
      apply RPars.PairCong; apply RPars.AppCong; eauto using rtc_refl.
  - move => n a0 a1 b0 b1 ha _ hb _ a b [*]. subst.
    split.
    + move => p.
      exists (if p is PL then a1 else b1).
      split.
      * apply rtc_once. apply : RPar.ProjPair'; eauto using RPar.refl.
      * hauto lq:on rew:off.
    + exists a1, b1.
      split. apply rtc_once. apply RPar.AppPair; eauto using RPar.refl.
      split => //.
Qed.

Lemma commutativity0 n (a b0 b1 : Tm n) :
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
      move /(_ _ ltac:(by eauto using RPar.PairCong)) : iha
           => [c [ihc0 ihc1]].
      move /(_ _ ltac:(by eauto)) : ihb => [d [ihd0 ihd1]].
      move /Pair_EPar  : ihc1 => [_ [d0 [d1 [ih0 [ih1 ih2]]]]].
      move /RPars.substing : ih0. move /(_ d).
      asimpl => h.
      exists (Pair (App d0 d) (App d1 d)).
      split.
      hauto lq:on use:relations.rtc_transitive, RPars.AppCong.
      apply EPar.PairCong; by apply EPar.AppCong.
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
      move /Pair_EPar : ih1 => [/(_ p)[d [ihd ihd']] _].
      exists d. split => //.
      hauto lq:on use:RPars.ProjCong, relations.rtc_transitive.
    + hauto lq:on ctrs:EPar.R use:RPars.ProjCong.
  - hauto lq:on inv:RPar.R ctrs:EPar.R, rtc use:RPars.PiCong.
  - hauto l:on ctrs:EPar.R inv:RPar.R.
Qed.

Lemma commutativity1 n (a b0 b1 : Tm n) :
  EPar.R a b0 -> rtc RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ EPar.R b1 c.
Proof.
  move => + h. move : b0.
  elim : a b1 / h.
  - sfirstorder.
  - qauto l:on use:relations.rtc_transitive, commutativity0.
Qed.

Lemma commutativity n (a b0 b1 : Tm n) :
  rtc EPar.R a b0 -> rtc RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ rtc EPar.R b1 c.
  move => h. move : b1. elim : a b0 /h.
  - sfirstorder.
  - move => a0 a1 a2 + ha1 ih b1 +.
    move : commutativity1; repeat move/[apply].
    hauto q:on ctrs:rtc.
Qed.

Lemma Abs_EPar' n a (b : Tm n) :
  EPar.R (Abs a) b ->
  (exists d, EPar.R a d /\
          rtc OExp.R (Abs d) b).
Proof.
  move E : (Abs a) => u h.
  move : a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha a ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Proj_EPar' n p a (b : Tm n) :
  EPar.R (Proj p a) b ->
  (exists d, EPar.R a d /\
          rtc OExp.R (Proj p d) b).
Proof.
  move E : (Proj p a) => u h.
  move : p a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha a p ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a p ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma App_EPar' n (a b u : Tm n)  :
  EPar.R (App a b) u ->
  (exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (App a0 b0) u).
Proof.
  move E : (App a b) => t h.
  move : a b E. elim : n t u /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Pi_EPar' n (a : Tm n) b u  :
  EPar.R (Pi a b) u ->
  (exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (Pi a0 b0) u).
Proof.
  move E : (Pi a b) => t h.
  move : a b E. elim : n t u /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Pair_EPar' n (a b u : Tm n) :
  EPar.R (Pair a b) u ->
  exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (Pair a0 b0) u.
Proof.
  move E : (Pair a b) => t h.
  move : a b E. elim : n t u /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Bot_EPar' n (u : Tm n) :
  EPar.R Bot u ->
  rtc OExp.R Bot u.
  move E : Bot => t h.
  move : E. elim : n t u /h => //=.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma EPar_diamond n (c a1 b1 : Tm n) :
  EPar.R c a1 ->
  EPar.R c b1 ->
  exists d2, EPar.R a1 d2 /\ EPar.R b1 d2.
Proof.
  move => h. move : b1. elim : n c a1 / h.
  - move => n c a1 ha iha b1 /iha [d2 [hd0 hd1]].
    exists(Abs (App (ren_Tm shift d2) (VarTm var_zero))).
    hauto lq:on ctrs:EPar.R use:EPar.renaming.
  - hauto lq:on rew:off ctrs:EPar.R.
  - hauto lq:on use:EPar.refl.
  - move => n a0 a1 ha iha a2.
    move /Abs_EPar' => [d [hd0 hd1]].
    move : iha hd0; repeat move/[apply].
    move => [d2 [h0 h1]].
    have : EPar.R (Abs d) (Abs d2) by eauto using EPar.AbsCong.
    move : OExp.commutativity0 hd1; repeat move/[apply].
    move => [d1 [hd1 hd2]].
    exists d1. hauto lq:on ctrs:EPar.R use:OExp.merge.
  - move => n a0 a1 b0 b1 ha iha hb ihb c.
    move /App_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (App a2 b2)(App a3 b3)
      by hauto l:on use:EPar.AppCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - move => n a0 a1 b0 b1 ha iha hb ihb c.
    move /Pair_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (Pair a2 b2)(Pair a3 b3)
      by hauto l:on use:EPar.PairCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - move => n p a0 a1 ha iha b.
    move /Proj_EPar' => [d [/iha [d2 h] h1]] {iha}.
    have : EPar.R (Proj p d) (Proj p d2)
      by hauto l:on use:EPar.ProjCong.
    move : OExp.commutativity0 h1; repeat move/[apply].
    move => [d1 h1].
    exists d1. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - move => n a0 a1 b0 b1 ha iha hb ihb c.
    move /Pi_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (Pi a2 b2)(Pi a3 b3)
      by hauto l:on use:EPar.PiCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - qauto use:Bot_EPar', EPar.refl.
Qed.

Function tstar {n} (a : Tm n) :=
  match a with
  | VarTm i => a
  | Abs a => Abs (tstar a)
  | App (Abs a) b => subst_Tm (scons (tstar b) VarTm) (tstar a)
  | App (Pair a b) c =>
      Pair (App (tstar a) (tstar c)) (App (tstar b) (tstar c))
  | App a b => App (tstar a) (tstar b)
  | Pair a b => Pair (tstar a) (tstar b)
  | Proj p (Pair a b) => if p is PL then (tstar a) else (tstar b)
  | Proj p (Abs a) => (Abs (Proj p (tstar a)))
  | Proj p a => Proj p (tstar a)
  | Pi a b => Pi (tstar a) (tstar b)
  | Bot => Bot
  end.

Lemma RPar_triangle n (a : Tm n) : forall b, RPar.R a b -> RPar.R b (tstar a).
Proof.
  apply tstar_ind => {n a}.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on use:RPar.cong, RPar.refl ctrs:RPar.R inv:RPar.R.
  - hauto lq:on rew:off ctrs:RPar.R inv:RPar.R.
  - hauto lq:on rew:off inv:RPar.R ctrs:RPar.R.
  - hauto lq:on rew:off inv:RPar.R ctrs:RPar.R.
  - hauto drew:off inv:RPar.R use:RPar.refl, RPar.ProjPair'.
  - hauto drew:off inv:RPar.R use:RPar.refl, RPar.ProjPair'.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
Qed.

Lemma RPar_diamond n (c a1 b1 : Tm n) :
  RPar.R c a1 ->
  RPar.R c b1 ->
  exists d2, RPar.R a1 d2 /\ RPar.R b1 d2.
Proof. hauto l:on use:RPar_triangle. Qed.

Lemma RPar_confluent n (c a1 b1 : Tm n) :
  rtc RPar.R c a1 ->
  rtc RPar.R c b1 ->
  exists d2, rtc RPar.R a1 d2 /\ rtc RPar.R b1 d2.
Proof.
  sfirstorder use:relations.diamond_confluent, RPar_diamond.
Qed.

Lemma EPar_confluent n (c a1 b1 : Tm n) :
  rtc EPar.R c a1 ->
  rtc EPar.R c b1 ->
  exists d2, rtc EPar.R a1 d2 /\ rtc EPar.R b1 d2.
Proof.
  sfirstorder use:relations.diamond_confluent, EPar_diamond.
Qed.

Fixpoint depth_tm {n} (a : Tm n) :=
  match a with
  | VarTm _ => 1
  | Pi A B => 1 + max (depth_tm A) (depth_tm B)
  | Abs a => 1 + depth_tm a
  | App a b => 1 + max (depth_tm a) (depth_tm b)
  | Proj p a => 1 + depth_tm a
  | Pair a b => 1 + max (depth_tm a) (depth_tm b)
  | Bot => 1
  end.

Lemma depth_ren n m (ξ: fin n -> fin m) a :
  depth_tm a = depth_tm (ren_Tm ξ a).
Proof.
  move : m ξ. elim : n / a; scongruence.
Qed.

Lemma depth_subst n m (ρ : fin n -> Tm m) a :
  (forall i, depth_tm (ρ i) = 1) ->
  depth_tm a = depth_tm (subst_Tm ρ a).
Proof.
  move : m ρ. elim : n / a.
  - sfirstorder.
  - move => n a iha m ρ hρ.
    simpl.
    f_equal. apply iha.
    destruct i as [i|].
    + simpl.
      by rewrite -depth_ren.
    + by simpl.
  - hauto lq:on rew:off.
  - hauto lq:on rew:off.
  - hauto lq:on rew:off.
  - move => n a iha b ihb m ρ hρ.
    simpl. f_equal.
    f_equal.
    by apply iha.
    apply ihb.
    destruct i as [i|].
    + simpl.
      by rewrite -depth_ren.
    + by simpl.
  - sfirstorder.
Qed.

Lemma depth_subst_bool n (a : Tm (S n)) :
  depth_tm a = depth_tm (subst_Tm (scons Bot VarTm) a).
Proof.
  apply depth_subst.
  destruct i as [i|] => //=.
Qed.

Local Ltac prov_tac := sfirstorder use:depth_ren.
Local Ltac extract_tac := rewrite -?depth_subst_bool;hauto use:depth_subst_bool.

#[tactic="prov_tac"]Equations prov {n} (A : Tm n) (B : Tm (S n)) (a : Tm n) : Prop by wf (depth_tm a) lt :=
  prov A B (Pi A0 B0) := rtc Par.R A A0 /\ rtc Par.R B B0;
  prov A B (Abs a) := prov (ren_Tm shift A) (ren_Tm (upRen_Tm_Tm shift) B) a;
  prov A B (App a b) := prov A B a;
  prov A B (Pair a b) := prov A B a /\ prov A B b;
  prov A B (Proj p a) := prov A B a;
  prov A B Bot := False;
  prov A B (VarTm _) := False.

#[tactic="prov_tac"]Equations extract {n} (a : Tm n) : Tm n by wf (depth_tm a) lt :=
  extract (Pi A B) := Pi A B;
  extract (Abs a) := subst_Tm (scons Bot VarTm) (extract a);
  extract (App a b) := extract a;
  extract (Pair a b) := extract a;
  extract (Proj p a) := extract a;
  extract Bot := Bot;
  extract (VarTm _) := Bot.

(* Lemma extract_ren n m a (ξ : fin n -> fin m) : *)
(*   extract (ren_Tm ξ a) = ren_Tm ξ (extract a). *)
(* Proof. *)

(* Lemma ren_extract' n m a b (ξ : fin n -> fin m) : *)
(*   extract a = ren_Tm ξ b -> *)
(*   exists a0, ren_Tm ξ a0 = a /\ extract a0 = b. *)
(* Proof. *)
(*   move : n b ξ. *)
(*   elim : m / a. *)
(*   - move => n i m b ξ. simp extract. *)
(*     case : b => //= _. *)
(*     exists *)

Lemma ren_extract n m (a : Tm n) (ξ : fin n -> fin m) :
  extract (ren_Tm ξ a) = ren_Tm ξ (extract a).
Proof.
  move : m ξ. elim : n/a.
  - sfirstorder.
  - move => n a ih m ξ. simpl. simp extract.
    rewrite ih.
    by asimpl.
  - hauto q:on rew:db:extract.
  - hauto q:on rew:db:extract.
  - hauto q:on rew:db:extract.
  - hauto q:on rew:db:extract.
  - sfirstorder.
Qed.

Lemma tm_depth_ind (P : forall n, Tm n -> Prop)   :
  (forall n (a : Tm n), (forall m (b : Tm m), depth_tm b < depth_tm a -> P m b)  -> P n a) -> forall n a, P n a.
  move => ih.
  suff : forall m n (a : Tm n), depth_tm a <= m -> P n a by sfirstorder.
  elim.
  - move => n a h.
    apply ih. lia.
  - move => n ih0 m a h.
    apply : ih.
    move => m0 b h0.
    apply : ih0.
    lia.
Qed.

Lemma prov_ren n m (ξ : fin n -> fin m) A B a :
  prov A B a -> prov (ren_Tm ξ A) (ren_Tm (upRen_Tm_Tm ξ) B) (ren_Tm ξ a).
Proof.
  move : m ξ A B. elim : n / a.
  - sfirstorder rew:db:prov.
  - move => n a ih m ξ A B.
    simp prov. simpl.
    move /ih => {ih}.
    move /(_ _ (upRen_Tm_Tm ξ)).
    simp prov. by asimpl.
  - hauto q:on rew:db:prov.
  - qauto l:on rew:db:prov.
  - hauto lq:on rew:db:prov.
  - move => n A0 ih B0 h0 m ξ A B. simpl.
    simp prov.
    hauto l:on use:Pars.renaming.
  - sfirstorder.
Qed.

Lemma prov_morph n m (ρ : fin n -> Tm m) A B a :
  prov A B a ->
  prov (subst_Tm ρ A) (subst_Tm (up_Tm_Tm ρ) B) (subst_Tm ρ a).
Proof.
  move : m ρ A B. elim : n / a.
  - hauto q:on rew:db:prov.
  - move => n a ih m ρ A B.
    simp prov => /=.
    move /ih => {ih}.
    move /(_ _ (up_Tm_Tm ρ)). asimpl.
    simp prov. by asimpl.
  - hauto q:on rew:db:prov.
  - hauto q:on rew:db:prov.
  - hauto lq:on rew:db:prov.
  - hauto l:on use:Pars.substing rew:db:prov.
  - qauto rew:db:prov.
Qed.

Lemma prov_par n (A : Tm n) B a b : prov A B a -> Par.R a b -> prov A B b.
Proof.
  move => + h. move : A B.
  elim : n a b /h.
  - move => n a0 a1 b0 b1 ha iha hb ihb A B /=.
    simp prov => h.
    move /iha : h.
    move /(prov_morph _ _ (scons b1 VarTm)).
    by asimpl.
  - hauto lq:on rew:db:prov.
  - hauto lq:on rew:db:prov.
  - hauto lq:on rew:db:prov.
  - move => n a0 a1 ha iha A B. simp prov. move /iha.
    hauto l:on use:prov_ren.
  - hauto l:on rew:db:prov.
  - simp prov.
  - move => n a0 a1 ha iha A B. simp prov.
  - hauto l:on rew:db:prov.
  - hauto l:on rew:db:prov.
  - hauto lq:on rew:db:prov.
  - move => n A0 A1 B0 B1 hA ihA hB ihB A B. simp prov.
    move => [hA0 hA1].
    eauto using rtc_r.
  - sfirstorder.
Qed.

Lemma prov_pars n (A : Tm n) B a b : prov A B a -> rtc Par.R a b -> prov A B b.
Proof.
  induction 2; hauto lq:on use:prov_par.
Qed.

Lemma prov_extract n A B (a : Tm n) :
  prov A B a -> exists A0 B0,
      extract a = Pi A0 B0 /\ rtc Par.R A A0 /\ rtc Par.R B B0.
Proof.
  move : A B. elim : n / a => //=.
  - move => n a ih A B.
    simp prov.
    move /ih.
    simp extract.
    move => [A0][B0][h0][h1]h2.
    (* anti renaming for par *)
    have : exists A1, rtc Par.R A A1 /\ ren_Tm shift A1 = A0
        by hauto l:on use:Pars.antirenaming.
    move => [A1 [h3 h4]].
    have : exists B1, rtc Par.R B B1 /\ ren_Tm (upRen_Tm_Tm shift) B1 = B0
        by hauto l:on use:Pars.antirenaming.
    move => [B1 [h5 h6]].
    subst.
    have {}h0 : subst_Tm (scons Bot VarTm) (extract a) =
                  subst_Tm (scons Bot VarTm) (ren_Tm shift (Pi A1 B1)) by sauto lq:on.
    move : h0. asimpl. move => ->.
    hauto lq:on.
  - hauto l:on rew:db:prov, extract.
  - hauto l:on rew:db:prov, extract.
  - hauto l:on rew:db:prov, extract.
  - qauto l:on rew:db:prov, extract.
Qed.

Lemma pi_inv n (A : Tm n) B C :
  rtc Par.R (Pi A B) C ->
  exists A0 B0, extract C = Pi A0 B0 /\
             rtc Par.R A A0 /\ rtc Par.R B B0.
Proof.
  have : prov A B (Pi A B) by sfirstorder.
  move : prov_pars. repeat move/[apply].
  by move /prov_extract.
Qed.

Lemma pi_inj n (A0 A1 : Tm n) B0 B1 C :
  rtc Par.R (Pi A0 B0) C ->
  rtc Par.R (Pi A1 B1) C ->
  exists A2 B2, rtc Par.R A0 A2 /\ rtc Par.R A1 A2 /\
             rtc Par.R B0 B2 /\ rtc Par.R B1 B2.
Proof.
  move /pi_inv => [A2 [B2 [? [h0 h1]]]].
  move /pi_inv => [A3 [B3 [? [h2 h3]]]].
  exists A2, B2. hauto l:on.
Qed.

Lemma EPar_Par n (a b : Tm n) : EPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; qauto ctrs:Par.R.
Qed.

Lemma RPar_Par n (a b : Tm n) : RPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; hauto lq:on ctrs:Par.R.
Qed.

Module ERPar.
  Inductive R {n} (a b : Tm n) : Prop :=
  | RPar : RPar.R a b -> R a b
  | EPar : EPar.R a b -> R a b.
End ERPar.

Lemma ERPar_Par n (a b : Tm n) : ERPar.R a b -> Par.R a b.
Proof.
  sfirstorder inv:ERPar.R use:EPar_Par, RPar_Par.
Qed.

Lemma Par_ERPar n (a b : Tm n) : Par.R a b -> rtc ERPar.R a b.
Proof.
  move => h. elim : n a b /h.
  - move => n a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_l. apply ERPar.RPar.
    apply RPar.AppAbs; eauto using RPar.refl.
    (* congruence *)
    admit.
  - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc.
    apply : rtc_l. apply ERPar.RPar.
    apply RPar.AppPair; eauto using RPar.refl.
    admit.
  - move => n p a0 a1 ha iha.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjAbs; eauto using RPar.refl.
    admit.
  - move => n p a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjPair; eauto using RPar.refl.
    admit.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.AppEta; eauto using EPar.refl.
    admit.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.PairEta; eauto using EPar.refl.
    admit.
  - sfirstorder.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - sfirstorder.
Admitted.

Lemma Par_confluent n (c a1 b1 : Tm n) :
  rtc Par.R c a1 ->
  rtc Par.R c b1 ->
  exists d2, rtc Par.R a1 d2 /\ rtc Par.R b1 d2.
Proof.
Admitted.
