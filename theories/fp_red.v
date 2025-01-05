From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
Require Import ssreflect ssrbool.
Require Import FunInd.
Require Import Arith.Wf_nat.
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

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
  | BindCong p A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (TBind p A0 B0) (TBind p A1 B1)
  (* Bot is useful for making the prov function computable  *)
  | BotCong :
    R Bot Bot
  | UnivCong i :
    R (Univ i) (Univ i).

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
    - move => n p A0 A1 B0 B1 ha iha hB ihB m ξ []//= ? t t0 [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]].
      move : ihB => [c0 [? ?]]. subst.
      eexists. split. by apply BindCong; eauto.
      by asimpl.
    - move => n n0 ξ []//=. hauto l:on.
    - move => n i n0 ξ []//=. hauto l:on.
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
  | BindCong p A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (TBind p A0 B0) (TBind p A1 B1)
  | BotCong :
    R Bot Bot
  | UnivCong i :
    R (Univ i) (Univ i).

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

Module ERed.
  Inductive R {n} : Tm n -> Tm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a :
    R a (Abs (App (ren_Tm shift a) (VarTm var_zero)))
  | PairEta a :
    R a (Pair (Proj PL a) (Proj PR a))

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (Abs a0) (Abs a1)
  | AppCong0 a0 a1 b :
    R a0 a1 ->
    R (App a0 b) (App a1 b)
  | AppCong1 a b0 b1 :
    R b0 b1 ->
    R (App a b0) (App a b1)
  | PairCong0 a0 a1 b :
    R a0 a1 ->
    R (Pair a0 b) (Pair a1 b)
  | PairCong1 a b0 b1 :
    R b0 b1 ->
    R (Pair a b0) (Pair a b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (Proj p a0) (Proj p a1)
  | BindCong0 p A0 A1 B:
    R A0 A1 ->
    R (TBind p A0 B) (TBind p A1 B)
  | BindCong1 p A B0 B1:
    R B0 B1 ->
    R (TBind p A B0) (TBind p A B1).

  Lemma AppEta' n a (u : Tm n) :
    u = (Abs (App (ren_Tm shift a) (VarTm var_zero))) ->
    R a u.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a m ξ.
    apply AppEta'. by asimpl.
    all : qauto ctrs:R.
  Qed.

  Lemma substing n m (a : Tm n) b (ρ : fin n -> Tm m) :
    R a b ->
    R (subst_Tm ρ a) (subst_Tm ρ b).
  Proof.
    move => h. move : m ρ. elim : n a b / h => n.
    move => a m ρ /=.
    apply : AppEta'; eauto. by asimpl.
    all : hauto ctrs:R inv:option use:renaming.
  Qed.

End ERed.

Module EReds.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:ERed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : Tm (S n)) :
    rtc ERed.R a b ->
    rtc ERed.R (Abs a) (Abs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : Tm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (App a0 b0) (App a1 b1).
  Proof. solve_s. Qed.

  Lemma BindCong n p (a0 a1 : Tm n) b0 b1 :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (TBind p a0 b0) (TBind p a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : Tm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (Pair a0 b0) (Pair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : Tm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R (Proj p a0) (Proj p a1).
  Proof. solve_s. Qed.
End EReds.

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
  | BindCong p A0 A1 B0 B1:
    R A0 A1 ->
    R B0 B1 ->
    R (TBind p A0 B0) (TBind p A1 B1)
  | BotCong :
    R Bot Bot
  | UnivCong i :
    R (Univ i) (Univ i).

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

  Lemma BindCong n p (a0 a1 : Tm n) b0 b1 :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (TBind p a0 b0) (TBind p a1 b1).
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
  - hauto lq:on inv:RPar.R ctrs:EPar.R, rtc use:RPars.BindCong.
  - hauto l:on ctrs:EPar.R inv:RPar.R.
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

Lemma Bind_EPar' n p (a : Tm n) b u  :
  EPar.R (TBind p a b) u ->
  (exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (TBind p a0 b0) u).
Proof.
  move E : (TBind p a b) => t h.
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

Lemma Univ_EPar' n i (u : Tm n) :
  EPar.R (Univ i) u ->
  rtc OExp.R (Univ i) u.
  move E : (Univ i) => t h.
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
  - move => n p a0 a1 b0 b1 ha iha hb ihb c.
    move /Bind_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (TBind p a2 b2)(TBind p a3 b3)
      by hauto l:on use:EPar.BindCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - qauto use:Bot_EPar', EPar.refl.
  - qauto use:Univ_EPar', EPar.refl.
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
  | TBind p a b => TBind p (tstar a) (tstar b)
  | Bot => Bot
  | Univ i => Univ i
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
  | TBind _ A B => 1 + max (depth_tm A) (depth_tm B)
  | Abs a => 1 + depth_tm a
  | App a b => 1 + max (depth_tm a) (depth_tm b)
  | Proj p a => 1 + depth_tm a
  | Pair a b => 1 + max (depth_tm a) (depth_tm b)
  | Bot => 1
  | Univ i => 1
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
  - move => n p a iha b ihb m ρ hρ.
    simpl. f_equal.
    f_equal.
    by apply iha.
    apply ihb.
    destruct i as [i|].
    + simpl.
      by rewrite -depth_ren.
    + by simpl.
  - sfirstorder.
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

Definition prov_bind {n} p0 A0 B0 (a : Tm n)  :=
  match a with
  | TBind p A B => p = p0 /\ rtc Par.R A A0 /\ rtc Par.R B B0
  | _ => False
  end.

Definition prov_univ {n} i0 (a : Tm n) :=
  match a with
  | Univ i => i = i0
  | _ => False
  end.


Inductive prov {n} : Tm n -> Tm n -> Prop :=
| P_Bind p A A0 B B0  :
  rtc Par.R A A0 ->
  rtc Par.R B B0 ->
  prov (TBind p A B) (TBind p A0 B0)
| P_Abs h a :
  (forall b, prov h (subst_Tm (scons b VarTm) a)) ->
  prov h (Abs a)
| P_App h a b  :
  prov h a ->
  prov h (App a b)
| P_Pair h a b :
  prov h a ->
  prov h b ->
  prov h (Pair a b)
| P_Proj h p a :
  prov h a ->
  prov h (Proj p a)
| P_Bot  :
  prov Bot Bot
| P_Var i :
  prov (VarTm i) (VarTm i)
| P_Univ i :
  prov (Univ i) (Univ i).

Lemma ERed_EPar n (a b : Tm n) : ERed.R a b -> EPar.R a b.
Proof.
  induction 1; hauto lq:on ctrs:EPar.R use:EPar.refl.
Qed.

Lemma EPar_ERed n (a b : Tm n) : EPar.R a b -> rtc ERed.R a b.
Proof.
  move => h. elim : n a b /h.
  - eauto using rtc_r, ERed.AppEta.
  - eauto using rtc_r, ERed.PairEta.
  - auto using rtc_refl.
  - eauto using EReds.AbsCong.
  - eauto using EReds.AppCong.
  - eauto using EReds.PairCong.
  - eauto using EReds.ProjCong.
  - eauto using EReds.BindCong.
  - auto using rtc_refl.
  - auto using rtc_refl.
Qed.

Lemma EPar_Par n (a b : Tm n) : EPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; qauto ctrs:Par.R.
Qed.

Lemma RPar_Par n (a b : Tm n) : RPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; hauto lq:on ctrs:Par.R.
Qed.

Lemma rtc_idem n (a b : Tm n) : rtc (rtc EPar.R) a b -> rtc EPar.R a b.
Proof.
  induction 1; hauto l:on use:@relations.rtc_transitive, @rtc_r.
Qed.

Lemma prov_rpar n (u : Tm n) a b : prov u a -> RPar.R a b -> prov u b.
Proof.
  move => h.
  move : b.
  elim : u a / h.
  - qauto l:on ctrs:prov inv:RPar.R use:@rtc_r, RPar_Par.
  - hauto lq:on ctrs:prov inv:RPar.R use:RPar.substing.
  - move => h a b ha iha b0.
    elim /RPar.inv => //= _.
    + move => a0 a1 b1 b2 h0 h1 [*]. subst.
      have {}iha :  prov h (Abs a1) by hauto lq:on ctrs:RPar.R.
      hauto lq:on inv:prov use:RPar.substing.
    + move => a0 a1 b1 b2 c0 c1.
      move => h0 h1 h2 [*]. subst.
      have {}iha : prov h (Pair a1 b2) by hauto lq:on ctrs:RPar.R.
      hauto lq:on inv:prov ctrs:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on ctrs:prov inv:RPar.R.
  - move => h p a ha iha b.
    elim /RPar.inv => //= _.
    + move => p0 a0 a1 h0 [*]. subst.
      have {iha} :  prov h (Abs a1) by hauto lq:on ctrs:RPar.R.
      hauto lq:on ctrs:prov inv:prov use:RPar.substing.
    + move => p0 a0 a1 b0 b1 h0 h1 [*]. subst.
      have {iha} : prov h (Pair a1 b1) by hauto lq:on ctrs:RPar.R.
      qauto l:on inv:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on ctrs:prov inv:RPar.R.
  - hauto l:on ctrs:RPar.R inv:RPar.R.
  - hauto l:on ctrs:RPar.R inv:RPar.R.
Qed.

Lemma prov_oexp n (u : Tm n) a b : prov u a -> OExp.R a b -> prov u b.
Proof.
  move => + h. move : u.
  case : a b / h.
  - move => a u h.
    constructor. move => b. asimpl. by constructor.
  - move => a u h. by do 2 constructor.
Qed.

Lemma prov_oexps n (u : Tm n) a b : prov u a -> rtc OExp.R a b -> prov u b.
Proof.
  induction 2; sfirstorder use:prov_oexp.
Qed.

Lemma prov_lam n (u : Tm n) a : prov u a <-> prov u (Abs (App (ren_Tm shift a) (VarTm var_zero))).
Proof.
  split.
  move => h. constructor. move => b. asimpl. by constructor.
  inversion 1; subst.
  specialize H2 with (b := Bot).
  move : H2. asimpl. inversion 1; subst. done.
Qed.

Lemma prov_pair n (u : Tm n) a : prov u a <-> prov u (Pair (Proj PL a) (Proj PR a)).
Proof. hauto lq:on inv:prov ctrs:prov. Qed.

Derive Dependent Inversion inv with (forall n (a b : Tm n), ERed.R a b) Sort Prop.

Lemma prov_ered n (u : Tm n) a b : prov u a -> ERed.R a b -> prov u b.
Proof.
  move => h.
  move : b.
  elim : u a / h.
  - move => p A A0 B B0 hA hB b.
    elim /inv => // _.
    + move => a0 *. subst.
      rewrite -prov_lam.
      by constructor.
    + move => a0 *. subst.
      rewrite -prov_pair.
      by constructor.
    + qauto l:on ctrs:prov use:@rtc_r, ERed_EPar, EPar_Par.
    + qauto l:on ctrs:prov use:@rtc_r, ERed_EPar, EPar_Par.
  - move => h a ha iha b.
    elim /inv => // _.
    + move => a0 *. subst.
      rewrite -prov_lam.
      by constructor.
    + move => a0 *. subst.
      rewrite -prov_pair.
      by constructor.
    + hauto lq:on ctrs:prov use:ERed.substing.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - move => h a b ha iha hb ihb b0.
    elim /inv => //_.
    + move => a0 *. subst.
      rewrite -prov_lam.
      by constructor.
    + move => a0 *. subst.
      rewrite -prov_pair.
      by constructor.
    + hauto lq:on ctrs:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
Qed.

Fixpoint extract {n} (a : Tm n) : Tm n :=
  match a with
  | TBind p A B => TBind p A B
  | Abs a => subst_Tm (scons Bot VarTm) (extract a)
  | App a b => extract a
  | Pair a b => extract a
  | Proj p a => extract a
  | Bot => Bot
  | VarTm i => VarTm i
  | Univ i => Univ i
  end.

Lemma ren_extract n m (a : Tm n) (ξ : fin n -> fin m) :
  extract (ren_Tm ξ a) = ren_Tm ξ (extract a).
Proof.
  move : m ξ. elim : n/a.
  - sfirstorder.
  - move => n a ih m ξ /=.
    rewrite ih.
    by asimpl.
  - hauto q:on.
  - hauto q:on.
  - hauto q:on.
  - hauto q:on.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma ren_morphing n m (a : Tm n) (ρ : fin n -> Tm m) :
  (forall i, ρ i = extract (ρ i)) ->
  extract (subst_Tm ρ a) = subst_Tm ρ (extract a).
Proof.
  move : m ρ.
  elim : n /a => n //=.
  move => a ha m ρ hi.
  rewrite ha.
  - destruct i as [i|] => //.
    rewrite ren_extract.
    rewrite -hi.
    by asimpl.
  - by asimpl.
Qed.

Lemma ren_subst_bot n (a : Tm (S n)) :
  extract (subst_Tm (scons Bot VarTm) a) = subst_Tm (scons Bot VarTm) (extract a).
Proof.
  apply ren_morphing. destruct i as [i|] => //=.
Qed.

Definition prov_extract_spec {n} u (a : Tm n) :=
  match u with
  | TBind p A B => exists A0 B0, extract a = TBind p A0 B0 /\ rtc Par.R A A0 /\ rtc Par.R B B0
  | Univ i => extract a = Univ i
  | VarTm i => extract a = VarTm i
  | _ => True
  end.

Lemma prov_extract n u (a : Tm n) :
  prov u a -> prov_extract_spec u a.
Proof.
  move => h.
  elim : u a /h.
  - sfirstorder.
  - move => h a ha ih.
    case : h ha ih => //=.
    + move => i ha ih.
      move /(_ Bot) in ih.
      rewrite -ih.
      by rewrite ren_subst_bot.
    + move => p A B h ih.
      move /(_ Bot) : ih => [A0][B0][h0][h1]h2.
      rewrite ren_subst_bot in h0.
      rewrite h0.
      eauto.
    + move => i h /(_ Bot).
      by rewrite ren_subst_bot => ->.
  - hauto lq:on.
  - hauto lq:on.
  - hauto lq:on.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
Qed.

Definition union {A : Type} (R0 R1 : A -> A -> Prop) a b :=
  R0 a b \/ R1 a b.

Module ERPar.
  Definition R {n} (a b : Tm n) := union RPar.R EPar.R a b.
  Lemma RPar {n} (a b : Tm n) : RPar.R a b -> R a b.
  Proof. sfirstorder. Qed.

  Lemma EPar {n} (a b : Tm n) : EPar.R a b -> R a b.
  Proof. sfirstorder. Qed.

  Lemma refl {n} ( a : Tm n) : ERPar.R a a.
  Proof.
    sfirstorder use:RPar.refl, EPar.refl.
  Qed.

  Lemma ProjCong n p (a0 a1 : Tm n) :
    R a0 a1 ->
    rtc R (Proj p a0) (Proj p a1).
  Proof.
    move => [].
    - move => h.
      apply rtc_once.
      left.
      by apply RPar.ProjCong.
    - move => h.
      apply rtc_once.
      right.
      by apply EPar.ProjCong.
  Qed.

  Lemma AbsCong n (a0 a1 : Tm (S n)) :
    R a0 a1 ->
    rtc R (Abs a0) (Abs a1).
  Proof.
    move => [].
    - move => h.
      apply rtc_once.
      left.
      by apply RPar.AbsCong.
    - move => h.
      apply rtc_once.
      right.
      by apply EPar.AbsCong.
  Qed.

  Lemma AppCong n (a0 a1 b0 b1 : Tm n) :
    R a0 a1 ->
    R b0 b1 ->
    rtc R (App a0 b0) (App a1 b1).
  Proof.
    move => [] + [].
    - sfirstorder use:RPar.AppCong, @rtc_once.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.AppCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.AppCong, EPar.refl.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.AppCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.AppCong, EPar.refl.
    - sfirstorder use:EPar.AppCong, @rtc_once.
  Qed.

  Lemma BindCong n p (a0 a1 : Tm n) b0 b1:
    R a0 a1 ->
    R b0 b1 ->
    rtc R (TBind p a0 b0) (TBind p a1 b1).
  Proof.
    move => [] + [].
    - sfirstorder use:RPar.BindCong, @rtc_once.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.BindCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.BindCong, EPar.refl.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.BindCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.BindCong, EPar.refl.
    - sfirstorder use:EPar.BindCong, @rtc_once.
  Qed.

  Lemma PairCong n (a0 a1 b0 b1 : Tm n) :
    R a0 a1 ->
    R b0 b1 ->
    rtc R (Pair a0 b0) (Pair a1 b1).
  Proof.
    move => [] + [].
    - sfirstorder use:RPar.PairCong, @rtc_once.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.PairCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.PairCong, EPar.refl.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.PairCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.PairCong, EPar.refl.
    - sfirstorder use:EPar.PairCong, @rtc_once.
  Qed.

  Lemma renaming n m (a b : Tm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_Tm ξ a) (ren_Tm ξ b).
  Proof.
    sfirstorder use:EPar.renaming, RPar.renaming.
  Qed.

End ERPar.

Hint Resolve ERPar.AppCong ERPar.refl ERPar.AbsCong ERPar.PairCong ERPar.ProjCong ERPar.BindCong : erpar.

Module ERPars.
  #[local]Ltac solve_s_rec :=
  move => *; eapply relations.rtc_transitive; eauto;
         hauto lq:on db:erpar.
  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AppCong n (a0 a1 b0 b1 : Tm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R b0 b1 ->
    rtc ERPar.R (App a0 b0) (App a1 b1).
  Proof. solve_s. Qed.

  Lemma AbsCong n (a0 a1 : Tm (S n)) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (Abs a0) (Abs a1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : Tm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R b0 b1 ->
    rtc ERPar.R (Pair a0 b0) (Pair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1 : Tm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (Proj p a0) (Proj p a1).
  Proof. solve_s. Qed.

  Lemma BindCong n p (a0 a1 : Tm n) b0 b1:
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R b0 b1 ->
    rtc ERPar.R (TBind p a0 b0) (TBind p a1 b1).
  Proof. solve_s. Qed.

  Lemma renaming n (a0 a1 : Tm n) m (ξ : fin n -> fin m) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (ren_Tm ξ a0) (ren_Tm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using ERPar.renaming, rtc_l.
  Qed.

End ERPars.

Lemma ERPar_Par n (a b : Tm n) : ERPar.R a b -> Par.R a b.
Proof.
  sfirstorder use:EPar_Par, RPar_Par.
Qed.

Lemma Par_ERPar n (a b : Tm n) : Par.R a b -> rtc ERPar.R a b.
Proof.
  move => h. elim : n a b /h.
  - move => n a0 a1 b0 b1 ha iha hb ihb.
    suff ? : rtc ERPar.R (App (Abs a0) b0) (App (Abs a1) b1).
    apply : relations.rtc_transitive; eauto.
    apply rtc_once. apply ERPar.RPar.
    by apply RPar.AppAbs; eauto using RPar.refl.
    eauto using ERPars.AppCong,ERPars.AbsCong.
  - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc.
    apply : rtc_l. apply ERPar.RPar.
    apply RPar.AppPair; eauto using RPar.refl.
    sfirstorder use:ERPars.AppCong, ERPars.PairCong.
  - move => n p a0 a1 ha iha.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjAbs; eauto using RPar.refl.
    sfirstorder use:ERPars.AbsCong, ERPars.ProjCong.
  - move => n p a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjPair; eauto using RPar.refl.
    hauto lq:on.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.AppEta; eauto using EPar.refl.
    hauto lq:on ctrs:rtc
      use:ERPars.AppCong, ERPars.AbsCong, ERPars.renaming.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.PairEta; eauto using EPar.refl.
    sfirstorder use:ERPars.PairCong, ERPars.ProjCong.
  - sfirstorder.
  - sfirstorder use:ERPars.AbsCong.
  - sfirstorder use:ERPars.AppCong.
  - sfirstorder use:ERPars.PairCong.
  - sfirstorder use:ERPars.ProjCong.
  - sfirstorder use:ERPars.BindCong.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma Pars_ERPar n (a b : Tm n) : rtc Par.R a b -> rtc ERPar.R a b.
Proof.
  induction 1; hauto l:on use:Par_ERPar, @relations.rtc_transitive.
Qed.

Lemma Par_ERPar_iff n (a b : Tm n) : rtc Par.R a b <-> rtc ERPar.R a b.
Proof.
  split.
  sfirstorder use:Pars_ERPar, @relations.rtc_subrel.
  sfirstorder use:ERPar_Par, @relations.rtc_subrel.
Qed.

Lemma RPar_ERPar n (a b : Tm n) : rtc RPar.R a b -> rtc ERPar.R a b.
Proof.
  sfirstorder use:@relations.rtc_subrel.
Qed.

Lemma EPar_ERPar n (a b : Tm n) : rtc EPar.R a b -> rtc ERPar.R a b.
Proof.
  sfirstorder use:@relations.rtc_subrel.
Qed.

Module Type HindleyRosen.
  Parameter A : nat -> Type.
  Parameter R0 R1 : forall n, A n -> A n -> Prop.
  Axiom diamond_R0 : forall n, relations.diamond (R0 n).
  Axiom diamond_R1 : forall n, relations.diamond (R1 n).
  Axiom commutativity : forall n,
    forall a b c, R0 n a b -> R1 n a c -> exists d, R1 n b d /\ R0 n c d.
End HindleyRosen.

Module HindleyRosenFacts (M : HindleyRosen).
  Import M.
  Lemma R0_comm :
    forall n a b c, R0 n a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ R0 n c d.
  Proof.
    move => n a + c + h.
    elim : a c /h.
    - sfirstorder.
    - move => a0 a1 a2 ha ha0 ih b h.
      case : ha.
      + move : diamond_R0 h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
      + move : commutativity h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
  Qed.

  Lemma R1_comm :
    forall n a b c, R1 n a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ R1 n c d.
  Proof.
    move => n a + c + h.
    elim : a c /h.
    - sfirstorder.
    - move => a0 a1 a2 ha ha0 ih b h.
      case : ha.
      + move : commutativity h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
      + move : diamond_R1 h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
  Qed.

  Lemma U_comm :
    forall n a b c, (union (R0 n) (R1 n)) a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ (union (R0 n) (R1 n)) c d.
  Proof.
    hauto lq:on use:R0_comm, R1_comm.
  Qed.

  Lemma U_comms :
    forall n a b c, rtc (union (R0 n) (R1 n)) a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ rtc (union (R0 n) (R1 n)) c d.
  Proof.
    move => n a b + h.
    elim : a b /h.
    - sfirstorder.
    - hecrush ctrs:rtc use:U_comm.
  Qed.

End HindleyRosenFacts.

Module HindleyRosenER <: HindleyRosen.
  Definition A := Tm.
  Definition R0 n := rtc (@RPar.R n).
  Definition R1 n := rtc (@EPar.R n).
  Lemma diamond_R0 : forall n, relations.diamond (R0 n).
    sfirstorder use:RPar_confluent.
  Qed.
  Lemma diamond_R1 : forall n, relations.diamond (R1 n).
    sfirstorder use:EPar_confluent.
  Qed.
  Lemma commutativity : forall n,
    forall a b c, R0 n a b -> R1 n a c -> exists d, R1 n b d /\ R0 n c d.
  Proof.
    hauto l:on use:commutativity.
  Qed.
End HindleyRosenER.

Module ERFacts := HindleyRosenFacts HindleyRosenER.

Lemma rtc_union n (a b : Tm n) :
  rtc (union RPar.R EPar.R) a b <->
    rtc (union (rtc RPar.R) (rtc EPar.R)) a b.
Proof.
  split; first by induction 1; hauto lq:on ctrs:rtc.
  move => h.
  elim  :a b /h.
  - sfirstorder.
  - move => a0 a1 a2.
    case.
    + move => h0 h1 ih.
      apply : relations.rtc_transitive; eauto.
      move : h0.
      apply relations.rtc_subrel.
      sfirstorder.
    + move => h0 h1 ih.
      apply : relations.rtc_transitive; eauto.
      move : h0.
      apply relations.rtc_subrel.
      sfirstorder.
Qed.

Lemma Par_confluent n (a b c : Tm n) :
  rtc Par.R a b ->
  rtc Par.R a c ->
  exists d, rtc Par.R b d /\ rtc Par.R c d.
Proof.
  move : n a b c.
  suff : forall (n : nat) (a b c : Tm n),
      rtc ERPar.R a b ->
      rtc ERPar.R a c -> exists d : Tm n, rtc ERPar.R b d /\ rtc ERPar.R c d.
  move => h n a b c h0 h1.
  apply Par_ERPar_iff in h0, h1.
  move : h h0 h1; repeat move/[apply].
  hauto lq:on use:Par_ERPar_iff.
  have h := ERFacts.U_comms.
  move => n a b c.
  rewrite /HindleyRosenER.R0 /HindleyRosenER.R1 in h.
  specialize h with (n := n).
  rewrite /HindleyRosenER.A in h.
  rewrite /ERPar.R.
  have eq : (fun a0 b0 : Tm n => union RPar.R EPar.R a0 b0) = union RPar.R EPar.R by reflexivity.
  rewrite !{}eq.
  move /rtc_union => + /rtc_union.
  move : h; repeat move/[apply].
  hauto lq:on use:rtc_union.
Qed.

Lemma pars_univ_inv n i (c : Tm n) :
  rtc Par.R (Univ i) c ->
  extract c = Univ i.
Proof.
  have : prov (Univ i) (Univ i : Tm n) by sfirstorder.
  move : prov_pars. repeat move/[apply].
  move /(_ ltac:(reflexivity)).
  by move/prov_extract.
Qed.

Lemma pars_pi_inv n p (A : Tm n) B C :
  rtc Par.R (TBind p A B) C ->
  exists A0 B0, extract C = TBind p A0 B0 /\
             rtc Par.R A A0 /\ rtc Par.R B B0.
Proof.
  have : prov (TBind p A B) (TBind p A B) by sfirstorder.
  move : prov_pars. repeat move/[apply].
  move /(_ eq_refl).
  by move /prov_extract.
Qed.

Lemma pars_univ_inj n i j (C : Tm n) :
  rtc Par.R (Univ i) C ->
  rtc Par.R (Univ j) C ->
  i = j.
Proof.
  sauto l:on use:pars_univ_inv.
Qed.

Lemma pars_pi_inj n p0 p1 (A0 A1 : Tm n) B0 B1 C :
  rtc Par.R (TBind p0 A0 B0) C ->
  rtc Par.R (TBind p1 A1 B1) C ->
  exists A2 B2, p1 = p0 /\ rtc Par.R A0 A2 /\ rtc Par.R A1 A2 /\
             rtc Par.R B0 B2 /\ rtc Par.R B1 B2.
Proof.
  move /pars_pi_inv => [A2 [B2 [? [h0 h1]]]].
  move /pars_pi_inv => [A3 [B3 [? [h2 h3]]]].
  exists A2, B2. hauto l:on.
Qed.

Definition join {n} (a b : Tm n) :=
  exists c, rtc Par.R a c /\ rtc Par.R b c.

Lemma join_transitive n (a b c : Tm n) :
  join a b -> join b c -> join a c.
Proof.
  rewrite /join.
  move => [ab [h0 h1]] [bc [h2 h3]].
  move : Par_confluent h1 h2; repeat move/[apply].
  move => [abc [h4 h5]].
  eauto using relations.rtc_transitive.
Qed.

Lemma join_symmetric n (a b : Tm n) :
  join a b -> join b a.
Proof. sfirstorder unfold:join. Qed.

Lemma join_refl n (a : Tm n) : join a a.
Proof. hauto lq:on ctrs:rtc unfold:join. Qed.

Lemma join_univ_inj n i j :
  join (Univ i : Tm n) (Univ j) -> i = j.
Proof.
  sfirstorder use:pars_univ_inj.
Qed.

Lemma join_pi_inj n p0 p1 (A0 A1 : Tm n) B0 B1 :
  join (TBind p0 A0 B0) (TBind p1 A1 B1) ->
  p0 = p1 /\ join A0 A1 /\ join B0 B1.
Proof.
  move => [c []].
  move : pars_pi_inj; repeat move/[apply].
  sfirstorder unfold:join.
Qed.

Lemma join_univ_pi_contra n p (A : Tm n) B i :
  join (TBind p A B) (Univ i) -> False.
Proof.
  rewrite /join.
  move => [c [h0 h1]].
  move /pars_univ_inv : h1.
  move /pars_pi_inv : h0.
  hauto l:on.
Qed.


Lemma join_substing n m (a b : Tm n) (ρ : fin n -> Tm m) :
  join a b ->
  join (subst_Tm ρ a) (subst_Tm ρ b).
Proof. hauto lq:on unfold:join use:Pars.substing. Qed.
