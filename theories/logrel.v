Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..)).
Definition ProdSpace {n} (PA : Tm n -> Prop)
  (PF : Tm n -> (Tm n -> Prop) -> Prop) : Tm n -> Prop :=
  fun b => forall a PB, PA a -> PF a PB -> PB (App b a).

Reserved Notation "⟦ A ⟧ i ;; I ↘ S" (at level 70).
Inductive InterpExt {n} i (I : forall n, nat -> Tm n -> Prop) : Tm n -> (Tm n -> Prop) -> Prop :=
| InterpExt_Fun A B PA PF :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) ->
  ⟦ TBind TPi A B ⟧ i ;; I ↘ (ProdSpace PA PF)

| InterpExt_Univ j :
  j < i ->
  ⟦ Univ j ⟧ i ;; I ↘ (I n j)

| InterpExt_Step A A0 PA :
  RPar.R A A0 ->
  ⟦ A0 ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PA
where "⟦ A ⟧ i ;; I ↘ S" := (InterpExt i I A S).

Lemma InterpExt_Univ' {n} i  I j (PF : Tm n -> Prop) :
  PF = I n j ->
  j < i ->
  ⟦ Univ j ⟧ i ;; I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Infix "<?" := Compare_dec.lt_dec (at level 60).

Equations InterpUnivN n (i : nat) : Tm n -> (Tm n -> Prop) -> Prop by wf i lt :=
  InterpUnivN n i := @InterpExt n i
                     (fun n j A =>
                        match j <? i  with
                        | left _ => exists PA, InterpUnivN n j A PA
                        | right _ => False
                        end).
Arguments InterpUnivN {n}.

Lemma InterpExt_lt_impl {n : nat} i I I' A (PA : Tm n -> Prop) :
  (forall j, j < i -> I n j = I' n j) ->
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI h.
  elim : A PA /h.
  - hauto lq:on rew:off ctrs:InterpExt.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_eq {n : nat} i I I' A (PA : Tm n -> Prop) :
  (forall j, j < i -> I n j = I' n j) ->
  ⟦ A ⟧ i ;; I ↘ PA =
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI. apply propositional_extensionality.
  have : forall j, j < i -> I' n j = I n j by sfirstorder.
  firstorder using InterpExt_lt_impl.
Qed.

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

Lemma InterpUnivN_nolt n i :
  @InterpUnivN n i = @InterpExt n i (fun n j (A : Tm n) => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUnivN.
  extensionality A. extensionality PA.
  set I0 := (fun _ => _).
  set I1 := (fun _ => _).
  apply InterpExt_lt_eq.
  hauto q:on.
Qed.

#[export]Hint Rewrite @InterpUnivN_nolt : InterpUniv.

Lemma RPar_substone n (a b : Tm (S n)) (c : Tm n):
    RPar.R a b -> RPar.R (subst_Tm (scons c VarTm) a) (subst_Tm (scons c VarTm) b).
  Proof. hauto l:on inv:option use:RPar.substing, RPar.refl. Qed.

Lemma InterpExt_Fun_inv n i I (A : Tm n) B P
  (h :  ⟦ TBind TPi A B ⟧ i ;; I ↘ P) :
  exists (PA : Tm n -> Prop) (PF : Tm n -> (Tm n -> Prop) -> Prop),
     ⟦ A ⟧ i ;; I ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (TBind TPi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto l:on.
  - move => A A0 PA hA hA0 hPi A1 B ?. subst.
    elim /RPar.inv : hA => //= _ p A2 A3 B0 B1 hA1 hB0 [*]. subst.
    hauto lq:on ctrs:InterpExt use:RPar_substone.
Qed.

Lemma InterpExt_Fun_nopf n i I (A : Tm n) B PA  :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘  PB) ->
  ⟦ Pi A B ⟧ i ;; I ↘ (ProdSpace PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB)).
Proof.
  move => h0 h1. apply InterpExt_Fun =>//.
Qed.

Lemma InterpUnivN_Fun_nopf n i (A : Tm n) B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) ->
  ⟦ Pi A B ⟧ i ↘ (ProdSpace PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB)).
Proof.
  hauto l:on use:InterpExt_Fun_nopf rew:db:InterpUniv.
Qed.

Lemma InterpExt_cumulative n i j I (A : Tm n) PA :
  i < j ->
   ⟦ A ⟧ i ;; I ↘ PA ->
   ⟦ A ⟧ j ;; I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.lt_trans.
Qed.

Lemma InterpUnivN_cumulative n i (A : Tm n) PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i < j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Lemma InterpExt_preservation n i I (A : Tm n) B P (h : InterpExt i I A P) :
  RPar.R A B ->
  ⟦ B ⟧ i ;; I ↘ P.
Proof.
  move : B.
  elim : A P / h; auto.
  - move => A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /RPar.inv :  hT => //.
    move => hPar A0 A1 B0 B1 h0 h1 [? ?] ?; subst.
    apply InterpExt_Fun; auto.
    move => a PB hPB0.
    apply : ihPB; eauto.
    sfirstorder use:RPar.cong, RPar.refl.
  - hauto lq:on inv:RPar.R ctrs:InterpExt.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := RPar_diamond  _ _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation n i (A : Tm n) B P (h : ⟦ A ⟧ i ↘ P) :
  RPar.R A B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star n i I (A : Tm n) B P (h : ⟦ B ⟧ i ;; I ↘ P) :
  rtc RPar.R A B ->
  ⟦ A ⟧ i ;; I ↘ P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star n i I (A : Tm n) B P (h : ⟦ A ⟧ i ;; I ↘ P) :
  rtc RPar.R A B ->
  ⟦ B ⟧ i ;; I ↘ P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star n i (A : Tm n) B P (h : ⟦ A ⟧ i ↘ P) :
  rtc RPar.R A B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star n i (A : Tm n) B P (h : ⟦ B ⟧ i ↘ P) :
  rtc RPar.R A B ->
  ⟦ A ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

Definition ty_hf {n} (a : Tm n) :=
  match a with
  | Pi _ _ => true
  | Univ _ => true
  | _ => false
  end.

Lemma InterpExtInv n i I (A : Tm n) PA :
  ⟦ A ⟧ i ;; I ↘ PA ->
  exists B, ty_hf B /\ rtc RPar.R A B /\  ⟦ B ⟧ i ;; I ↘ PA.
Proof.
  move => h. elim : A PA /h.
  - move => A B PA PF hPA _ hPF hPF0 _.
    exists (Pi A B). repeat split => //=.
    apply rtc_refl.
    hauto l:on ctrs:InterpExt.
  - move => j ?. exists (Univ j).
    hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:rtc.
Qed.

Lemma InterpExt_Join n i I (A B : Tm n) PA PB :
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ B ⟧ i ;; I ↘ PB ->
  join A B ->
  PA = PB.
Proof.
  move => h. move : B PB. elim : A PA /h.
  - move => A B PA PF hPA ihPA hTot hRes ihPF U PU /InterpExtInv.
    move => [B0 []].
    case : B0 => //=.
    + move => A0 B0 _ [hr hPi].
      move /InterpExt_Fun_inv : hPi.
      move => [PA0][PF0][hPA0][hTot0][hRes0]?. subst.
      move => hjoin.
      have ? : join A A0 by admit.
      have ? : join B B0 by admit.
      have ? : PA0 = PA by hauto l:on. subst.
      rewrite /ProdSpace.
      extensionality b.
      apply propositional_extensionality.
      admit.
    (* Contradiction *)
    + admit.
  - admit.
  - admit.
Admitted.
