Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..), rtc_subrel).
Definition ProdSpace {n} (PA : Tm n -> Prop)
  (PF : Tm n -> (Tm n -> Prop) -> Prop) b : Prop :=
  forall a PB, PA a -> PF a PB -> PB (App b a).

Definition SumSpace {n} (PA : Tm n -> Prop)
  (PF : Tm n -> (Tm n -> Prop) -> Prop) t : Prop :=
  exists a b, rtc RPar.R t (Pair a b) /\ PA a /\ (forall PB, PF a PB -> PB b).

Definition BindSpace {n} p := if p is TPi then @ProdSpace n else @SumSpace n.

Reserved Notation "⟦ A ⟧ i ;; I ↘ S" (at level 70).
Inductive InterpExt {n} i (I : forall n, nat -> Tm n -> Prop) : Tm n -> (Tm n -> Prop) -> Prop :=
| InterpExt_Bind p A B PA PF :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) ->
  ⟦ TBind p A B ⟧ i ;; I ↘ BindSpace p PA PF

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

Lemma InterpExt_Bind_inv n p i I (A : Tm n) B P
  (h :  ⟦ TBind p A B ⟧ i ;; I ↘ P) :
  exists (PA : Tm n -> Prop) (PF : Tm n -> (Tm n -> Prop) -> Prop),
     ⟦ A ⟧ i ;; I ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) /\
    P = BindSpace p PA PF.
Proof.
  move E : (TBind p A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto l:on.
  - move => A A0 PA hA hA0 hPi A1 B ?. subst.
    elim /RPar.inv : hA => //= _ p0 A2 A3 B0 B1 hA1 hB0 [*]. subst.
    hauto lq:on ctrs:InterpExt use:RPar_substone.
Qed.

Lemma InterpExt_Univ_inv n i I j P
  (h :  ⟦ @Univ n j  ⟧ i ;; I ↘ P) :
  P = I n j /\ j < i.
Proof.
  move : h.
  move E : (@Univ n j) => T h. move : j E.
  elim : T P /h => //.
  - hauto l:on.
  - hauto lq:on rew:off inv:RPar.R.
Qed.

Lemma InterpExt_Bind_nopf n p i I (A : Tm n) B PA  :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘  PB) ->
  ⟦ TBind p A B ⟧ i ;; I ↘ (BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB)).
Proof.
  move => h0 h1. apply InterpExt_Bind =>//.
Qed.

Lemma InterpUnivN_Fun_nopf n p i (A : Tm n) B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) ->
  ⟦ TBind p A B ⟧ i ↘ (BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB)).
Proof.
  hauto l:on use:InterpExt_Bind_nopf rew:db:InterpUniv.
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
  - move => p A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /RPar.inv :  hT => //.
    move => hPar p0 A0 A1 B0 B1 h0 h1 [? ?] ? ?; subst.
    apply InterpExt_Bind; auto => a PB hPB0.
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

Lemma InterpExtInv n i I (A : Tm n) PA :
  ⟦ A ⟧ i ;; I ↘ PA ->
  exists B, hfb B /\ rtc RPar.R A B /\  ⟦ B ⟧ i ;; I ↘ PA.
Proof.
  move => h. elim : A PA /h.
  - move => p A B PA PF hPA _ hPF hPF0 _.
    exists (TBind p A B). repeat split => //=.
    apply rtc_refl.
    hauto l:on ctrs:InterpExt.
  - move => j ?. exists (Univ j).
    hauto l:on ctrs:InterpExt.
  - hauto lq:on ctrs:rtc.
Qed.

Lemma RPars_Pars {n} (A B : Tm n) :
  rtc RPar.R A B ->
  rtc Par.R A B.
Proof. hauto lq:on use:RPar_Par, rtc_subrel. Qed.

Lemma RPars_join {n} (A B : Tm n) :
  rtc RPar.R A B -> join A B.
Proof. hauto lq:on ctrs:rtc use:RPars_Pars. Qed.

Lemma bindspace_iff {n} p (PA : Tm n -> Prop) PF PF0 b  :
  (forall (a : Tm n) (PB PB0 : Tm n -> Prop), PF a PB -> PF0 a PB0 -> PB = PB0) ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a, PA a -> exists PB0, PF0 a PB0) ->
  (BindSpace p PA PF b <-> BindSpace p PA PF0 b).
Proof.
  rewrite /BindSpace => h hPF hPF0.
  case : p => /=.
  - rewrite /ProdSpace.
    split.
    move => h1 a PB ha hPF'.
    specialize hPF with (1 := ha).
    specialize hPF0 with (1 := ha).
    sblast.
    move => ? a PB ha.
    specialize hPF with (1 := ha).
    specialize hPF0 with (1 := ha).
    sblast.
  - rewrite /SumSpace.
    hauto lq:on rew:off.
Qed.

Lemma InterpExt_Join n i I (A B : Tm n) PA PB :
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ B ⟧ i ;; I ↘ PB ->
  join A B ->
  PA = PB.
Proof.
  move => h. move : B PB. elim : A PA /h.
  - move => p A B PA PF hPA ihPA hTot hRes ihPF U PU /InterpExtInv.
    move => [B0 []].
    case : B0 => //=.
    + move => p0 A0 B0 _ [hr hPi].
      move /InterpExt_Bind_inv : hPi.
      move => [PA0][PF0][hPA0][hTot0][hRes0]?. subst.
      move => hjoin.
      have{}hr : join U (TBind p0 A0 B0) by auto using RPars_join.
      have hj : join (TBind p A B) (TBind p0 A0 B0) by eauto using join_transitive.
      have {hj} : p0 = p /\ join A A0 /\ join B B0 by hauto l:on use:join_pi_inj.
      move => [? [h0 h1]]. subst.
      have ? : PA0 = PA by hauto l:on. subst.
      rewrite /ProdSpace.
      extensionality b.
      apply propositional_extensionality.
      apply bindspace_iff; eauto.
      move => a PB PB0 hPB hPB0.
      apply : ihPF; eauto.
      by apply join_substing.
    + move => j _.
      move => [h0 h1] h.
      have ? : join U (Univ j) by eauto using RPars_join.
      have : join (TBind p A B) (Univ j) by eauto using join_transitive.
      move => ?. exfalso.
      eauto using join_univ_pi_contra.
  - move => j ? B PB /InterpExtInv.
    move => [+ []]. case => //=.
    + move => p A0 B0 _ [].
      move /RPars_join => *.
      have ?  : join (TBind p A0 B0) (Univ j) by eauto using join_symmetric, join_transitive.
      exfalso.
      eauto using join_univ_pi_contra.
    + move => m _ [/RPars_join h0 + h1].
      have /join_univ_inj {h0 h1} ?  : join (Univ j : Tm n) (Univ m) by eauto using join_transitive.
      subst.
      move /InterpExt_Univ_inv. firstorder.
  - move => A A0 PA h.
    have /join_symmetric {}h : join A A0 by hauto lq:on ctrs:rtc use:RPar_Par, relations.rtc_once.
    eauto using join_transitive.
Qed.

Lemma InterpUniv_Bind_inv n p i  (A : Tm n) B P
  (h :  ⟦ TBind p A B ⟧ i ↘ P) :
  exists (PA : Tm n -> Prop) (PF : Tm n -> (Tm n -> Prop) -> Prop),
     ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) /\
    P = BindSpace p PA PF.
Proof. hauto l:on use:InterpExt_Bind_inv rew:db:InterpUniv. Qed.

Lemma InterpUniv_Univ_inv n i j P
  (h :  ⟦ @Univ n j  ⟧ i ↘ P) :
  P = (fun (A : Tm n) => exists PA, ⟦ A ⟧ j ↘ PA) /\ j < i.
Proof. hauto l:on use:InterpExt_Univ_inv rew:db:InterpUniv. Qed.

Lemma InterpExt_Functional n i I (A B : Tm n) PA PB :
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PB ->
  PA = PB.
Proof. hauto use:InterpExt_Join, join_refl. Qed.

Lemma InterpUniv_Functional n i (A B : Tm n) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PB ->
  PA = PB.
Proof. hauto use:InterpExt_Functional rew:db:InterpUniv. Qed.

Lemma InterpExt_Bind_inv_nopf n i I p A B P (h :  ⟦TBind p A B ⟧ i ;; I ↘ P) :
  exists (PA : Tm n -> Prop),
     ⟦ A ⟧ i ;; I ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) /\
      P = BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB).
Proof.
  move /InterpExt_Bind_inv : h. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
  exists PA. repeat split => //.
  - sfirstorder.
  - extensionality b.
    case : p => /=.
    + extensionality a.
      extensionality PB.
      extensionality ha.
      apply propositional_extensionality.
      split.
      * hecrush use:InterpExt_Functional.
      * sfirstorder.
    + rewrite /SumSpace. apply propositional_extensionality.
      split; hauto q:on use:InterpExt_Functional.
Qed.

Lemma InterpUniv_Bind_inv_nopf n i p A B P (h :  ⟦TBind p A B ⟧ i ↘ P) :
  exists (PA : Tm n -> Prop),
     ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) /\
      P = BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB).
Proof. hauto l:on use:InterpExt_Bind_inv_nopf rew:db:InterpUniv. Qed.

Lemma InterpExt_back_clos n i I (A : Tm n) PA :
  (forall j,  forall a b, (RPar.R a b) ->  I n j b -> I n j a) ->
    ⟦ A ⟧ i ;; I ↘ PA ->
    forall a b, (RPar.R a b) ->
           PA b -> PA a.
Proof.
  move => hI h.
  elim : A PA /h.
  - move => p A B PA PF hPA ihPA hTot hRes ihPF a b hr.
    case : p => //=.
    + have  : forall b0 b1 a, RPar.R b0 b1 -> RPar.R (App b0 a) (App b1 a)
          by hauto lq:on ctrs:RPar.R use:RPar.refl.
      hauto lq:on rew:off unfold:ProdSpace.
    + hauto lq:on ctrs:rtc unfold:SumSpace.
  - eauto.
  - eauto.
Qed.

Lemma InterpUniv_back_clos n i (A : Tm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, (RPar.R a b) ->
           PA b -> PA a.
Proof.
  simp InterpUniv.
  apply InterpExt_back_clos.
  hauto lq:on ctrs:rtc use:InterpUnivN_back_preservation_star.
Qed.

Lemma InterpUniv_back_clos_star n i (A : Tm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, rtc RPar.R a b ->
           PA b -> PA a.
Proof.
  move => h  a b.
  induction 1=> //.
  hauto lq:on use:InterpUniv_back_clos.
Qed.

Definition ρ_ok {n} Γ (ρ : fin n -> Tm n) := forall i m PA,
  ⟦ Γ i ⟧ m ↘ PA -> PA (ρ i).

Definition SemWt {n} Γ (a A : Tm n) := forall ρ, ρ_ok Γ ρ -> forall (i : fin n), exists m PA, ⟦ subst_Tm ρ (Γ i) ⟧ m ↘ PA.
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

(* Semantic context wellformedness *)
Definition SemWff {n} Γ := forall (i : fin n), exists j, Γ ⊨ Γ i ∈ Univ j.
Notation "⊨ Γ" := (SemWff Γ) (at level 70).

Lemma ρ_ok_nil ρ :
  ρ_ok null ρ.
Proof.  rewrite /ρ_ok. inversion i; subst. Qed.

Lemma ρ_ok_cons n i (Γ : fin n -> Tm n) ρ a PA A :
  ⟦ subst_Tm ρ A ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (funcomp (ren_Tm shift) (scons A Γ)) (funcomp (ren_Tm shift) (scons a ρ)).
