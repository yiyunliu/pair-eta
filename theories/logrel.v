Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..), rtc_subrel).
Import Psatz.
Definition ProdSpace (PA : Tm 0 -> Prop)
  (PF : Tm 0 -> (Tm 0 -> Prop) -> Prop) b : Prop :=
  forall a PB, PA a -> PF a PB -> PB (App b a).

Definition SumSpace (PA : Tm 0 -> Prop)
  (PF : Tm 0 -> (Tm 0 -> Prop) -> Prop) t : Prop :=
  exists a b, rtc RPar.R t (Pair a b) /\ PA a /\ (forall PB, PF a PB -> PB b).

Definition BindSpace p := if p is TPi then ProdSpace else SumSpace.

Reserved Notation "⟦ A ⟧ i ;; I ↘ S" (at level 70).
Inductive InterpExt i (I : nat -> Tm 0 -> Prop) : Tm 0 -> (Tm 0 -> Prop) -> Prop :=
| InterpExt_Bind p A B PA PF :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB) ->
  ⟦ TBind p A B ⟧ i ;; I ↘ BindSpace p PA PF

| InterpExt_Univ j :
  j < i ->
  ⟦ Univ j ⟧ i ;; I ↘ (I j)

| InterpExt_Step A A0 PA :
  RPar.R A A0 ->
  ⟦ A0 ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PA
where "⟦ A ⟧ i ;; I ↘ S" := (InterpExt i I A S).

Lemma InterpExt_Univ'  i  I j (PF : Tm 0 -> Prop) :
  PF = I j ->
  j < i ->
  ⟦ Univ j ⟧ i ;; I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Infix "<?" := Compare_dec.lt_dec (at level 60).

Equations InterpUnivN (i : nat) : Tm 0 -> (Tm 0 -> Prop) -> Prop by wf i lt :=
  InterpUnivN i := @InterpExt i
                     (fun j A =>
                        match j <? i  with
                        | left _ => exists PA, InterpUnivN  j A PA
                        | right _ => False
                        end).
Arguments InterpUnivN .

Lemma InterpExt_lt_impl i I I' A (PA : Tm 0 -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI h.
  elim : A PA /h.
  - hauto lq:on rew:off ctrs:InterpExt.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_eq i I I' A (PA : Tm 0 -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA =
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI. apply propositional_extensionality.
  have : forall j, j < i -> I' j = I j by sfirstorder.
  firstorder using InterpExt_lt_impl.
Qed.

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

Lemma InterpUnivN_nolt i :
  InterpUnivN i = InterpExt i (fun j (A : Tm 0) => exists PA, ⟦ A ⟧ j ↘ PA).
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

Lemma InterpExt_Bind_inv p i I (A : Tm 0) B P
  (h :  ⟦ TBind p A B ⟧ i ;; I ↘ P) :
  exists (PA : Tm 0 -> Prop) (PF : Tm 0 -> (Tm 0 -> Prop) -> Prop),
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

Lemma InterpExt_Univ_inv i I j P
  (h :  ⟦ Univ j  ⟧ i ;; I ↘ P) :
  P = I j /\ j < i.
Proof.
  move : h.
  move E : (Univ j) => T h. move : j E.
  elim : T P /h => //.
  - hauto l:on.
  - hauto lq:on rew:off inv:RPar.R.
Qed.

Lemma InterpExt_Bind_nopf p i I (A : Tm 0) B PA  :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘  PB) ->
  ⟦ TBind p A B ⟧ i ;; I ↘ (BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ;; I ↘ PB)).
Proof.
  move => h0 h1. apply InterpExt_Bind =>//.
Qed.

Lemma InterpUnivN_Fun_nopf p i (A : Tm 0) B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) ->
  ⟦ TBind p A B ⟧ i ↘ (BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB)).
Proof.
  hauto l:on use:InterpExt_Bind_nopf rew:db:InterpUniv.
Qed.

Lemma InterpExt_cumulative i j I (A : Tm 0) PA :
  i <= j ->
   ⟦ A ⟧ i ;; I ↘ PA ->
   ⟦ A ⟧ j ;; I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt solve+:(by lia).
Qed.

Lemma InterpUnivN_cumulative i (A : Tm 0) PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Lemma InterpExt_preservation i I (A : Tm 0) B P (h : InterpExt i I A P) :
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

Lemma InterpUnivN_preservation i (A : Tm 0) B P (h : ⟦ A ⟧ i ↘ P) :
  RPar.R A B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star i I (A : Tm 0) B P (h : ⟦ B ⟧ i ;; I ↘ P) :
  rtc RPar.R A B ->
  ⟦ A ⟧ i ;; I ↘ P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star i I (A : Tm 0) B P (h : ⟦ A ⟧ i ;; I ↘ P) :
  rtc RPar.R A B ->
  ⟦ B ⟧ i ;; I ↘ P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star i (A : Tm 0) B P (h : ⟦ A ⟧ i ↘ P) :
  rtc RPar.R A B ->
  ⟦ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star i (A : Tm 0) B P (h : ⟦ B ⟧ i ↘ P) :
  rtc RPar.R A B ->
  ⟦ A ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

Lemma InterpExtInv i I (A : Tm 0) PA :
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

Lemma RPars_Pars  (A B : Tm 0) :
  rtc RPar.R A B ->
  rtc Par.R A B.
Proof. hauto lq:on use:RPar_Par, rtc_subrel. Qed.

Lemma RPars_join  (A B : Tm 0) :
  rtc RPar.R A B -> join A B.
Proof. hauto lq:on ctrs:rtc use:RPars_Pars. Qed.

Lemma bindspace_iff  p (PA : Tm 0 -> Prop) PF PF0 b  :
  (forall (a : Tm 0) (PB PB0 : Tm 0 -> Prop), PF a PB -> PF0 a PB0 -> PB = PB0) ->
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

Lemma InterpExt_Join i I (A B : Tm 0) PA PB :
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
      have /join_univ_inj {h0 h1} ?  : join (Univ j : Tm 0) (Univ m) by eauto using join_transitive.
      subst.
      move /InterpExt_Univ_inv. firstorder.
  - move => A A0 PA h.
    have /join_symmetric {}h : join A A0 by hauto lq:on ctrs:rtc use:RPar_Par, relations.rtc_once.
    eauto using join_transitive.
Qed.

Lemma InterpUniv_Join i (A B : Tm 0) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ i ↘ PB ->
  join A B ->
  PA = PB.
Proof. hauto l:on use:InterpExt_Join rew:db:InterpUniv. Qed.

Lemma InterpUniv_Bind_inv p i  (A : Tm 0) B P
  (h :  ⟦ TBind p A B ⟧ i ↘ P) :
  exists (PA : Tm 0 -> Prop) (PF : Tm 0 -> (Tm 0 -> Prop) -> Prop),
     ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PF a PB -> ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) /\
    P = BindSpace p PA PF.
Proof. hauto l:on use:InterpExt_Bind_inv rew:db:InterpUniv. Qed.

Lemma InterpUniv_Univ_inv i j P
  (h :  ⟦ Univ j  ⟧ i ↘ P) :
  P = (fun (A : Tm 0) => exists PA, ⟦ A ⟧ j ↘ PA) /\ j < i.
Proof. hauto l:on use:InterpExt_Univ_inv rew:db:InterpUniv. Qed.

Lemma InterpExt_Functional i I (A B : Tm 0) PA PB :
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PB ->
  PA = PB.
Proof. hauto use:InterpExt_Join, join_refl. Qed.

Lemma InterpUniv_Functional i (A : Tm 0) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PB ->
  PA = PB.
Proof. hauto use:InterpExt_Functional rew:db:InterpUniv. Qed.

Lemma InterpUniv_Join' i j (A B : Tm 0) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ j ↘ PB ->
  join A B ->
  PA = PB.
Proof.
  have [? ?] : i <= max i j /\ j <= max i j by lia.
  move => hPA hPB.
  have : ⟦ A ⟧ (max i j) ↘ PA by eauto using InterpUnivN_cumulative.
  have : ⟦ B ⟧ (max i j) ↘ PB by eauto using InterpUnivN_cumulative.
  eauto using InterpUniv_Join.
Qed.

Lemma InterpUniv_Functional' i j A PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ j ↘ PB ->
  PA = PB.
Proof.
  hauto l:on use:InterpUniv_Join', join_refl.
Qed.

Lemma InterpExt_Bind_inv_nopf i I p A B P (h :  ⟦TBind p A B ⟧ i ;; I ↘ P) :
  exists (PA : Tm 0 -> Prop),
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

Lemma InterpUniv_Bind_inv_nopf i p A B P (h :  ⟦TBind p A B ⟧ i ↘ P) :
  exists (PA : Tm 0 -> Prop),
     ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB) /\
      P = BindSpace p PA (fun a PB => ⟦ subst_Tm (scons a VarTm) B ⟧ i ↘ PB).
Proof. hauto l:on use:InterpExt_Bind_inv_nopf rew:db:InterpUniv. Qed.

Lemma InterpExt_back_clos i I (A : Tm 0) PA :
  (forall j,  forall a b, (RPar.R a b) ->  I j b -> I j a) ->
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

Lemma InterpUniv_back_clos i (A : Tm 0) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, (RPar.R a b) ->
           PA b -> PA a.
Proof.
  simp InterpUniv.
  apply InterpExt_back_clos.
  hauto lq:on ctrs:rtc use:InterpUnivN_back_preservation_star.
Qed.

Lemma InterpUniv_back_clos_star i (A : Tm 0) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, rtc RPar.R a b ->
           PA b -> PA a.
Proof.
  move => h  a b.
  induction 1=> //.
  hauto lq:on use:InterpUniv_back_clos.
Qed.

Definition ρ_ok {n} Γ (ρ : fin n -> Tm 0) := forall i m PA,
  ⟦ subst_Tm ρ (Γ i) ⟧ m ↘ PA -> PA (ρ i).

Definition SemWt {n} Γ (a A : Tm n) := forall ρ, ρ_ok Γ ρ -> exists m PA, ⟦ subst_Tm ρ A ⟧ m ↘ PA /\ PA (subst_Tm ρ a).
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
  ρ_ok (funcomp (ren_Tm shift) (scons A Γ)) ((scons a ρ)).
Proof.
  move => h0 h1 h2.
  rewrite /ρ_ok.
  move => j.
  destruct j as [j|].
  - move => m PA0. asimpl => ?.
    firstorder.
  - move => m PA0. asimpl => h3.
    have ? : PA0 = PA by eauto using InterpUniv_Functional'.
    by subst.
Qed.

Definition renaming_ok {n m} (Γ : fin n -> Tm n) (Δ : fin m -> Tm m) (ξ : fin m -> fin n) :=
  forall (i : fin m), ren_Tm ξ (Δ i) = Γ (ξ i).

Lemma ρ_ok_renaming n m (Γ : fin n -> Tm n) ρ :
  forall (Δ : fin m -> Tm m) ξ,
    renaming_ok Γ Δ ξ ->
    ρ_ok Γ ρ ->
    ρ_ok Δ (funcomp ρ ξ).
Proof.
  move => Δ ξ hξ hρ.
  rewrite /ρ_ok => i m' PA.
  rewrite /renaming_ok in hξ.
  rewrite /ρ_ok in hρ.
  move => h.
  rewrite /funcomp.
  apply hρ with (m := m').
  move : h. rewrite -hξ.
  by asimpl.
Qed.

Lemma renaming_SemWt {n} Γ a A :
  Γ ⊨ a ∈ A ->
  forall {m} Δ (ξ : fin n -> fin m),
    renaming_ok Δ Γ ξ ->
    Δ ⊨ ren_Tm ξ a ∈ ren_Tm ξ A.
Proof.
  rewrite /SemWt => h m Δ ξ hξ ρ hρ.
  have /h hρ' : (ρ_ok Γ (funcomp ρ ξ)) by eauto using ρ_ok_renaming.
  hauto q:on solve+:(by asimpl).
Qed.

Lemma weakening_Sem n Γ (a : Tm n) A B i
  (h0 : Γ ⊨ B ∈ Univ i)
  (h1 : Γ ⊨ a ∈ A) :
   funcomp (ren_Tm shift) (scons B Γ) ⊨ ren_Tm shift a ∈ ren_Tm shift A.
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on inv:option unfold:renaming_ok.
Qed.

Lemma SemWt_Univ n Γ (A : Tm n) i  :
  Γ ⊨ A ∈ Univ i <->
  forall ρ, ρ_ok Γ ρ -> exists S, ⟦ subst_Tm ρ A ⟧ i ↘ S.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUniv_Univ_inv.
  - move => /[swap] ρ /[apply].
    move => [PA hPA].
    exists (S i). eexists.
    split.
    + simp InterpUniv. apply InterpExt_Univ. lia.
    + simpl. eauto.
Qed.

(* Structural laws for Semantic context wellformedness *)
Lemma SemWff_nil : SemWff null.
Proof. case. Qed.

Lemma SemWff_cons n Γ (A : Tm n) i :
    ⊨ Γ ->
    Γ ⊨ A ∈ Univ i ->
    (* -------------- *)
    ⊨ funcomp (ren_Tm shift) (scons A Γ).
Proof.
  move => h h0.
  move => j. destruct j as [j|].
  - move /(_ j) : h => [k hk].
    exists k. change (Univ k) with (ren_Tm shift (Univ k : Tm n)).
    eauto using weakening_Sem.
  - hauto q:on use:weakening_Sem.
Qed.

(* Semantic typing rules *)
Lemma ST_Var n Γ (i : fin n) :
  ⊨ Γ ->
  Γ ⊨ VarTm i ∈ Γ i.
Proof.
  move /(_ i) => [j /SemWt_Univ h].
  rewrite /SemWt => ρ /[dup] hρ {}/h [S hS].
  exists j, S.
  asimpl. firstorder.
Qed.

Lemma ST_Bind n Γ i j p (A : Tm n) (B : Tm (S n)) :
  Γ ⊨ A ∈ Univ i ->
  funcomp (ren_Tm shift) (scons A Γ) ⊨ B ∈ Univ j ->
  Γ ⊨ TBind p A B ∈ Univ (max i j).
Proof.
  move => /SemWt_Univ h0 /SemWt_Univ h1.
  apply SemWt_Univ => ρ hρ.
  move /h0 : (hρ){h0} => [S hS].
  eexists => /=.
  have ? : i <= Nat.max i j by lia.
  apply InterpUnivN_Fun_nopf.
  - eauto using InterpUnivN_cumulative.
  - move => *. asimpl. hauto l:on use:InterpUnivN_cumulative, ρ_ok_cons.
Qed.

Lemma ST_Conv n Γ (a : Tm n) A B i :
  Γ ⊨ a ∈ A ->
  Γ ⊨ B ∈ Univ i ->
  join A B ->
  Γ ⊨ a ∈ B.
Proof.
  move => ha /SemWt_Univ h h0.
  move => ρ hρ.
  have {}h0 : join (subst_Tm ρ A) (subst_Tm ρ B) by eauto using join_substing.
  move /ha : (hρ){ha} => [m [PA [h1 h2]]].
  move /h : (hρ){h} => [S hS].
  have ? : PA = S by eauto using InterpUniv_Join'. subst.
  eauto.
Qed.

Lemma ST_Abs n Γ (a : Tm (S n)) A B i :
  Γ ⊨ TBind TPi A B ∈ (Univ i) ->
  funcomp (ren_Tm shift) (scons A Γ) ⊨ a ∈ B ->
  Γ ⊨ Abs a ∈ TBind TPi A B.
Proof.
  rename a into b.
  move /SemWt_Univ => + hb ρ hρ.
  move /(_ _ hρ) => [PPi hPPi].
  exists i, PPi. split => //.
  simpl in hPPi.
  move /InterpUniv_Bind_inv_nopf : hPPi.
  move => [PA [hPA [hTot ?]]]. subst=>/=.
  move => a PB ha. asimpl => hPB.
  move : ρ_ok_cons (hPA) (hρ) (ha). repeat move/[apply].
  move /hb.
  intros (m & PB0 & hPB0 & hPB0').
  replace PB0 with PB in * by hauto l:on use:InterpUniv_Functional'.
  apply : InterpUniv_back_clos; eauto.
  apply : RPar.AppAbs'; eauto using RPar.refl.
  by asimpl.
Qed.

Lemma ST_App n Γ (b a : Tm n) A B :
  Γ ⊨ b ∈ TBind TPi A B ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ App b a ∈ subst_Tm (scons a VarTm) B.
Proof.
  move => hf hb ρ hρ.
  move /(_ ρ hρ) : hf; intros (i & PPi & hPi & hf).
  move /(_ ρ hρ) : hb; intros (j & PA & hPA & hb).
  simpl in hPi.
  move /InterpUniv_Bind_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
  have ? : PA0 = PA by eauto using InterpUniv_Functional'. subst.
  move  : hf (hb). move/[apply].
  move : hTot hb. move/[apply].
  asimpl. hauto lq:on.
Qed.

Lemma ST_Pair n Γ (a b : Tm n) A B i :
  Γ ⊨ TBind TSig A B ∈ (Univ i) ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ b ∈ subst_Tm (scons a VarTm) B ->
  Γ ⊨ Pair a b ∈ TBind TSig A B.
Proof.
  move /SemWt_Univ => + ha hb ρ hρ.
  move /(_ _ hρ) => [PPi hPPi].
  exists i, PPi. split => //.
  simpl in hPPi.
  move /InterpUniv_Bind_inv_nopf : hPPi.
  move => [PA [hPA [hTot ?]]]. subst=>/=.
  rewrite /SumSpace.
  exists (subst_Tm ρ a), (subst_Tm ρ b).
  split.
  - hauto l:on use:Pars.substing.
  - move /ha : (hρ){ha}.
    move => [m][PA0][h0]h1.
    move /hb : (hρ){hb}.
    move => [k][PB][h2]h3.
    have ? : PA0 = PA by eauto using InterpUniv_Functional'. subst.
    split => // PB0.
    move : h2. asimpl => *.
    have ? : PB0 = PB by eauto using InterpUniv_Functional'. by subst.
Qed.

Lemma ST_Proj1 n Γ (a : Tm n) A B :
  Γ ⊨ a ∈ TBind TSig A B ->
  Γ ⊨ Proj PL a ∈ A.
Proof.
  move => h ρ /[dup]hρ {}/h [m][PA][/= /InterpUniv_Bind_inv_nopf h0]h1.
  move : h0 => [S][h2][h3]?. subst.
  move : h1 => /=.
  rewrite /SumSpace.
  move => [a0 [b0 [h4 [h5 h6]]]].
  exists m, S. split => //=.
  have {}h4 : rtc RPar.R (Proj PL (subst_Tm ρ a)) (Proj PL (Pair a0 b0)) by eauto using RPars.ProjCong.
  have ? : RPar.R (Proj PL (Pair a0 b0)) a0 by hauto l:on use:RPar.refl, RPar.ProjPair'.
  have : rtc RPar.R (Proj PL (subst_Tm ρ a)) a0 by eauto using @relations.rtc_r.
  move => h.
  apply : InterpUniv_back_clos_star; eauto.
Qed.

Lemma substing_RPar n m (A : Tm (S n)) ρ (B : Tm m) C :
  RPar.R B C ->
  RPar.R (subst_Tm (scons B ρ) A) (subst_Tm (scons C ρ) A).
Proof. hauto lq:on inv:option use:RPar.morphing, RPar.refl. Qed.

Lemma substing_RPars n m (A : Tm (S n)) ρ (B : Tm m) C :
  rtc RPar.R B C ->
  rtc RPar.R (subst_Tm (scons B ρ) A) (subst_Tm (scons C ρ) A).
Proof. induction 1; hauto lq:on ctrs:rtc use:substing_RPar. Qed.

Lemma ST_Proj2 n Γ (a : Tm n) A B :
  Γ ⊨ a ∈ TBind TSig A B ->
  Γ ⊨ Proj PR a ∈ subst_Tm (scons (Proj PL a) VarTm) B.
Proof.
  move => h ρ hρ.
  move : (hρ) => {}/h [m][PA][/= /InterpUniv_Bind_inv_nopf h0]h1.
  move : h0 => [S][h2][h3]?. subst.
  move : h1 => /=.
  rewrite /SumSpace.
  move => [a0 [b0 [h4 [h5 h6]]]].
  specialize h3 with (1 := h5).
  move : h3 => [PB hPB].
  have hr : forall p, rtc RPar.R (Proj p (subst_Tm ρ a)) (Proj p (Pair a0 b0)) by eauto using RPars.ProjCong.
  have hrl : RPar.R (Proj PL (Pair a0 b0)) a0 by hauto l:on use:RPar.ProjPair', RPar.refl.
  have hrr : RPar.R (Proj PR (Pair a0 b0)) b0 by hauto l:on use:RPar.ProjPair', RPar.refl.
  exists m, PB.
  asimpl. split.
  - have h : rtc RPar.R (Proj PL (subst_Tm ρ a)) a0 by eauto using @relations.rtc_r.
    have {}h : rtc RPar.R (subst_Tm (scons (Proj PL (subst_Tm ρ a)) ρ) B) (subst_Tm (scons a0 ρ) B) by eauto using substing_RPars.
    move : hPB. asimpl.
    eauto using InterpUnivN_back_preservation_star.
  - hauto lq:on use:@relations.rtc_r, InterpUniv_back_clos_star.
Qed.
