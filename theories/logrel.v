Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Definition ProdSpace {n} (PA : Tm n -> Prop)
  (PF : Tm n -> (Tm n -> Prop) -> Prop) : Tm n -> Prop :=
  fun b => forall a PB, PA a -> PF a PB -> PB (App b a).
