nat  : Type
Tm(VarTm) : Type
PTag : Type

PL : PTag
PR : PTag
Abs : (bind Tm in Tm) -> Tm
App : Tm -> Tm -> Tm
Pair : Tm -> Tm -> Tm
Proj : PTag -> Tm -> Tm
Pi : Tm -> (bind Tm in Tm) -> Tm
Bot : Tm
Univ : nat -> Tm