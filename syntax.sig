Tm(VarTm) : Type
-- nat : Type

Abs : (bind Tm in Tm) -> Tm
App : Tm -> Tm -> Tm
Pair : Tm -> Tm -> Tm
Proj1 : Tm -> Tm
Proj2 : Tm -> Tm
