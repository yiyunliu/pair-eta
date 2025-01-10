nat  : Type
Tm(VarTm) : Type
PTag : Type
TTag : Type
bool : Type

TPi : TTag
TSig : TTag
PL : PTag
PR : PTag
Abs : (bind Tm in Tm) -> Tm
App : Tm -> Tm -> Tm
Pair : Tm -> Tm -> Tm
Proj : PTag -> Tm -> Tm
TBind : TTag -> Tm -> (bind Tm in Tm) -> Tm
Bot : Tm
Univ : nat -> Tm
Bool : Tm
BVal : bool -> Tm
If : Tm -> Tm -> Tm -> Tm