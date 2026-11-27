import ExactPlaneFirstRankBasis
namespace ExactPlanePairSearchExamples
open ExactPlanePairSearch ExactPlaneResidualPivots
private def row (j : Fin 2) (i : Fin 4) : ZMod 2 :=
  if i.val/2=j.val then 1 else 0
private def k (i : Fin 4) : Key 2 := fun j=>if j.val=i.val/2 then 1 else 0
private def single (_ : Fin 4) : Key 2 := fun j=>if j=0 then 1 else 0
private def tags (i : Fin 4) : Plane := if i.val<2 then (1,0) else (0,1)
private def heights (i : Fin 4) : Plane := if i=1 then (1,0) else if i=3 then (0,1) else 0
#eval (pairs row).length
#eval (solve row k tags heights).map Finset.card
#eval (solve row single tags heights).isSome
end ExactPlanePairSearchExamples
