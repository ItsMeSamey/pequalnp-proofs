import ExactPlaneEnumeratedFirst
namespace ExactPlaneEnumeratedFirstExamples
open ExactPlanePairSearch (Key)
open ExactPlaneResidualPivots (Plane)
private def apart (i : Fin 4) : Key 2 := fun j=>if j.val=i.val/2 then 1 else 0
private def together (_ : Fin 4) : Key 2 := fun j=>if j=0 then 1 else 0
private def tags (i : Fin 4) : Plane := if i.val<2 then (1,0) else (0,1)
private def heights (i : Fin 4) : Plane := if i=1 then (1,0) else if i=3 then (0,1) else 0
private def facts (k : Fin 4→Key 2) :=
  let accepted := ExactPlaneEnumeratedFirst.masks k tags
  let basis := ExactPlaneEnumeratedFirst.basisList accepted
  (accepted.length,basis.length,(ExactPlaneEnumeratedFirst.solve k tags heights).map (fun A=>A.sort (·≤·)))
#eval facts apart
#eval facts together
#eval (ExactPlaneEnumeratedFirst.solve (N:=0) (d:=0) Fin.elim0 Fin.elim0 Fin.elim0).isSome
end ExactPlaneEnumeratedFirstExamples
