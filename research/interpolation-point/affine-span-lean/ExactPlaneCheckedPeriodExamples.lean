import ExactPlaneCheckedPeriod
namespace ExactPlaneCheckedPeriodExamples
open ExactPlaneSparseANF
open ExactPlaneProfileSolver (Selectors)
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def selector : Selectors 1 1 4 := fun _ i =>
  let x : Form (Fin 2) := {{0}}
  let y : Form (Fin 2) := {{1}}
  let one : Form (Fin 2) := {∅}
  times (if i.val%2=0 then plus one x else x) (if i.val<2 then plus one y else y)
private def priv (_ : Fin 4) : Key 1 := fun _=>1
private def tag (i : Fin 4) : Plane := (if i.val%2=0 then 0 else 1,if i.val<2 then 0 else 1)
private def gain (i : Fin 4) : Plane := if i.val=3 then (1,0) else 0
private def allZero : Fin 0→ExactPlaneProfileCharts.X 1 := Fin.elim0
private def flipY (_ : Fin 1) : ExactPlaneProfileCharts.X 1 := ![0,1]
#eval ExactPlaneSuppliedPeriods.valid selector gain allZero
#eval ExactPlaneSuppliedPeriods.valid selector gain flipY
#eval ExactPlaneSuppliedPeriods.valid selector (fun _=>0) flipY
#eval ExactPlaneCheckedPeriod.usePeriod allZero selector priv gain
#eval ExactPlaneCheckedPeriod.usePeriod allZero selector priv 0
#eval ExactPlanePeriodChoice.periodCount 2 0 2
#eval ExactPlanePeriodChoice.degreeCount 2 0 0
private def zpriv (_ : Fin 3) : Key 0 := Fin.elim0
private def zh (i : Fin 3) : Plane := if i=2 then (1,0) else (0,1)
#eval (ExactPlaneCheckedPeriod.solve (Fin.elim0 : Fin 0→ExactPlaneProfileCharts.X 0)
  (Fin.elim0 : Selectors 0 0 3) zpriv 0 zh).map (fun q=>q.2.card)
private def six : Selectors 1 1 6 := fun j i=>if hi : i.val<4 then selector j ⟨i.val,hi⟩ else ∅
private def keys6 (i : Fin 6) : Key 1 := fun _=>if i.val<4 then 1 else 0
private def tags6 (i : Fin 6) : Plane := if hi : i.val<4 then tag ⟨i.val,hi⟩ else 0
private def heights6 (i : Fin 6) : Plane := if i=4 then (1,0) else if i=5 then (0,1) else 0
private def allPeriods (i : Fin 2) : ExactPlaneProfileCharts.X 1 := fun j=>if i=j then 1 else 0
#eval ExactPlaneSuppliedPeriods.codim allPeriods
#eval ExactPlaneRawSectionCheck.valid keys6 tags6 six
#eval ExactPlaneCheckedPeriod.usePeriod allPeriods six keys6 heights6
end ExactPlaneCheckedPeriodExamples
