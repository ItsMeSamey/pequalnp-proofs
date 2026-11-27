import ExactPlaneCheckedProfile
namespace ExactPlaneCheckedProfileExamples
open ExactPlaneSparseANF
open ExactPlaneProfileSolver (Selectors)
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def selector : Selectors 1 1 4 := fun _ i =>
  let x : Form (Fin 2) := {{0}}
  let y : Form (Fin 2) := {{1}}
  let one : Form (Fin 2) := {∅}
  let a := if i.val%2=0 then plus one x else x
  let b := if i.val<2 then plus one y else y
  times a b

private def priv (_ : Fin 4) : Key 1 := fun _=>1
private def tag (i : Fin 4) : Plane :=
  (if i.val%2=0 then 0 else 1,if i.val<2 then 0 else 1)
private def height (i : Fin 4) : Plane := if i.val=3 then (1,0) else 0
#eval ExactPlaneRawSectionCheck.valid priv tag selector
#eval ExactPlaneSparseSections.actualD selector height
#eval ExactPlaneSparseSections.actualD selector (fun _=>0)

private def emptySection : Selectors 0 0 3 := Fin.elim0
private def priv0 (_ : Fin 3) : Key 0 := Fin.elim0
private def height0 (i : Fin 3) : Plane := if i=2 then (1,0) else (0,1)
#eval (ExactPlaneCheckedProfile.solve emptySection priv0 0 height0).map (fun q=>q.2.card)
#eval (ExactPlaneCheckedProfile.solve emptySection priv0 0 0).isSome
end ExactPlaneCheckedProfileExamples
