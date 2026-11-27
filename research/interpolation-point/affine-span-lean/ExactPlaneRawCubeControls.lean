import ExactPlaneSmallChartFallback
namespace ExactPlaneRawCubeControls
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots ExactPlaneComputedDeficit
private def keys (_ : Fin 4) : Key 3 := ![0,1,0]
private def tags (_ : Fin 4) : Plane := (1,0)
-- Sites 0 and 3 are physically identical.
private def heights : Fin 4 → Plane := ![(0,0),(1,0),(0,1),(0,0)]
private def result := (ExactPlaneSmallChartFallback.direct keys tags heights).map fun answer =>
  let ids := answer.2.sort (·≤·)
  (ids.map Fin.val, answer.2.card, ExactPlaneEagerBank.check ids keys tags heights)
private def collapsed : Fin 4 → Plane := ![(0,0),(1,0),(1,0),(0,0)]
#eval (keyRank keys Finset.univ, computed keys tags, result,
  (ExactPlaneSmallChartFallback.direct keys tags collapsed).isSome)
example : keyRank keys Finset.univ = 1 ∧ computed keys tags = 1 ∧
    result = some ([1,2,3],3,true) ∧
    (ExactPlaneSmallChartFallback.direct keys tags collapsed).isSome = false := by native_decide
end ExactPlaneRawCubeControls
