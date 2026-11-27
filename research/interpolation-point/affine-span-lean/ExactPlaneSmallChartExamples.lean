import ExactPlaneSmallChartFallback
namespace ExactPlaneSmallChartExamples
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def p : Fin 3 → Key 1 := fun _ _ => 1
private def b : Fin 3 → Plane := fun _ => (1,0)
private def h : Fin 3 → Plane := ![(0,0),(1,0),(0,1)]
private def yes := (ExactPlaneSmallChartFallback.solve p b h).map (fun result => result.2.card)
private def no := (ExactPlaneSmallChartFallback.solve p b (fun _ => (0,0))).isSome
#eval (yes,no)
example : yes=some 3 ∧ no=false := by native_decide
end ExactPlaneSmallChartExamples
