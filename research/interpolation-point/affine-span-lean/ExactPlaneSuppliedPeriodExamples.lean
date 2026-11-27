import ExactPlaneSuppliedPeriods
namespace ExactPlaneSuppliedPeriodExamples
open ExactPlaneSparseANF ExactPlaneProfileSolver ExactPlaneProfileCharts ExactPlaneResidualPivots
open ExactPlaneSuppliedPeriods

/-- x₀+x₁ is invariant under (1,1), even though both variables occur. -/
private def rows : Selectors 1 1 1 := fun _ _=>normalize [[0],[1]]
private def h : Fin 1→Plane := fun _=>(1,0)
private def redundant : Fin 3→X 1 := ![![1,1],![0,0],![1,1]]
private def bad : Fin 1→X 1 := ![![0,1]]
#eval (valid rows h redundant,codim redundant,valid rows h bad)
example : valid rows h redundant=true ∧ codim redundant=1 ∧ valid rows h bad=false := by
  native_decide
end ExactPlaneSuppliedPeriodExamples
