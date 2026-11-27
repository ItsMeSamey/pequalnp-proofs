import ExactPlaneCheckedPeriod
namespace IndependentCosetAudit
open ExactPlaneSparseANF ExactPlaneProfileSolver ExactPlaneProfileCharts
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def wrong : Selectors 0 1 4 := fun _ _=>∅
private def p (_ : Fin 4) : Key 0 := Fin.elim0
private def z : Fin 1→X 0 := fun _=>Fin.elim0
private def h : Fin 4→Plane := ![(1,0),(1,0),(0,1),(0,0)]
private def diag : Fin 2→X 1 := ![![1,1],![1,1]]
private def cos : Selectors 1 1 1 := fun _ _=>normalize [[0],[1]]
private def mon : Selectors 1 1 1 := fun _ _=>normalize [[0],[1],[0,1]]
#eval (ExactPlanePeriodChoice.preferPeriod 0 1 0 0,
       ExactPlanePeriodChoice.preferPeriod 2 0 0 2)
#eval (ExactPlaneSuppliedPeriods.codim diag,
       ExactPlaneSuppliedPeriods.valid cos (fun _=>(0,1)) diag,
       ExactPlaneSuppliedPeriods.valid mon (fun _=>(0,1)) diag)
#eval (ExactPlaneRawSectionCheck.valid p 0 wrong,
      (ExactPlaneCheckedPeriod.solve z wrong p 0 h).map (fun x=>x.2.card),
      (ExactPlaneCheckedPeriod.solve z wrong p 0 (fun _=>(1,0))).isSome)
end IndependentCosetAudit
