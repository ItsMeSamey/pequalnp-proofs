import ExactPlaneSemanticProfile
import ExactPlaneCheckedProfileExamples
namespace IndependentProfileAudit
open ExactPlaneSparseANF ExactPlaneProfileSolver ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def bad : Selectors 0 1 3 := fun _ _=>∅
private def p (_ : Fin 3) : Key 0 := Fin.elim0
private def b (_ : Fin 3) : Plane := 0
private def h (i : Fin 3) : Plane := if i=2 then (1,0) else (0,1)
#eval ExactPlaneRawSectionCheck.valid p b bad
#eval (ExactPlaneCheckedProfile.solve bad p b h).map (fun a=>a.2.card)
#eval (ExactPlaneCheckedProfile.solve bad p b 0).isSome
#eval (List.range 5).map (fun D => (ExactPlaneDegreeSampler.ordered [false,true] D).length)
end IndependentProfileAudit
