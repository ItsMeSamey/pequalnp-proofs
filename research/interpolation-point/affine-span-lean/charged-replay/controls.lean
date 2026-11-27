import ExactPlaneChargedSolver
import ExactPlaneChargedSites
import ExactPlaneDeficitCharged
import ExactPlaneChargedGenerator
import ExactPlaneDeficitScan
import ExactPlaneChargedOdd
import ExactPlaneEagerCounts
import ExactPlaneChargedScan
import ExactPlaneModulusCharges
import ExactPlaneSeedWork
namespace IndependentCharges
private def r := ExactPlaneModulusCharges.allCount (fun n : Nat => (decide (n≠2), n+1)) [0,2,99]
#eval r
example : r = (false,4) := by native_decide
private def base := ExactPlaneEagerField.store (fun _ : Fin 2 => 1)
private def test := ExactPlaneSeedWork.counted 3 base
#eval (test.tables,test.multiplications,test.dots,test.rows.length)
example : (test.tables,test.multiplications,test.dots,test.rows.length) = (4,12,48,16) := by native_decide
end IndependentCharges
namespace IndependentCharges
private def keys (_ : Fin 2) : Fin 0→ZMod 2 := Fin.elim0
private def gains : Fin 2→ExactPlaneResidualPivots.Plane := ![(1,0),(0,1)]
#eval ExactPlaneEagerCounts.checkC [0,1] keys 0 gains
example : ExactPlaneEagerCounts.checkC [0,1] keys 0 gains=(true,11) := by native_decide
#eval (ExactPlaneEagerCounts.basisC Finset.univ keys 0 gains).2
example : (ExactPlaneEagerCounts.basisC Finset.univ keys 0 gains).2=2 := by native_decide
private def odd := ExactPlaneChargedOdd.counted ([1,1] : List Nat)
#eval (odd.emitted,odd.terms)
example : (odd.emitted,odd.terms)=(42,186) := by native_decide
end IndependentCharges
namespace IndependentCharges
private def pass := ExactPlaneChargedSites.run [0,0] keys 0 gains
private def miss := ExactPlaneChargedSites.run [0,0] keys 0 0
#eval (pass.tested,pass.siteTests,pass.checkPivots,pass.recovered,pass.basisPivots)
example : (pass.tested,pass.siteTests,pass.checkPivots,pass.recovered,pass.basisPivots)
    = (1,2,11,1,2) := by native_decide
example : (miss.tested,miss.siteTests,miss.checkPivots,miss.recovered,miss.basisPivots)
    = (2,4,0,0,0) := by native_decide
private def g0 := ExactPlaneChargedGenerator.run 0 10
example : (g0.rows.length,g0.modulusCandidates,g0.baseTables)=(1,0,0) := by native_decide
end IndependentCharges
namespace IndependentCharges
private def raw := ExactPlaneChargedSolver.run keys 0 gains
example : (raw.field.seedRows,raw.emitted,raw.terms,raw.search.tested,raw.search.siteTests) = (1,3,9,1,2) := by native_decide
end IndependentCharges
