import ExactPlaneChargedSolver
namespace ExactPlaneChargedExamples
open ExactPlaneChargedSolver ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
private def key0 {N : Nat} (_ : Fin N) : Key 0 := Fin.elim0
private def good (i : Fin 3) : Plane := if i=0 then (0,1) else (1,0)
private def data (o : Output N) := (o.field.modulusCandidates,o.field.seedRows,o.emitted,o.terms,
  o.search.tested,o.search.siteTests,o.search.recovered,o.search.answer.map (fun a=>a.2.card))
#eval data (run (N:=0) key0 0 0)
#eval data (run (N:=3) key0 0 good)
#eval data (run (N:=3) key0 0 0)
end ExactPlaneChargedExamples
