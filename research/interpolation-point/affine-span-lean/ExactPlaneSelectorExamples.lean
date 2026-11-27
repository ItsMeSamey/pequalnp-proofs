import ExactPlaneExecutableCompression
namespace ExactPlaneSelectorExamples
open ExactPlaneExecutableSelector ExactPlaneResidualPivots
private def zeroKey (_ : Fin 3) : ZMod 2 := 0
private def zeroTag (_ : Fin 3) : Plane := 0
private def high (i : Fin 3) : Plane := if i=2 then (0,1) else (1,0)
private def miss (_ : Fin 3) : Plane := (1,1)
private def hit (_ : Fin 3) : Plane := 0
#eval (select (fun (g : Fin 3→Plane) i=>g i) zeroKey zeroTag high [miss,hit]).map (fun v=>v.2.card)
#eval (runCompact [hit] zeroKey zeroTag high).map (fun v=>v.2.card)
#eval (run [miss,hit] zeroKey zeroTag (fun _=>(1,0))).isSome
end ExactPlaneSelectorExamples
