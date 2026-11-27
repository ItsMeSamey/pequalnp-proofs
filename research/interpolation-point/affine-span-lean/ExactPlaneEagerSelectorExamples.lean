import ExactPlaneEagerDecision
namespace ExactPlaneEagerSelectorExamples
open ExactPlaneEagerSelector ExactPlaneResidualPivots
private def key0 (_ : Fin 3) : Key 0 := fun i=>Fin.elim0 i
private def z (_ : Fin 3) : Plane := 0
private def bad (_ : Fin 3) : Plane := (1,1)
private def heights (i : Fin 3) : Plane := if i=2 then (0,1) else (1,0)
#eval (selectCharts [bad,z] key0 z heights).map (fun x=>x.2.card)
#eval (runBasis [z] key0 z heights).map (fun x=>x.2.card)
#eval (runBasis [bad,z] key0 z (fun _=>(1,0))).isSome
private def key1 (_ : Fin 3) : Key 1 := fun _=>1
private def independentHeights (i : Fin 3) : Plane :=
  if i=0 then (0,0) else if i=1 then (1,0) else (0,1)
#eval (runBasis [z] key1 z independentHeights).map (fun x=>x.2.card)
#eval (runPacked [Vector.ofFn z] (Vector.ofFn fun i => Vector.ofFn (key1 i)) (Vector.ofFn z) (Vector.ofFn independentHeights)).map (fun x=>x.2.card)
end ExactPlaneEagerSelectorExamples
