import ExactPlaneWedgeRun
namespace ExactPlaneWedgeRunExamples
open ExactPlaneWedgePlan ExactPlaneWedgeCodec ExactPlaneWedgeRun ExactPlaneResidualPivots
def zcut : Cut 1 := ⟨0,Fin.elim0⟩
def ecut : Cut 1 := ⟨1,fun _ _=>1⟩
def small : Indexed 1 2 := .join (.leaf 0 zcut) (.leaf 1 zcut) zcut
def height (i : Fin 2) : Plane := if i=0 then (1,0) else (0,1)
#eval (solve small (fun _=>0) (fun _=>0) height).map (fun (u,v)=>(u.sort (·≤·),v.sort (·≤·)))
#eval (solve small (fun _=>0) (fun i=>if i=0 then (1,0) else 0) height).isSome
def pairTree : Indexed 1 4 :=
  .join (.join (.leaf 0 ecut) (.leaf 1 ecut) ecut)
        (.join (.leaf 2 ecut) (.leaf 3 ecut) ecut) zcut
def gains (i : Fin 4) : Plane := if i=0 then (1,0) else if i=2 then (0,1) else 0
#eval (solve pairTree (fun _ _=>1) (fun _=>0) gains).isSome
#eval (solve pairTree (fun _ _=>1) (fun i=>if i.val<2 then 0 else (1,0)) gains).isSome
end ExactPlaneWedgeRunExamples
