import ExactPlaneWedgeFused
namespace ExactPlaneWedgeFusedExamples
open ExactPlaneWedgeTree ExactPlaneWedgeCodec ExactPlaneWedgeRun ExactPlaneResidualPivots
def two : Tree 2 := .join (.leaf 0) (.leaf 1)
def four : Tree 4 := .join (.join (.leaf 0) (.leaf 1)) (.join (.leaf 2) (.leaf 3))
def gains (i : Fin 4) : Plane := if i=0 then (1,0) else if i=2 then (0,1) else 0
def key (i : Fin 4) : Word 1 := fun _ => 1
def masks (uv : Finset (Fin 4) × Finset (Fin 4)) := (uv.1.sort (·≤·),uv.2.sort (·≤·))
#eval (ExactPlaneWedgeFused.solve four key (fun _=>0) gains).map masks
#eval (ExactPlaneWedgeFused.solve four key (fun i=>if i.val < 2 then 0 else (1,0)) gains).isSome
#eval (ExactPlaneWedgeFused.solve two (fun _=> (0:Word 0)) (fun _=>0) (fun i=>if i=0 then (1,0) else (0,1))).isSome
end ExactPlaneWedgeFusedExamples
