import ExactPlaneWedgeFused
namespace IndependentTree98
open ExactPlaneWedgeTree ExactPlaneWedgeCodec ExactPlaneResidualPivots
def six : Tree 6 := .join (.join (.join (.leaf 0) (.leaf 1)) (.join (.leaf 2) (.leaf 3))) (.join (.leaf 4) (.leaf 5))
def key (conflict : Bool) (i : Fin 6) : Word 8 := fun j =>
  if j.val=(if i.val<2 then 7 else if i.val<4 then (if conflict then 7 else 5) else i.val-4) then 1 else 0
def tags (i : Fin 6) : Plane := if i.val<2 then 0 else (1,0)
def gains (i : Fin 6) : Plane := if i=0 then (1,0) else if i=2 then (0,1) else 0
def result (conflict : Bool) :=
  (ExactPlaneWedgeFused.solve six (key conflict) tags gains).map fun uv => (uv.1∪uv.2).sort (·≤·)
#eval result true
#eval result false
end IndependentTree98
