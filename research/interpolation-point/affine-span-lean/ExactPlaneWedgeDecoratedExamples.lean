import ExactPlaneWedgeRawTree

namespace ExactPlaneWedgeDecoratedExamples
open ExactPlaneWedgeTree ExactPlaneWedgeRun ExactPlaneResidualPivots ExactPlaneWedgeCodec

def sample : Tree 3 := .join (.leaf 0) (.join (.leaf 1) (.leaf 2))
def keys (_ : Fin 3) : Word 2 := fun j => if j=0 then 1 else 0
def heights (i : Fin 3) : Plane :=
  if i=0 then (1,0) else if i=1 then (0,1) else 0

-- All three private keys coincide. The two independent even relations can share a site.
#eval (raw sample keys (fun _ => 0) heights).map
  (fun (u,v) => (u.sort (·≤·),v.sort (·≤·)))
-- Duplicating a complete column leaves just one independent height difference.
#eval (raw sample keys (fun _ => 0) (fun i => if i=0 then (1,0) else 0)).isSome
end ExactPlaneWedgeDecoratedExamples
