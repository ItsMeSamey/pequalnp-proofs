import ExactPlanePhysicalIntersection
namespace ExactPlaneIntersectionExamples
open ExactPlanePhysicalIntersection ExactPlaneWedgeProduct
private def keys : Fin 4 → V 2 := ![![1,0],![0,1],![1,1],![1,1]]

-- The only nonzero common key is a combination of the two left columns.
#guard rows keys {0,1} {2,3} = [![1,1]]
#guard rows keys {0} {1} = []
#guard rows keys ∅ Finset.univ = []
#guard (rows keys Finset.univ Finset.univ).length = 2
end ExactPlaneIntersectionExamples
