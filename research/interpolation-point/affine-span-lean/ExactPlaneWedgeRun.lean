import ExactPlaneWedgePlan
import ExactPlaneWedgeLeaf
import ExactPlaneFeatureSelect
import ExactPlaneWedgeDecision
namespace ExactPlaneWedgeRun
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgePlan ExactPlaneWedgeArrayDP
open ExactPlaneWedgeDecision ExactPlaneResidualPivots ExactPlanePhysicalWedgeTree
open ExactPlaneFeatureStream (selectFeatures selectFeatures_spec)
variable {d n : Nat}
def inputs (k : Fin n→Word d) (b : Fin n→Plane) : LeafRows d n :=
  fun i c s => ExactPlaneWedgeLeaf.leaf i k b c.columns s
def first (c : Cut d) : Fin (size c) :=
  ⟨0,by obtain ⟨j,_⟩ := has_code c (zero _); exact lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩
def rows (t : Indexed d n) (k : Fin n→Word d) (b : Fin n→Plane) : Rows n :=
  (run selectFeatures (plan (inputs k b) t))[first (cut t)]
def solve (t : Indexed d n) (k : Fin n→Word d) (b h : Fin n→Plane) : Option (Sites n × Sites n) :=
  find h (rows t k b)

theorem select_law (xs : Rows n) :
    items (selectFeatures xs)⊆items xs ∧ Submodule.span F (items (selectFeatures xs))=Submodule.span F (items xs) :=
  ⟨(selectFeatures_spec xs).1.subset,(selectFeatures_spec xs).2.2.2.1⟩

end ExactPlaneWedgeRun
