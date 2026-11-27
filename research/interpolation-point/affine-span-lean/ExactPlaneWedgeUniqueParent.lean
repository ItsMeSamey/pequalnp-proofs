import ExactPlaneWedgeSplit
namespace ExactPlaneWedgeUniqueParent
open ExactPlaneWedgeSplit ExactPlaneWedgeProduct ExactPlaneWedgeBoundary
variable {K B : Type*} [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]

theorem unique_parent (L R E : Submodule F K) {s t : State (parentBoundary L R E) B}
    {l : State (leftBoundary L R E) B} {r : State (rightBoundary L R E) B}
    (a : Compatible L R E s l r) (b : Compatible L R E t l r) : s=t := by
  have ch : s.chart=t.chart := by
    ext x
    obtain ⟨u,v,eq⟩ := parent_parts L R E x
    exact (a.outer u v x eq).symm.trans (b.outer u v x eq)
  have p : s.p=t.p := Subtype.ext (a.p.symm.trans b.p)
  have q : s.q=t.q := Subtype.ext (a.q.symm.trans b.q)
  cases s
  cases t
  congr
#print axioms unique_parent
end ExactPlaneWedgeUniqueParent
