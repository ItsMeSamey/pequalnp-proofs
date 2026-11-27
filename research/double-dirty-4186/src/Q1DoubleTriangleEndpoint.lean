import Q1DoubleTripleEndpoint
import Q1DoubleTriangleCover

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

def rowEdges {n r : ℕ} (pt : Fin r → Bool → Fin n) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun i => s(pt i false, pt i true))

theorem coversRowEdges {n r : ℕ} (pt : Fin r → Bool → Fin n) (F : Finset (Fin n))
    (meets : ∀ i, ∃ b, pt i b ∈ F) : OneLeak.covers F (rowEdges pt) := by
  intro u v he
  obtain ⟨i,_,eq⟩ := Finset.mem_image.mp he
  obtain ⟨b,hb⟩ := meets i
  have member : pt i b ∈ s(u,v) := by
    rw [← eq]
    cases b
    · exact Sym2.mem_mk_left _ _
    · exact Sym2.mem_mk_right _ _
  rcases Sym2.mem_iff.mp member with hu | hv
  · exact Or.inl (hu ▸ hb)
  · exact Or.inr (hv ▸ hb)

theorem rowEdges_card {n r : ℕ} (pt : Fin r → Bool → Fin n) : (rowEdges pt).card ≤ r := by
  simpa only [rowEdges,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_image_le (s := Finset.univ) (f := fun i => s(pt i false,pt i true)))

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
