import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A two-point assignment meets every primitive clause of the local top. -/
def hitsPair (clauses : Finset (Finset (Fin n))) (a b : Fin n) : Prop :=
  ∀ K ∈ clauses, a ∈ K ∨ b ∈ K

/-- A clause containing two distinct inputs has a star center covering all its inputs. -/
def clauseStars (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (clauses : Finset (Finset (Fin n))) : Prop :=
  ∀ K ∈ clauses, ∀ p ∈ K, ∀ q ∈ K, p ≠ q →
    ∃ w, ∀ z ∈ K, G.Adj w z ∧ s(w,z) ∈ starEdges G C

private theorem uniqueCenter (h4 : NoFourCycle G) {w x p q : Fin n} (hne : p ≠ q)
    (hwp : G.Adj w p) (hwq : G.Adj w q) (hxp : G.Adj x p) (hxq : G.Adj x q) : w = x := by
  by_contra hwx
  apply hne
  apply Finset.card_le_one.mp (h4 w x hwx) p _ q _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwp, hxp⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq, hxq⟩

variable {clauses : Finset (Finset (Fin n))}

/-- The lambda center and the common ambient neighbor would coincide, starring xp. -/
private theorem noTogether (h4 : NoFourCycle G) (hs : clauseStars G C clauses)
    {x p q : Fin n} (hne : p ≠ q) (hxp : G.Adj x p) (hxq : G.Adj x q)
    (hr : s(x,p) ∈ Ustar G C) {K} (hK : K ∈ clauses) (hp : p ∈ K) (hq : q ∈ K) : False := by
  obtain ⟨w, hw⟩ := hs K hK p hp q hq hne
  have he := uniqueCenter h4 hne (hw p hp).1 (hw q hq).1 hxp hxq
  exact (Finset.mem_sdiff.mp hr).2 (he ▸ (hw p hp).2)

/-- Accepted residual edges at the same endpoint have the same other endpoint. -/
theorem matching_unique (h4 : NoFourCycle G) (hs : clauseStars G C clauses)
    (clean : ∀ a b, hitsPair clauses a b → G.Adj a b) {x y z : Fin n}
    (hxy : hitsPair clauses x y) (hxz : hitsPair clauses x z)
    (hr : s(x,y) ∈ Ustar G C) : y = z := by
  by_contra hyz
  apply G.loopless.irrefl x
  apply clean x x
  intro K hK
  by_cases hx : x ∈ K
  · exact Or.inl hx
  · exact False.elim (noTogether h4 hs hyz (clean _ _ hxy) (clean _ _ hxz) hr hK
      ((hxy K hK).resolve_left hx) ((hxz K hK).resolve_left hx))

/-- Disjoint accepted residual edges have no ambient cross-edge between the designated
    first endpoints. Swapping either edge yields all four cross-edge exclusions. -/
theorem matching_induced (h4 : NoFourCycle G) (hs : clauseStars G C clauses)
    (clean : ∀ a b, hitsPair clauses a b → G.Adj a b) {x p y q : Fin n}
    (hxp : hitsPair clauses x p) (hyq : hitsPair clauses y q)
    (rx : s(x,p) ∈ Ustar G C) (ry : s(y,q) ∈ Ustar G C)
    (hxy : x ≠ y) (hpy : p ≠ y) (hqx : q ≠ x) (hpq : p ≠ q) : ¬ G.Adj x y := by
  intro hadj
  have hxq : hitsPair clauses x q := by
    intro K hK
    by_cases hx : x ∈ K
    · exact Or.inl hx
    · by_cases hq : q ∈ K
      · exact Or.inr hq
      · exact False.elim (noTogether h4 hs hpy (clean _ _ hxp) hadj rx hK
          ((hxp K hK).resolve_left hx) ((hyq K hK).resolve_right hq))
  have hyp : hitsPair clauses y p := by
    intro K hK
    by_cases hy : y ∈ K
    · exact Or.inl hy
    · by_cases hp : p ∈ K
      · exact Or.inr hp
      · exact False.elim (noTogether h4 hs hqx (clean _ _ hyq) (G.adj_symm hadj) ry hK
          ((hyq K hK).resolve_left hy) ((hxp K hK).resolve_right hp))
  exact hxy (uniqueCenter h4 hpq (clean _ _ hxp) (clean _ _ hxq) (clean _ _ hyp) (clean _ _ hyq))

end PEqualNP.Outside.L_meta_4186_aux.Q0
