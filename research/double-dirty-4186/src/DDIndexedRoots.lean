import DDIndexedPrefix
import Q1DoubleSplitActual
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor
attribute [local instance] gateOpDecEq
def rootIndices (n : ℕ) (C : Circuit) (p : Cuts) (external : Finset ℕ) : Finset ℕ :=
  insert (rank n C p C.size) (insert (rank n C p C.size+1) (external.image (rank n C p)))

theorem root_card (n : ℕ) (C : Circuit) (p : Cuts) (external : Finset ℕ) :
    (rootIndices n C p external).card ≤ external.card + 2 := by
  have h₀ := Finset.card_image_le (f:=rank n C p) (s:=external)
  have h₁ := Finset.card_insert_le (rank n C p C.size+1) (external.image (rank n C p))
  have h₂ := Finset.card_insert_le (rank n C p C.size)
    (insert (rank n C p C.size+1) (external.image (rank n C p)))
  unfold rootIndices;omega

theorem root_budget {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (external : Finset ℕ) (budget : external.card ≤ (orT G C).card) (a b w : ℕ) :
    let p := splitCuts n C (orT G C) m
    (capPrefix n C p C.size a b w).size + (rootIndices n C p external).card ≤ C.size+2 := by
  let p := splitCuts n C (orT G C) m
  have hcap : (capPrefix n C p C.size a b w).size = rank n C p C.size+2 := by
    simp [capPrefix,Circuit.size,rank]
  have cost := mixer_split_budget d edge least
  have eq := rank_expense C p least.1 C.size le_rfl
  have size := root_card n C p external
  change (capPrefix n C p C.size a b w).size + (rootIndices n C p external).card ≤ _
  change expense (seed n) (rows n C p C.size) + 2 + _ ≤ _ at cost
  omega
theorem root_valid {n : ℕ} {C : Circuit} {p : Cuts} {E : Finset ℕ}
    (ext : E ⊆ Finset.range C.size) (a b w : ℕ) {t : ℕ} (h : t ∈ rootIndices n C p E) :
    t < (capPrefix n C p C.size a b w).size := by
  have hcap : (capPrefix n C p C.size a b w).size = rank n C p C.size+2 := by
    simp [capPrefix,Circuit.size,rank]
  rw [hcap]
  rcases Finset.mem_insert.mp h with rfl | h
  · omega
  rcases Finset.mem_insert.mp h with rfl | h
  · omega
  obtain ⟨j,mem,rfl⟩ := Finset.mem_image.mp h
  have le := rank_mono (n:=n) C p (Nat.le_of_lt (Finset.mem_range.mp (ext mem)))
  omega
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
