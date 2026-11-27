import DDRootRegion
import DDFactorCone

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable abbrev leaves (n : ℕ) (C : Circuit) (r : ℕ) := occurrences n C (andRegion n C r)
def leafSupport (n : ℕ) (C : Circuit) (p : ℕ × Fin 2) := orIn n C (opnd C p.1 p.2)

theorem region_occurrences_bound {r : ℕ} (ao : IsAO2 n C) (hr : r<C.gates.length)
    (hand : (gateAt C r).op=.and) : (leaves n C r).card ≤ (andRegion n C r).card+1 :=
  occurrence_bound n C _ r (root_mem_region hr hand) (region_used ao r)

theorem region_mixer_influence {m r : ℕ} (ao : IsAO2 n C) {p : ℕ × Fin 2}
    (h : p ∈ leaves n C r) (eq : opnd C p.1 p.2 = n+m) : Influence n C m (n+r) := by
  obtain ⟨reg,pin⟩ := region_pin_mem ao h
  obtain ⟨b,_,path⟩ := in_region.mp reg
  have go {w : ℕ} (pth : AndPath n C p.1 w) :
      Influence n C m (n+p.1) → Influence n C m w := by
    induction pth with
    | source => exact id
    | step _ bound _ used ih => exact fun v => .step (ih v) bound used
  exact go path (.step .source b (eq ▸ pin))

theorem external_plain {m r : ℕ} (ao : IsAO2 n C) (external : ¬ Influence n C m (n+r)) :
    ∀ p ∈ leaves n C r, PlainWire n C m (opnd C p.1 p.2) := by
  intro p hp
  rcases region_boundary_kind (m := m) ao hp with eq | raw
  · exact (external (region_mixer_influence ao hp eq)).elim
  · exact raw

theorem arm_boundary_plain {m r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (arm : n+r ∈ (gateAt C m).inputs) :
    ∀ p ∈ leaves n C r, PlainWire n C m (opnd C p.1 p.2) := by
  have prior := ao.2.1 m (mixer_info D).1 _ arm
  exact fun _ hp => region_boundary_before ao (by omega : r ≤ m) hp

theorem leaf_semantics {m r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (form : PEqualNP.TopForm.TopForm G C) {p : ℕ × Fin 2} (hp : p ∈ leaves n C r)
    (plain : PlainWire n C m (opnd C p.1 p.2)) (x : Fin n → Bool) :
    W n C x (opnd C p.1 p.2) = true ↔ ∃ z ∈ leafSupport n C p, x z = true := by
  obtain ⟨reg,used⟩ := region_pin_mem ao hp
  obtain ⟨b,op,_⟩ := in_region.mp reg
  exact plain_pin_semantics D ao form b op used plain x

theorem region_clause_semantics {m r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (form : PEqualNP.TopForm.TopForm G C) (hr : r<C.gates.length) (hand : (gateAt C r).op=.and)
    (plain : ∀ p ∈ leaves n C r, PlainWire n C m (opnd C p.1 p.2)) (x : Fin n → Bool) :
    gateVal n C r x = true ↔ ∀ p ∈ leaves n C r, ∃ z ∈ leafSupport n C p, x z=true := by
  rw [region_eval ao hr hand x]
  exact ⟨fun h p hp => (leaf_semantics D ao form hp (plain p hp) x).mp (h p hp),
    fun h p hp => (leaf_semantics D ao form hp (plain p hp) x).mpr (h p hp)⟩

theorem region_clause_stars {m : ℕ} (D : DoubleDirty G C m) (four : NoFourCycle G)
    (least : IsLeastAO G C) (L : Finset (ℕ × Fin 2))
    (plain : ∀ p ∈ L, PlainWire n C m (opnd C p.1 p.2)) :
    Q0.clauseStars G C (L.image (leafSupport n C)) := by
  intro K hK a ha b hb ne
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
  rcases plain_pin_anchor D four least (plain p hp) with small | anchor
  · exact (ne (Finset.card_le_one.mp small a ha b hb)).elim
  · exact anchor

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
