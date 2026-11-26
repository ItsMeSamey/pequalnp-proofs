import Research.PlaneRectangleCost

namespace PlaneRectangleCost
namespace Sample

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def masks : List (ℕ × ℕ) :=
  [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]

def multipliers : List Vertex := [1,3,9]

/-- The two halves of the sample's Fin.append, in the original coordinate order. -/
def bit (s t : ℕ) (a b : Vertex) (swap : Bool) (v : Vertex) : Bool :=
  if swap = true then t.testBit ↑(-(a*v+b)) else s.testBit ↑(a*v+b)

-- For coverage it suffices to use the unswapped translations of the third mask.
private theorem hits : ∀ u v : Vertex, u-v ∉ D →
    ∃ b : Vertex, bit 19 708 1 b false u = true ∧ bit 708 19 1 b false v = true := by
  decide +kernel

def accepts {m : ℕ} (A B : Fin m → Finset Vertex) (left right : Vertex → Bool) : Prop :=
  ∃ i, (∃ u ∈ A i, left u = true) ∧ (∃ v ∈ B i, right v = true)

/-- Meeting the positive and negative sample promises forces an exact edge cover. -/
theorem exactOfSamples {m : ℕ} (A B : Fin m → Finset Vertex)
    (pos : ∀ u v : Vertex, u-v ∈ D →
      accepts A B (fun x => decide (x=u)) (fun y => decide (y=v)))
    (neg : ∀ p ∈ masks, ∀ a ∈ multipliers, ∀ (b : Vertex) (s : Bool),
      ¬ accepts A B (bit p.1 p.2 a b s) (bit p.2 p.1 a b s)) :
    Finset.univ.biUnion (fun i => (A i) ×ˢ (B i)) = edges := by
  ext ⟨u,v⟩
  constructor
  · intro h
    obtain ⟨i,_,hr⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra miss
    obtain ⟨b,bl,br⟩ := hits u v miss
    exact neg (19,708) (by decide) 1 (by decide) b false ⟨i,⟨u,hu,bl⟩,⟨v,hv,br⟩⟩
  · intro h
    obtain ⟨i,⟨x,hx,ex⟩,⟨y,hy,ey⟩⟩ := pos u v (Finset.mem_filter.mp h).2
    have ex' : x = u := of_decide_eq_true ex
    have ey' : y = v := of_decide_eq_true ey
    subst x; subst y
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_product.mpr ⟨hx,hy⟩⟩

theorem costOfSamples {m : ℕ} (A B : Fin m → Finset Vertex)
    (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (pos : ∀ u v : Vertex, u-v ∈ D →
      accepts A B (fun x => decide (x=u)) (fun y => decide (y=v)))
    (neg : ∀ p ∈ masks, ∀ a ∈ multipliers, ∀ (b : Vertex) (s : Bool),
      ¬ accepts A B (bit p.1 p.2 a b s) (bit p.2 p.1 a b s)) :
    64 ≤ (∑ i, (((A i).card - 1) + ((B i).card - 1) + 1)) + (m-1) :=
  cost m A B ha hb (exactOfSamples A B pos neg)

end Sample
end PlaneRectangleCost
