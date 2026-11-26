import Mathlib.Combinatorics.SimpleGraph.Finite
namespace ThresholdFamilySimpleGraph
variable {V : Type*} [DecidableEq V] (S : Finset V) (E : Finset (Finset V))

def graph : SimpleGraph ↥S where
  Adj a b := a ≠ b ∧ {a.val,b.val} ∈ E
  symm := ⟨fun a b h => ⟨Ne.symm h.1,by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

def profile (p : Sym2 ↥S) := p.toFinset.map (Function.Embedding.subtype (·∈S))

private theorem injective_profile : Function.Injective (profile S) := by
  intro x y h
  apply Sym2.ext
  intro v
  have e := congrArg (fun q : Finset V => v.val∈q) h
  simpa [profile] using e.to_iff

theorem edge_card (hE : E⊆S.powersetCard 2) [Fintype (graph S E).edgeSet] :
    (graph S E).edgeFinset.card=E.card := by
  classical
  have valid (p : (graph S E).edgeSet) : profile S p.val∈E := by
    obtain ⟨q,hq⟩ := p
    induction q using Sym2.ind with
    | _ a b =>
      have adj : (graph S E).Adj a b := hq
      simpa [profile,Sym2.toFinset_mk_eq] using adj.2
  let f : (graph S E).edgeSet → ↥E := fun p => ⟨_,valid p⟩
  have bij : Function.Bijective f := by
    constructor
    · intro p q e
      exact Subtype.ext (injective_profile S (congrArg Subtype.val e))
    · rintro ⟨q,hq⟩
      obtain ⟨incl,sz⟩ := Finset.mem_powersetCard.mp (hE hq)
      obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp sz
      let A : ↥S := ⟨a,incl (by simp [eq])⟩
      let B : ↥S := ⟨b,incl (by simp [eq])⟩
      have adj : (graph S E).Adj A B := ⟨fun h => ne (congrArg Subtype.val h),eq ▸ hq⟩
      refine ⟨⟨Sym2.mk A B,adj⟩,Subtype.ext ?_⟩
      change profile S (Sym2.mk A B)=q
      simp [profile,Sym2.toFinset_mk_eq,eq,A,B]
  rw [SimpleGraph.edgeFinset_card]
  exact (Fintype.card_congr (Equiv.ofBijective f bij)).trans (Fintype.card_coe _)

end ThresholdFamilySimpleGraph
