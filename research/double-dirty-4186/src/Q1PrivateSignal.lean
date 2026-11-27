import Q1PrivateOwned
import Q1DoubleProjectedOwned

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

theorem batch_of_signal {n a w : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (A : Fin a → Clause n) (W : Fin w → Clause n)
    (R : Finset (Sym2 (Fin n))) (remain : R ⊆ Ustar G C)
    (term : (Fin n → Bool) → Bool) (owned : ∀ e ∈ R, AcceptPair term e)
    (below : ∀ x, term x = true → graphFun G ∅ x = true)
    (sem : ∀ x, term x = true ↔ ∀ c, ∃ v ∈ literals A W c, x v = true)
    (anchor : ∀ c, ∀ x ∈ literals A W c, ∀ y ∈ literals A W c, x ≠ y →
      ∃ d, ∀ z ∈ literals A W c, G.Adj d z ∧ s(d,z) ∈ starEdges G C) :
    ∃ P : Batch G C A W R.card, ∀ i, (R.equivFin.symm i).val = s(P.pt i false,P.pt i true) := by
  classical
  apply batch_of_owned four A W R remain _ _ anchor
  · intro u v he c
    obtain ⟨x,y,eq,h⟩ := owned _ he
    obtain ⟨z,hz,active⟩ := (sem _).mp h c
    have hxy : z=x ∨ z=y := by simpa [pairInput] using active
    have hmem : z ∈ s(u,v) := eq ▸ (Sym2.mem_iff.mpr hxy : z ∈ s(x,y))
    rcases Sym2.mem_iff.mp hmem with e | e
    · exact Or.inl (e ▸ hz)
    · exact Or.inr (e ▸ hz)
  · intro S hits
    let x := fun z : Fin n => decide (z ∈ S)
    have yes : term x = true := (sem x).mpr (by
      intro c
      obtain ⟨z,hz,hk⟩ := hits c
      exact ⟨z,hk,decide_eq_true hz⟩)
    have hit := below x yes
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
      Bool.false_or,decide_eq_true_eq,x] at hit
    obtain ⟨i,j,adj,hi,hj⟩ := hit
    exact ⟨i,hi,j,hj,adj⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
