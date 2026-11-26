import ThresholdSharedOrBudget
import ThresholdUnrestrictedGraph
namespace ThresholdPublicShared
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2SoleOrSplice
open T2CubeDeletion T2RegularOrDelete ThresholdSharedOrBudget

theorem shared_or_delete {k : Nat} (hk : 2≤k) (C : Circuit) (hm : Monotone2 C)
    (hc : Computes (k+1) C) :
    Saving k C.size ∨ ∃ gs : List Raw, ∃ out, ∃ M : LexMinimum (k+1) (source gs out),
      Regular (k+1) gs ∧ (source gs out).size≤C.size ∧
      (sharedOrs (source gs out) (k+1)).length+2*(k+1)≤(source gs out).size+1 ∧
      ∀ i∈sharedOrs (source gs out) (k+1), T2OrPartition.next (source gs out) (k+1) i=none := by
  rcases regular_or_delete hk C hm hc with save | ⟨gs,out,M,size,reg⟩
  · exact Or.inl save
  · refine Or.inr ⟨gs,out,M,reg,?_,regular_shared_budget M reg,?_⟩
    · simpa [source,Circuit.size,List.length_map] using size
    · intro i hi
      exact shared_stops (List.mem_filter.mp hi).1

#print axioms shared_or_delete
end ThresholdPublicShared
