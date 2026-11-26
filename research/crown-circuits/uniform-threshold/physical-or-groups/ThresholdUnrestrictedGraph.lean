import ThresholdSimpleIncidence
import T2RegularOrDelete

namespace ThresholdUnrestrictedGraph
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdSimpleIncidence
open ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource T2SoleOrSplice
open T2CubeDeletion T2RegularOrDelete

/-- A public input circuit either admits the lower-arity saving, or its inputs
are distinct edges of a simple incidence graph in a minimum representative.
The decoder's OR budget is charged against the number of active vertices. -/
theorem regular_graph_or_delete {m : Nat} (two : 2 ≤ m) (C : Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (rep : Computes (m+1) C) :
    Saving m C.size ∨ ∃ gs : List Raw, ∃ out : Nat,
      ∃ mini : LexMinimum (m+1) (source gs out),
      let L := layout (m+1) gs out mini.eligible
      gs.length ≤ C.size ∧ Regular (m+1) gs ∧
      (∀ w, (endpoints L w).card=2) ∧ Function.Injective (endpoints L) ∧
      ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ s : Finset (Fin (m+1)), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card) ∧
        ors D.gates + 2*(m+1) ≤ ors (source gs out).gates + (vertices L).card := by
  rcases regular_or_delete two C mono rep with save | ⟨gs,out,mini,budget,reg⟩
  · exact Or.inl save
  refine Or.inr ⟨gs,out,mini,budget,reg,?_⟩
  obtain ⟨card,inj,D,hm,hc,price⟩ := classified_simple (by omega) mini reg
  exact ⟨card,inj,D,hm,hc,by simpa only [vertices_card] using price⟩

#print axioms regular_graph_or_delete
end ThresholdUnrestrictedGraph
