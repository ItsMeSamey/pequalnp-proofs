import ThresholdBoundaryDecoder

namespace ThresholdFirstMarkCut
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins
open ThresholdOccurrenceEval
variable {C : Circuit} {n k : Nat} (L : Layout C n)

structure Partition (L : Layout C n) where
  marked : Id C → Prop
  first : Id C → Id C
  onMark : ∀ i, marked i → first i=i
  follows : ∀ j i b, ¬marked j → source L (i,b)=n+j.val → first j=first i

def region (P : Partition L) (u i : Id C) := P.marked i ∨ P.first i≠u

private theorem in_basin (P : Partition L) {u i : Id C} (hi : region L P u i)
    (different : i≠u) : P.first i≠u := by
  rcases hi with marked|away
  · simpa only [P.onMark i marked] using different
  · exact away

/-- Every physical gate operand at a region gate other than its entry has its
source in the region. This includes both occurrences of a twice-read wire. -/
theorem incoming_gate (P : Partition L) (u i : Id C) (hi : region L P u i)
    (different : i≠u) (b : Bool) (j : Id C) (edge : source L (i,b)=n+j.val) :
    region L P u j := by
  by_cases marked : P.marked j
  · exact Or.inl marked
  · exact Or.inr (fun eq => in_basin L P hi different ((P.follows j i b marked edge).symm.trans eq))

/-- The route from a raw pin is only consulted when the occurrence carries a
fresh input. Distinct occurrences of the same raw wire may carry different
assignments after a restriction. -/
theorem pin_locality (P : Partition L) (A : Assignment C k) (owner : Fin k → Id C)
    (route : ∀ q : Pin C, source L q<n → ∀ x, A q=Sum.inr x → owner x=P.first q.1)
    (u : Id C) (s t : Finset (Fin k)) (same : ∀ x, owner x≠u → (x∈s ↔ x∈t))
    (i : Id C) (hi : region L P u i) (different : i≠u) (b : Bool)
    (outside : ∀ j : Id C, source L (i,b)=n+j.val → ¬region L P u j) :
    pinEval L A s (i,b)=pinEval L A t (i,b) := by
  by_cases raw : source L (i,b)<n
  · simp only [pinEval,if_pos raw]
    cases h : A (i,b) with
    | inl c => rfl
    | inr x =>
      have away : owner x≠u := fun e => in_basin L P hi different ((route (i,b) raw x h).symm.trans e)
      simp only [value]
      simp [same x away]
  · have lt := earlier L (i,b)
    change source L (i,b)<n+i.val at lt
    let j : Id C := ⟨source L (i,b)-n,by have bound := i.isLt; omega⟩
    have eq : source L (i,b)=n+j.val := by dsimp [j]; omega
    exact False.elim (outside j eq (incoming_gate L P u i hi different b j eq))

theorem unary (P : Partition L) (A : Assignment C k) (owner : Fin k → Id C)
    (route : ∀ q : Pin C, source L q<n → ∀ x, A q=Sum.inr x → owner x=P.first q.1)
    (u out : Id C) (marked : P.marked out) (family : Finset (Fin k) → Prop)
    (same : ∀ s, family s → ∀ t, family t → ∀ x, owner x≠u → (x∈s ↔ x∈t)) :
    ∃ d : Bool → Bool, ∀ s, family s → eval L A s out=d (eval L A s u) := by
  exact ThresholdBoundaryDecoder.unary L A (region L P u) u out (Or.inl marked) family
    (fun s hs t ht => pin_locality L P A owner route u s t (same s hs t ht))

end ThresholdFirstMarkCut
