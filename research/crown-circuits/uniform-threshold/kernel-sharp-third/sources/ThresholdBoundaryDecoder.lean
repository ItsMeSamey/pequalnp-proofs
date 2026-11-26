import ThresholdOccurrenceEval
namespace ThresholdBoundaryDecoder
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins ThresholdOccurrenceEval
variable {C : Circuit} {n k : Nat} (L : Layout C n) (A : Assignment C k)

/-- Gates in the downstream region use three kinds of information: the boundary
bit itself, earlier gates in the region, and unaffected incoming operand values. -/
theorem cut_eq (region : Id C → Prop) (u : Id C) (s t : Finset (Fin k))
    (hub : eval L A s u=eval L A t u)
    (incoming : ∀ i, region i → i≠u → ∀ b,
      (∀ j : Id C,source L (i,b)=n+j.val → ¬region j) →
      pinEval L A s (i,b)=pinEval L A t (i,b))
    (i : Id C) (inside : region i) : eval L A s i=eval L A t i := by
  classical
  by_cases atHub : i=u
  · simpa [atHub] using hub
  have agree (b : Bool) : pinEval L A s (i,b)=pinEval L A t (i,b) := by
    by_cases pred : ∃ j : Id C,source L (i,b)=n+j.val ∧ region j
    · obtain ⟨j,eq,rj⟩ := pred
      have lt := earlier L (i,b)
      change source L (i,b)<n+i.val at lt
      have decreases : j.val < i.val := by omega
      have next := cut_eq region u s t hub incoming j rj
      simpa [pinEval,eq] using next
    · apply incoming i inside atHub b
      intro j eq rj
      exact pred ⟨j,eq,rj⟩
  rw [row L A s i,row L A t i,agree false,agree true]
termination_by i.val
decreasing_by
  have h := earlier L (i,b)
  change source L (i,b) < n+i.val at h
  omega

/-- For a fixed outside assignment class, the output factors through a unary
Boolean function of the boundary wire; unreachable bit values are assigned false. -/
theorem unary (region : Id C → Prop) (u out : Id C) (hout : region out)
    (family : Finset (Fin k) → Prop)
    (fixedInputs : ∀ s, family s → ∀ t, family t → ∀ i, region i → i≠u → ∀ b,
      (∀ j : Id C,source L (i,b)=n+j.val → ¬region j) →
      pinEval L A s (i,b)=pinEval L A t (i,b)) :
    ∃ d : Bool → Bool, ∀ s, family s → eval L A s out=d (eval L A s u) := by
  classical
  let available (v : Bool) := ∃ t, family t ∧ eval L A t u=v
  let d (v : Bool) := if h : available v then eval L A h.choose out else false
  refine ⟨d,?_⟩
  intro s hs
  have h : available (eval L A s u) := ⟨s,hs,rfl⟩
  simp only [d,dif_pos h]
  exact cut_eq L A region u s h.choose h.choose_spec.2.symm
    (fixedInputs s hs _ h.choose_spec.1) out hout
end ThresholdBoundaryDecoder
