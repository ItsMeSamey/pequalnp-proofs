import T2SoleOrSplice
import Mathlib.Data.Nat.Find

namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds

/-- Size comparison is unrestricted within Eligible; secondary comparison
    is the already existing equal-size singleton-hot-row predicate. -/
structure LexMinimum (n : Nat) (C : Circuit) : Prop where
  eligible : Eligible n C
  primary : ∀ D, Eligible n D → C.size ≤ D.size
  secondary : SecondaryMinimum n C

theorem exists_lexMinimum {n : Nat} (feasible : ∃ C : Circuit, Eligible n C) :
    ∃ C : Circuit, LexMinimum n C := by
  classical
  let S := fun k : Nat => ∃ C : Circuit, Eligible n C ∧ C.size=k
  have someS : ∃ k, S k := by
    obtain ⟨C,h⟩ := feasible
    exact ⟨C.size,C,h,rfl⟩
  let k := Nat.find someS
  have minSize : S k := Nat.find_spec someS
  let H := fun h : Nat => ∃ C : Circuit, Eligible n C ∧ C.size=k ∧ hotRows n C=h
  have someH : ∃ h, H h := by
    obtain ⟨C,hc,sz⟩ := minSize
    exact ⟨hotRows n C,C,hc,sz,rfl⟩
  obtain ⟨C,hc,sz,score⟩ : H (Nat.find someH) := Nat.find_spec someH
  refine ⟨C,hc,?_,?_⟩
  · intro D hd
    rw [sz]
    exact Nat.find_min' someS (show S D.size from ⟨D,hd,rfl⟩)
  · intro D hd same
    rw [score]
    exact Nat.find_min' someH (show H (hotRows n D) from ⟨D,hd,same.trans sz,rfl⟩)

/-- Every eligible witness has a smallest-size, secondary-minimal representative,
    without enumerating gate syntax or requiring finite wire-index domains. -/
theorem lex_representative {n : Nat} (D : Circuit) (hd : Eligible n D) :
    ∃ C : Circuit, LexMinimum n C ∧ C.size≤D.size := by
  obtain ⟨C,h⟩ := exists_lexMinimum ⟨D,hd⟩
  exact ⟨C,h,h.primary D hd⟩

/-- Explicit interface to the physical normalization theorem. The benchmark's
    arbitrary input lists and output conventions prevent silently treating every
    Monotone2 competitor as eligible. A normalized result need not preserve
    singleton gate values or the hot-row score. -/
def CanNormalize (n : Nat) : Prop :=
  ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → Computes n D →
    ∃ E : Circuit, Eligible n E ∧ E.size≤D.size

theorem LexMinimum.benchmark_bound {n : Nat} {C : Circuit} (h : LexMinimum n C)
    (normalize : CanNormalize n) (D : Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 D) (correct : Computes n D) :
    C.size≤D.size := by
  obtain ⟨E,he,price⟩ := normalize D mono correct
  exact (h.primary E he).trans price

/-- Use this formulation when the induction supplies a lower bound only on
    lexicographic representatives and deletion returns a general Monotone2
    circuit of the smaller arity. A normalized deleted circuit itself supplies
    the smaller-arity witness. -/
theorem lower_after_deletion {m bound saved parentSize : Nat}
    (normalize : CanNormalize m)
    (ih : ∀ C : Circuit, LexMinimum m C → bound≤C.size)
    (D : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 D)
    (correct : Computes m D) (cost : D.size+saved≤parentSize) :
    bound+saved≤parentSize := by
  obtain ⟨E,he,price⟩ := normalize D mono correct
  obtain ⟨C,hc,small⟩ := lex_representative E he
  exact (Nat.add_le_add_right ((ih C hc).trans (small.trans price)) saved).trans cost

/-- If the induction hypothesis quantifies over all benchmark circuits, the
    smaller circuit returned by deletion can be applied to it directly. -/
theorem lower_after_deletion_all {m bound saved parentSize : Nat}
    (ih : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C → Computes m C → bound≤C.size)
    (D : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 D)
    (correct : Computes m D) (cost : D.size+saved≤parentSize) :
    bound+saved≤parentSize :=
  (Nat.add_le_add_right (ih D mono correct) saved).trans cost

#print axioms exists_lexMinimum
#print axioms lower_after_deletion
end T2SoleOrSplice
