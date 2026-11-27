import ExactPlaneDirectDivision
import ExactPlaneIrreducibleCount
namespace ExactPlaneDirectDivision
open ExactPlaneIrreducibleSearch

/-- Size of the complete trial domain traversed by the two nested all-tests.
Short-circuiting may skip a suffix. -/
def slots (n : ℕ) := ∑ j ∈ Finset.range (n/2), (words (j+1)).length

theorem slots_exact (n : ℕ) : slots n + 2 = 2^(n/2+1) := by
  simpa only [slots,words_length,ExactPlaneIrreducibleCount.trials,
    ExactPlaneIrreducibleCount.candidates] using ExactPlaneIrreducibleCount.trials_exact (n/2)

theorem slots_lt (n : ℕ) : slots n < 2*Nat.sqrt (2^n) := by
  simpa only [slots,words_length,ExactPlaneIrreducibleCount.trials,
    ExactPlaneIrreducibleCount.candidates] using ExactPlaneIrreducibleCount.trial_bound n

theorem candidate_times_slots (n : ℕ) :
    (words n).length * slots n < 2^n*(2*Nat.sqrt (2^n)) := by
  rw [words_length]
  exact Nat.mul_lt_mul_of_pos_left (slots_lt n) (by positivity)

#print axioms candidate_times_slots
end ExactPlaneDirectDivision
