import ThresholdSharedPairEndpoints
import ThresholdMissedFour
namespace ThresholdSharpEndpoint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2CubeDeletion T2SoleOrSplice
open T2RegularOrDelete ThresholdSimpleIncidence ThresholdRegularSource ThresholdSharedPartition
open ThresholdSharedFlow ThresholdOrExtraction ThresholdPublicMinimum ThresholdSharpArithmetic
open ThresholdSharedStructural
def StarBoundary : Prop := ∀ n, 5≤n → ∀ gs out (M : LexMinimum n (source gs out)),
  Regular n gs → ∀ u∈hubs (source gs out) n,
    let L := layout n gs out M.eligible
    (singleAt L u).card≤1+max (fan L u) (leak L u)

theorem structure_of_star (star : StarBoundary) : PhysicalStructure := by
  intro n hn gs out M reg
  have two := (classified_simple (by omega : 2≤n) M reg).1
  have inputs := (regular_inputs n gs out M.eligible reg).1
  exact ⟨ThresholdMissedFour.missed_bound _ M inputs (by omega) two,star n hn gs out M reg,
    ThresholdSharedPairMinimum.regular_no_shared_raw M reg (by omega)⟩

theorem native_real_of_star (star : StarBoundary) {n : Nat} (hn : 4≤n)
    (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    2*(n:ℝ)+(Real.sqrt (8*(n:ℝ)-7)-7)/2 ≤ (C.size:ℝ) :=
  native_real_of_structure (structure_of_star star) hn C mono full
#print axioms native_real_of_star
end ThresholdSharpEndpoint
