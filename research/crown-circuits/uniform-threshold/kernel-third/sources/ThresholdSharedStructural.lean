import ThresholdFlowTally
import ThresholdSharedFunding
import ThresholdSimpleIncidence
namespace ThresholdSharedStructural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2CubeDeletion T2SoleOrSplice
open T2RegularOrDelete ThresholdSimpleIncidence ThresholdRegularSource ThresholdSharedPartition
open ThresholdSharedFlow ThresholdOrExtraction ThresholdPublicMinimum ThresholdSharpArithmetic
structure Structural {C : Circuit} {n} (L : Layout C n) : Prop where
  missed_bound : (missed L).card≤4
  leaf_bound : ∀ u∈hubs C n, (singleAt L u).card≤1+max (fan L u) (leak L u)
  no_shared_raw : ∀ u∈hubs C n, ∀ v∈hubs C n, u≠v → active L u v=true →
    ∀ e : Fin n, u∈endpoints L e → v∉endpoints L e

def PhysicalStructure : Prop := ∀ n, 5≤n → ∀ gs out (M : LexMinimum n (source gs out)),
  Regular n gs → Structural (layout n gs out M.eligible)

theorem structure_tally (structural : PhysicalStructure) : PhysicalTally := by
  intro n hn gs out M reg
  have S := structural n hn gs out M reg
  have G := classified_simple (by omega : 2≤n) M reg
  apply ThresholdFlowTally.tally (layout n gs out M.eligible) G.1 G.2.1 S.missed_bound S.leaf_bound S.no_shared_raw
  simpa only [ThresholdFlowSum.deltaO,ThresholdFlowSum.deltaA,ThresholdSharedFlow.fan_readers,
    ThresholdSharedFunding.extrasOr,ThresholdSharedFunding.extrasAnd,ThresholdSharedFunding.fan]
    using ThresholdSharedFunding.funding M reg

theorem native_real_of_structure (structural : PhysicalStructure) {n : Nat} (hn : 4≤n)
    (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    2*(n:ℝ)+(Real.sqrt (8*(n:ℝ)-7)-7)/2 ≤ (C.size:ℝ) :=
  (minimum_real (structure_tally structural) hn).trans (by exact_mod_cast le_size mono full)
#print axioms structure_tally
end ThresholdSharedStructural
