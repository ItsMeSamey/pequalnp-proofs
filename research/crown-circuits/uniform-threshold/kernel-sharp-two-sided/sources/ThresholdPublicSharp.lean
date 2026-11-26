import ThresholdStarLeafBound
import ThresholdSharpPublicBounds

namespace ThresholdPublicSharp
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice
open ThresholdStarBypass ThresholdSharpEndpoint

/-- Physical fan-in-at-most-two monotone gates computing threshold two, on the full Boolean cube. -/
theorem native_real {n : Nat} (hn : 4≤n) (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    2*(n:ℝ)+(Real.sqrt (8*(n:ℝ)-7)-7)/2 ≤ (C.size:ℝ) :=
  native_real_of_star regular_star_boundary hn C mono full

theorem native_squared {n : Nat} (hn : 4≤n) (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    ThresholdSharpArithmetic.Bound (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) :=
  native_squared_of_star regular_star_boundary hn C mono full

theorem minimum_real {n : Nat} (hn : 4≤n) :
    2*(n:ℝ)+(Real.sqrt (8*(n:ℝ)-7)-7)/2 ≤ (ThresholdPublicMinimum.minimum n:ℝ) :=
  ThresholdSharpArithmetic.minimum_real
    (ThresholdSharedStructural.structure_tally (structure_of_star regular_star_boundary)) hn

#print axioms native_real
#print axioms native_squared
#print axioms minimum_real
end ThresholdPublicSharp
