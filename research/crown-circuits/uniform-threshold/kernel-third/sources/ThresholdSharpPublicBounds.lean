import ThresholdSharpEndpoint
namespace ThresholdSharpEndpoint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ThresholdPublicMinimum ThresholdSharpArithmetic T2SoleOrSplice

theorem native_squared_of_star (star : StarBoundary) {n : Nat} (hn : 4≤n)
    (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    Bound (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) := by
  have small := minimum_squared (ThresholdSharedStructural.structure_tally (structure_of_star star)) hn
  have cost := le_size mono full
  have h : (minimum n:ℤ)≤C.size := by exact_mod_cast cost
  obtain ⟨pos,sq⟩ := small
  unfold ThresholdFourThirds.excess intMinimum at pos sq
  constructor
  · omega
  · have a : 0≤2*((C.size:ℤ)-(minimum n:ℤ)) := by omega
    have b : 0≤2*((C.size:ℤ)-2*(n:ℤ))+2*((minimum n:ℤ)-2*(n:ℤ))+14 := by omega
    nlinarith [mul_nonneg a b]
#print axioms native_squared_of_star
end ThresholdSharpEndpoint
