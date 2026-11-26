import ThresholdMinimumEndpoint
import ThresholdPublicInduction
import ThresholdRegularLedger
namespace ThresholdPublicFourThirds
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ThresholdOrGroups ThresholdOrExtraction
open ThresholdSimpleIncidence ThresholdRegularSource T2SoleOrSplice T2CubeDeletion
open ThresholdPublicMinimum ThresholdFourThirds

theorem native_step : NativeStep := by
  intro k hk C hc
  rcases ThresholdUnrestrictedGraph.regular_graph_or_delete hk C (eligible_mono hc.eligible) hc.eligible.1 with save | ⟨gs,out,M,price,reg,two,inj,D,dm,rep,cost⟩
  · exact Or.inl save
  · have same := (lex_size (by omega : 2≤k+1) M).trans (lex_size (by omega : 2≤k+1) hc).symm
    apply Or.inr
    rw [←same]
    exact ThresholdGlobalGlue.regular_ledger M reg two inj D dm rep cost

theorem native_squared {n : Nat} (hn : 2≤n) (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    Bound (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) := by
  apply ThresholdPublicInduction.bound_mono (minimum_squared native_step hn)
  unfold excess intMinimum
  have h := le_size mono full
  omega

theorem native_real {n : Nat} (hn : 2≤n) (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    2*(n : ℝ)+(4/3 : ℝ)*Real.sqrt ((n : ℝ)+3)-6 ≤ (C.size : ℝ) :=
  (minimum_real native_step hn).trans (by exact_mod_cast le_size mono full)

#print axioms native_step
#print axioms native_squared
#print axioms native_real
end ThresholdPublicFourThirds
