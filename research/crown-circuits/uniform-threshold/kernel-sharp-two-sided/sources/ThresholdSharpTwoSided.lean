import ThresholdUpperAllOrders
import ThresholdUpperBeta
namespace ThresholdSharpTwoSided
open ThresholdThirdDeletion

theorem rational (ε : ℝ) (ep : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 0≤surplus n ∧
      (9765625-ε)*(n:ℝ)^3≤2048*(surplus n)^10 ∧
      2048*(surplus n)^10≤(9765625+ε)*(n:ℝ)^3 := by
  obtain ⟨beta,b1,b2,fifth⟩ := ThresholdUpperBeta.exists_beta
  exact ThresholdUpperSharpAssembly.two_sided (by linarith) b2 fifth
    (ThresholdUpperAllOrders.parameters b1 b2 fifth) ε ep
#print axioms rational
end ThresholdSharpTwoSided
