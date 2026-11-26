import ThresholdSharpNativeBands
import ThresholdPhysicalMiddlePacking
import ThresholdSharpEventualAssembly
namespace ThresholdSharpGlobalLower
open ThresholdThirdDeletion
theorem native_scale_ledger : NativeScaleLedger := by
  intro n out gs hn M reg P X t E u root sur pp big time elo ehi tol prod up us
  obtain ⟨ep,hp,ord,lo,hi,budget,low,a,v,miss,del,imp⟩ :=
    ThresholdSharpNativeWindow.bands hn M reg P X t E u root sur pp big time elo ehi tol up us
  exact ThresholdPhysicalMiddlePacking.packing M reg hn t E P X u
    (by norm_num at pp; linarith) big (by rwa [mul_comm]) hp ep (by rwa [time])
    (by rwa [time]) (by norm_num at elo; exact elo) ord miss low a v imp del budget

theorem regular_sharp : RegularLower := regular_from_native native_scale_ledger

theorem lower_sharp (ε : ℝ) (ep : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 0≤surplus n ∧
      (9765625-ε)*(n:ℝ)^3≤2048*(surplus n)^10 :=
  rational_endpoint regular_sharp ε ep
#print axioms regular_sharp
#print axioms lower_sharp
end ThresholdSharpGlobalLower
