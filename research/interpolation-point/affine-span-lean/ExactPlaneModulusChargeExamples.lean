import ExactPlaneModulusCharges
namespace ExactPlaneModulusChargeExamples
def counts (n : ℕ) : ℕ×ℕ :=
  let r := ExactPlaneModulusCharges.search n
  (r.candidates,r.divisions)
#eval (List.range 6).map counts
example : counts 1 = (1,0) := by native_decide
end ExactPlaneModulusChargeExamples
