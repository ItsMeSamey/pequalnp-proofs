import ThresholdUpperParameters
import ThresholdUpperFirstRate
import ThresholdUpperSecondRate

namespace ThresholdUpperAllOrders
theorem parameters {β : ℝ} (b1 : 1≤β) (b2 : β≤2) (fifth : β^5=8) :
    ThresholdUpperSharpAssembly.AllOrderParameters β :=
  ThresholdUpperParameters.from_rates b1 b2
    (ThresholdUpperFirstRate.first_rate b1 b2 fifth) ThresholdUpperSecondRate.second_rate

#print axioms parameters
end ThresholdUpperAllOrders
