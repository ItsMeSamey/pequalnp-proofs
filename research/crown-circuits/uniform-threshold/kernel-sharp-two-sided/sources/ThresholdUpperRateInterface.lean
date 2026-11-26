import ThresholdUpperActualSelection
import Mathlib.Data.Real.Basic
namespace ThresholdUpperParameters
open ThresholdUpperCatalogue ThresholdUpperSecond ThresholdUpperActualSelection

def FirstRate (β : ℝ) : Prop := ∀ (y : ℝ) (v w k : ℕ), 10000≤y → y^100=(v:ℝ) →
  β*y^60≤(w:ℝ) → (w:ℝ)≤β*y^60+1 → y^50≤(k:ℝ) → (k:ℝ)≤y^50+1 →
  starCost w v k<sampleCount w v ∧
  ((lossBudget w v/(sampleCount w v-starCost w v k):ℕ):ℝ)≤(β/4)*y^160+10*y^140

def SecondRate : Prop := ∀ (y : ℝ) (n v w z k : ℕ), 10000≤y → y^100=(v:ℝ) →
  y^60≤(w:ℝ) → (w:ℝ)≤3*y^60 → y^45≤(z:ℝ) → (z:ℝ)≤y^45+1 →
  y^50≤(k:ℝ) → (k:ℝ)≤y^50+1 →
  w≤Fintype.card (Edges z) ∧
  ∀ f : ℕ, f≤v.choose 2 → (n:ℝ)+4000000*y^155≤(f:ℝ) →
    Fintype.card (Injection w z)*n+f*failCost w z+
      (3*f*(v+(k-1)^2-1))*pairCost w z 2+
      f.choose 2*max (pairCost w z 3) (pairCost w z 4) ≤ Fintype.card (Injection w z)*f

end ThresholdUpperParameters
