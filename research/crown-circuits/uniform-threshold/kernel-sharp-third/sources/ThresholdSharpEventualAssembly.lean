import ThresholdSharpScaleChoice
import ThresholdSharpRelativeAdapter
import ThresholdPublicThird
namespace ThresholdSharpGlobalLower
open ResidualSurplus T2CubeDeletion T2SoleOrSplice T2RegularOrDelete ThresholdThirdDeletion ThresholdPublicMinimum

def NativeScaleLedger : Prop := ∀ {n out : ℕ} {gs : List Raw}, 5≤n →
  LexMinimum n (source gs out) → Regular n gs → ∀ P X t E u : ℝ,
  t=Real.sqrt (2*(n:ℝ)) → E=((source gs out).size:ℝ)-2*n-t →
  (2:ℝ)^80≤P → P^100≤X → X^10=t → X^6≤(2:ℝ)^16*E → E≤P*X^6 →
  (2:ℝ)^20≤(u/10)*P → 1≤u*P → 0<u → u≤1/1000 → Nonempty (RelativeLedger n t E u)

theorem eventually_native (native : NativeScaleLedger) : BoundedRegular := by
  intro B bp u up us
  obtain ⟨P,N,p14,pB,p80,tol,prod,orders⟩ := ThresholdSharpScaleBand.choose bp up us
  refine ⟨max N ((2:ℕ)^402),?_⟩
  intro n large regular ep cap
  have hN := (le_max_left _ _).trans large
  have huge : (2:ℕ)^402≤n := (le_max_right _ _).trans large
  have hn : 5≤n := (by decide : 5≤(2:ℕ)^402).trans huge
  obtain ⟨X,big,time⟩ := orders n hN
  have pp : 1≤P := by linarith
  have xp : 0≤X := (pow_nonneg (by linarith : 0≤P) 100).trans big
  obtain ⟨_,weak⟩ := unrestricted ThresholdRegularThird.regular huge
  have sq := Real.sq_sqrt (show 0≤2*(n:ℝ) by positivity)
  obtain ⟨lo,hi⟩ := ThresholdSharpScaleBand.band n _ X (surplus n) B P sq time xp ep pp pB weak cap
  obtain ⟨gs,out,⟨M⟩,reg⟩ := regular
  refine native hn M reg P X _ _ u rfl ?_ p80 big time lo hi tol prod up us
  rw [lex_size (by omega : 2≤n) M]
  rfl

theorem regular_from_native (native : NativeScaleLedger) : RegularLower :=
  regular_of_bounded (eventually_native native)
end ThresholdSharpGlobalLower
