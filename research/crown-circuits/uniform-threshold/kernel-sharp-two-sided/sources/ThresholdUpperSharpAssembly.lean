import ThresholdUpperFiniteAssembly
import ThresholdUpperScalarRate
import ThresholdSharpLowerFinal
namespace ThresholdUpperSharpAssembly
open ThresholdUpperCatalogue ThresholdUpperSecond ThresholdThirdDeletion
open ThresholdUpperFiniteAssembly ThresholdUpperScalarRate ThresholdSharpGlobalLower

def AllOrderParameters (beta : ℝ) : Prop := ∀ δ : ℝ, 0<δ → ∃ N : ℕ, ∀ n : ℕ, N≤n →
  ∃ (x : ℝ) (v w z k : ℕ), 1≤x ∧ x^200=2*(n:ℝ) ∧ (2:ℝ)^51≤δ*x ∧
    4≤v ∧ k≤v ∧ starCost w v k<sampleCount w v ∧ w≤Fintype.card (Edges z) ∧
    Envelope n v w z k ∧ (v:ℝ)+w+16*z-x^100≤
      (5*beta/4)*x^60+x^58+7*beta*x^40+2^49*x^45+18

theorem power_upper {beta : ℝ} (bp : 0≤beta) (b2 : beta≤2) (fifth : beta^5=8)
    (params : AllOrderParameters beta) (ε : ℝ) (ep : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n →
      2048*(surplus n)^10≤(9765625+ε)*(n:ℝ)^3 := by
  let f := fun q : ℝ => 2048*(8*(5*beta/4+q)^10)
  have cont : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨d,dp,near⟩ := Metric.continuousAt_iff.mp (cont.continuousAt (x:=0)) ε ep
  have close := near (x:=d/2) (show dist (d/2) 0<d by rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<d/2)]; linarith)
  have at0 : f 0=9765625 := by simpa [f] using coefficient fifth
  rw [Real.dist_eq,abs_lt,at0] at close
  have tweak : 2048*(8*(5*beta/4+d/2)^10)≤9765625+ε := by change f (d/2)≤_; linarith [close.2]
  obtain ⟨N,all⟩ := params (d/2) (by positivity)
  refine ⟨max N ((2:ℕ)^402),?_⟩
  intro n large
  obtain ⟨x,v,w,z,k,x1,nx,cut,hv,hk,room,fit,env,size⟩ := all n ((le_max_left _ _).trans large)
  have save := cost hv hk room fit env
  have realSave : (ThresholdPublicMinimum.minimum n:ℝ)≤2*(n:ℝ)+v+w+16*z := by exact_mod_cast save
  have root : Real.sqrt (2*(n:ℝ))=x^100 := by
    rw [←nx,show x^200=(x^100)^2 by ring,Real.sqrt_sq (pow_nonneg (by linarith) _)]
  have size' : surplus n≤(5*beta/4)*x^60+x^58+7*beta*x^40+2^49*x^45+18 := by
    unfold surplus
    rw [root]
    linarith
  have nonneg := (unrestricted ThresholdRegularThird.regular ((le_max_right _ _).trans large)).1
  have bound := endpoint x1 bp b2 nx nonneg (by positivity) cut size'
  have a := mul_le_mul_of_nonneg_left bound (by norm_num : 0≤(2048:ℝ))
  have b := mul_le_mul_of_nonneg_right tweak (pow_nonneg (Nat.cast_nonneg n) 3)
  nlinarith only [a,b]

theorem two_sided {beta : ℝ} (bp : 0≤beta) (b2 : beta≤2) (fifth : beta^5=8)
    (params : AllOrderParameters beta) (ε : ℝ) (ep : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 0≤surplus n ∧
      (9765625-ε)*(n:ℝ)^3≤2048*(surplus n)^10 ∧
      2048*(surplus n)^10≤(9765625+ε)*(n:ℝ)^3 := by
  obtain ⟨L,lo⟩ := lower_sharp ε ep
  obtain ⟨U,hi⟩ := power_upper bp b2 fifth params ε ep
  exact ⟨max L U,fun n big=>⟨(lo n ((le_max_left _ _).trans big)).1,
    (lo n ((le_max_left _ _).trans big)).2,hi n ((le_max_right _ _).trans big)⟩⟩
end ThresholdUpperSharpAssembly
