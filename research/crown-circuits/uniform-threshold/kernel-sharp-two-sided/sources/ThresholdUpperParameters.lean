import ThresholdUpperRateInterface
import ThresholdUpperSharpAssembly
import ThresholdUpperRound
import ThresholdScaleRoot
namespace ThresholdUpperParameters
open ThresholdUpperCatalogue ThresholdUpperSecond ThresholdUpperActualSelection
open ThresholdUpperFiniteAssembly ThresholdUpperSharpAssembly

private theorem ceil_bounds {x : ℝ} (non : 0≤x) :
    x≤(⌈x⌉₊:ℝ) ∧ (⌈x⌉₊:ℝ)≤x+1 := ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one non).le⟩

private theorem choose_two {v : ℕ} (pos : 1≤v) :
    (v.choose 2:ℝ)=((v:ℝ)^2-v)/2 := by
  have h := ThresholdSharpArithmetic.twice_choose_two v
  have h' := congrArg (fun z : ℤ => (z:ℝ)) h
  push_cast at h'
  nlinarith

theorem from_rates {β : ℝ} (b1 : 1≤β) (b2 : β≤2) (first : FirstRate β)
    (second : SecondRate) : AllOrderParameters β := by
  intro δ dp
  let C : ℝ := 5000000
  let a := β/4
  let cutoff := max ((2:ℝ)^51/δ) (max (10000:ℝ) (2^170*(C+1)))
  have huge : 2^170*(C+1)≤cutoff := (le_max_right _ _).trans (le_max_right _ _)
  have big : 10000≤cutoff := (le_max_left _ _).trans (le_max_right _ _)
  have tc : (2:ℝ)^51/δ≤cutoff := le_max_left _ _
  have base : 1≤cutoff := by linarith only [big]
  obtain ⟨N,hN⟩ := exists_nat_ge (cutoff^200)
  refine ⟨N,fun n large => ?_⟩
  have nle : (N:ℝ)≤(n:ℝ) := by exact_mod_cast large
  have n2 : (n:ℝ)≤2*(n:ℝ) := by linarith only [Nat.cast_nonneg n (α:=ℝ)]
  obtain ⟨x,xb,nx⟩ := ThresholdScaleRoot.exists_above (by decide : 200≠0) base
    ((hN.trans nle).trans n2)
  have x1 := base.trans xb
  have xn : 0≤x := by linarith only [x1]
  have a0 : 0≤a := by dsimp [a]; linarith only [b1]
  have a1 : a≤1 := by dsimp [a]; linarith only [b2]
  let v := ⌈x^100+a*x^60+x^58⌉₊
  obtain ⟨vl,vh⟩ := ceil_bounds (show 0≤x^100+a*x^60+x^58 by positivity)
  change x^100+a*x^60+x^58≤(v:ℝ) at vl
  change (v:ℝ)≤x^100+a*x^60+x^58+1 at vh
  have xv : x^100≤(v:ℝ) := by linarith only [vl,mul_nonneg a0 (pow_nonneg xn 60),pow_nonneg xn 58]
  obtain ⟨y,xy,yv⟩ := ThresholdScaleRoot.exists_above (by decide : 100≠0) x1 xv
  have y1 := x1.trans xy
  have yn := xn.trans xy
  have ybig := (big.trans xb).trans xy
  let w := ⌈β*y^60⌉₊
  let z := ⌈y^45⌉₊
  let k := ⌈y^50⌉₊
  obtain ⟨wl,wh⟩ := ceil_bounds (mul_nonneg (by linarith only [b1] : 0≤β) (pow_nonneg yn 60))
  obtain ⟨zl,zh⟩ := ceil_bounds (pow_nonneg yn 45)
  obtain ⟨kl,kh⟩ := ceil_bounds (pow_nonneg yn 50)
  change β*y^60≤(w:ℝ) at wl
  change (w:ℝ)≤β*y^60+1 at wh
  change (z:ℝ)≤y^45+1 at zh
  change (k:ℝ)≤y^50+1 at kh
  obtain ⟨room,loss⟩ := first y v w k ybig yv wl wh kl kh
  have wc := mul_le_mul_of_nonneg_right b2 (pow_nonneg yn 60)
  have w0 : y^60≤(w:ℝ) := by linarith only [wl,mul_le_mul_of_nonneg_right b1 (pow_nonneg yn 60)]
  have w3 : (w:ℝ)≤3*y^60 := by linarith only [wh,wc,one_le_pow₀ y1 (n:=60)]
  obtain ⟨fit,econ⟩ := second y n v w z k ybig yv w0 w3 zl zh kl kh
  have tall := ThresholdUpperRound.slack x1 (huge.trans xb) (show 0≤C by norm_num [C]) a0 a1 yn yv nx.symm vl vh
  have yhuge : 4≤(v:ℝ) := by rw [←yv]; linarith only [le_self_pow₀ y1 (by decide : 100≠0),ybig]
  have hv : 4≤v := by exact_mod_cast yhuge
  have hk : k≤v := by
    have p := mul_le_mul_of_nonneg_right ybig (pow_nonneg yn 50)
    have c : y^51≤y^100 := pow_le_pow_right₀ y1 (by decide)
    have kbound : (k:ℝ)≤(v:ℝ) := by nlinarith only [p,c,kh,yv,one_le_pow₀ y1 (n:=50)]
    exact_mod_cast kbound
  have env : Envelope n v w z k := by
    intro f low cap
    apply econ f cap
    have freq : (v.choose 2:ℝ)≤(f:ℝ)+((lossBudget w v/(sampleCount w v-starCost w v k):ℕ):ℝ) := by exact_mod_cast low
    rw [choose_two (by omega : 1≤v)] at freq
    dsimp [C,a] at tall
    linarith only [tall,freq,loss,pow_le_pow_right₀ y1 (by decide : 140≤155),pow_nonneg yn 155]
  have wid : y^20≤x^20+1 := by
    by_contra! bad
    have p := pow_lt_pow_left₀ bad (by positivity : 0≤x^20+1) (by decide : 5≠0)
    have qr := mul_le_mul_of_nonneg_right a1 (pow_nonneg xn 60)
    nlinarith only [p,yv,vh,qr,pow_le_pow_right₀ x1 (by decide : 58≤60),
      pow_le_pow_right₀ x1 (by decide : 60≤80),one_le_pow₀ x1 (n:=60),
      pow_nonneg xn 20,pow_nonneg xn 40,pow_nonneg xn 60]
  have y60 : y^60≤x^60+7*x^40 := by
    have p := pow_le_pow_left₀ (pow_nonneg yn 20) wid 3
    nlinarith only [p,one_le_pow₀ x1 (n:=40),pow_le_pow_right₀ x1 (by decide : 20≤40)]
  have rough : y≤2*x := by
    by_contra! bad
    have base : 2*x*x^19 < y*x^19 :=
      mul_lt_mul_of_pos_right bad (pow_pos (by linarith only [x1] : 0<x) 19)
    have sub : x^19≤y^19 := pow_le_pow_left₀ xn (by linarith only [bad,x1]) 19
    have upper := mul_le_mul_of_nonneg_left sub yn
    nlinarith only [base,upper,wid,one_le_pow₀ x1 (n:=20)]
  have cut := (div_le_iff₀ dp).mp (tc.trans xb)
  refine ⟨x,v,w,z,k,x1,nx,by linarith only [cut],hv,hk,room,fit,env,?_⟩
  change (v:ℝ)+w+16*z-x^100≤_
  dsimp [a] at vh
  nlinarith only [vh,wh,zh,mul_le_mul_of_nonneg_left y60 (show 0≤β by linarith only [b1]),
    pow_le_pow_left₀ yn rough 45]

#print axioms from_rates
end ThresholdUpperParameters
