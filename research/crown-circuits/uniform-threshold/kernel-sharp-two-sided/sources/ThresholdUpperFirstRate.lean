import ThresholdUpperFirstMoments
import ThresholdUpperRateInterface
namespace ThresholdUpperFirstRate
open ThresholdUpperCatalogue ThresholdUpperFirstMoments ThresholdUpperParameters

private theorem binomials (w : Nat) (hw : 4≤w) :
    2*(w.choose 2:ℝ)=(w:ℝ)*((w:ℝ)-1) ∧
    2*((w-1).choose 2:ℝ)≤((w:ℝ)-1)^2 ∧
    24*(w.choose 4:ℝ)≤((w:ℝ)-1)^4 := by
  have h2 := Nat.descFactorial_eq_factorial_mul_choose w 2
  have h4 := Nat.descFactorial_eq_factorial_mul_choose w 4
  have h2' := choose_factorial (w-1) 2
  have a : ((w-1:Nat):ℝ)=(w:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have b : ((w-2:Nat):ℝ)=(w:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c : ((w-3:Nat):ℝ)=(w:ℝ)-3 := by rw [Nat.cast_sub (by omega)]; norm_num
  norm_num [Nat.descFactorial_succ,Nat.factorial] at h2 h4 h2'
  have eq2 : ((w-1:Nat):ℝ)*(w:ℝ)=2*(w.choose 2:ℝ) := by exact_mod_cast h2
  have eq4 : ((w-3:Nat):ℝ)*(((w-2:Nat):ℝ)*(((w-1:Nat):ℝ)*(w:ℝ)))=24*(w.choose 4:ℝ) := by exact_mod_cast h4
  rw [a] at eq2 h2'
  rw [a,b,c] at eq4
  have wr : (4:ℝ)≤w := by exact_mod_cast hw
  refine ⟨by linarith,by linarith,?_⟩
  nlinarith only [eq4,sq_nonneg ((w:ℝ)-1),
    mul_nonneg (sq_nonneg ((w:ℝ)-1)) (show 0≤2*(w:ℝ)-4 by linarith)]

set_option maxRecDepth 8192 in
theorem first_rate {β : ℝ} (b1 : 1≤β) (b2 : β≤2) (fifth : β^5=8) : FirstRate β := by
  intro y v w k big ys wl wh kl kh
  let N := w.choose 2
  let D := sampleCount w v
  let B := starCost w v k
  let A := lossBudget w v
  have yp : 0<y := by linarith
  have y1 : 1≤y := by linarith
  have inc {i j : Nat} (h : i≤j) : y^i≤y^j := pow_le_pow_right₀ y1 h
  have lo : y^60≤(w:ℝ) := by nlinarith only [wl,mul_nonneg (sub_nonneg.mpr b1) (pow_nonneg yp.le 60)]
  have hi : (w:ℝ)≤3*y^60 := by nlinarith only [wh,mul_nonneg (sub_nonneg.mpr b2) (pow_nonneg yp.le 60),inc (show 0≤60 by decide)]
  have y50 : y≤y^50 := by simpa using inc (show 1≤50 by decide)
  have k161 : 161≤k := by exact_mod_cast (show (161:ℝ)≤k by linarith)
  have w4 : 4≤w := by
    have h := inc (show 50≤60 by decide); exact_mod_cast (show (4:ℝ)≤w by linarith)
  have kv : k≤v := by
    have g := mul_le_mul_of_nonneg_right (show 2≤y^50 by linarith) (pow_nonneg yp.le 50)
    exact_mod_cast (show (k:ℝ)≤v by nlinarith only [g,ys,kh,y50,big])
  obtain ⟨tw,wed,cy⟩ := binomials w w4
  change 2*(N:ℝ)=_ at tw
  have nw : y^100≤(N:ℝ) := by
    have ww := mul_self_le_mul_self (pow_nonneg yp.le 60) lo
    have b : 4*y^100≤y^120 := by
      have t := inc (show 1≤20 by decide)
      have u := mul_le_mul_of_nonneg_right (show 4≤y^20 by simp only [pow_one] at t; linarith) (pow_nonneg yp.le 100)
      nlinarith only [u]
    have wp : (4:ℝ)≤w := by exact_mod_cast w4
    nlinarith only [ww,b,tw,mul_nonneg (show 0≤(w:ℝ) by positivity) (show 0≤(w:ℝ)-2 by linarith)]
  have vN : v≤N := by exact_mod_cast (ys ▸ nw : (v:ℝ)≤N)
  have np : 0<N := by omega
  have wp : 0<(w:ℝ) := by exact_mod_cast (by omega : 0<w)
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have dp : 0<D := Nat.choose_pos vN
  have dr : 0<(D:ℝ) := by exact_mod_cast dp
  let p := (v:ℝ)/N
  have pp : 0≤p := by dsimp [p]; positivity
  have pair : ((w:ℝ)-1)*p*(w:ℝ)=2*(v:ℝ) := by
    dsimp [p]; field_simp; nlinarith only [congrArg (fun z : ℝ => z*(v:ℝ)) tw]
  have ratio : ((w:ℝ)-1)*p≤2*y^40 := by
    apply (mul_le_mul_iff_left₀ wp).mp
    have h := mul_le_mul_of_nonneg_right lo (show 0≤2*y^40 by positivity)
    nlinarith only [h,pair,ys]
  have qa := star_tail y N v w k big kl hi k161 kv vN np (by simpa [p,Nat.cast_sub (show 1≤w by omega)] using ratio)
  have qpay : ((B:ℝ)/D)*y^100≤1 := by simpa [B,D,starCost,sampleCount,N,Nat.cast_mul,mul_assoc] using qa
  let q := (B:ℝ)/D
  have qp : 0≤q := by dsimp [q]; positivity
  have half : q≤1/2 := by
    have m := mul_le_mul_of_nonneg_left (show 2≤y^100 by have := inc (show 50≤100 by decide); linarith) qp
    change q*y^100≤1 at qpay
    linarith
  have BD : B<D := by
    have lt : (B:ℝ)/D<1 := by change q<1; linarith
    have r := (div_lt_one dr).mp lt
    exact_mod_cast r
  refine ⟨BD,?_⟩
  let W := (w:ℝ)*((w-1).choose 2:ℝ)*p^2
  let E := 3*(w.choose 4:ℝ)*p^4
  have pp2 := pow_nonneg pp 2
  have pp4 := pow_nonneg pp 4
  have Wone : 0≤(w:ℝ)-1 := by
    have v4 : (4:ℝ)≤w := by exact_mod_cast w4
    linarith only [v4]
  have Wcap : W≤2*y^140 := by
    have eq := congrArg (fun z : ℝ => z^2) pair
    have cost := mul_le_mul_of_nonneg_right wed (mul_nonneg wp.le pp2)
    have cost' := mul_le_mul_of_nonneg_right cost wp.le
    have h := mul_le_mul_of_nonneg_right lo (show 0≤2*y^140 by positivity)
    apply (mul_le_mul_iff_left₀ wp).mp
    dsimp [W]
    nlinarith only [cost',eq,h,ys,congrArg (fun z : ℝ => z^2) ys]
  have Ecap : E≤(β/4)*y^160 := by
    have cost := mul_le_mul_of_nonneg_right cy pp4
    have key : β*((w:ℝ)-1)*p≤2*y^40 := by
      have non : 0≤((w:ℝ)-1)*p := mul_nonneg Wone pp
      have h := mul_le_mul_of_nonneg_right wl non
      apply (mul_le_mul_iff_left₀ (pow_pos yp 60)).mp
      nlinarith only [h,pair,ys]
    have pw := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by linarith only [b1] : 0≤β) Wone) pp) key 4
    have bc := mul_le_mul_of_nonneg_right cost (pow_nonneg (show 0≤β by linarith) 4)
    have coef := congrArg (fun z : ℝ => z*y^160) fifth
    apply (mul_le_mul_iff_left₀ (pow_pos (show 0<β by linarith) 4)).mp
    dsimp [E]; nlinarith only [pw,bc,coef]
  have four : 4≤v := (by omega : 4≤k).trans kv
  have s2 := sampled N v 2 (by omega) vN np
  have s4 := sampled N v 4 four vN np
  have paid : (A:ℝ)/D≤E+W := by
    have h2 := mul_le_mul_of_nonneg_left s2 (show 0≤(w:ℝ)*((w-1).choose 2:ℝ) by positivity)
    have h4 := mul_le_mul_of_nonneg_left s4 (show 0≤3*(w.choose 4:ℝ) by positivity)
    dsimp [A,D,lossBudget,sampleCount,N,E,W,p]
    dsimp only [N] at h2 h4
    push_cast
    simp only [div_eq_mul_inv,mul_add,add_mul] at h2 h4 ⊢
    nlinarith only [h2,h4]
  let L : ℝ := ((A/(D-B):Nat):ℝ)
  have native : (D-B)*(A/(D-B))≤A := by simpa [Nat.mul_comm] using Nat.div_mul_le_self A (D-B)
  have cst : ((D-B:Nat):ℝ)*L≤(A:ℝ) := by dsimp only [L]; exact_mod_cast native
  rw [Nat.cast_sub BD.le] at cst
  have conditional : (1-q)*L≤E+W := by
    have eq : (1-q)*L=(((D:ℝ)-(B:ℝ))*L)/D := by
      dsimp [q]; field_simp <;> ring
    rw [eq]
    exact (div_le_div_of_nonneg_right cst dr.le).trans paid
  have ep : 0≤E := by dsimp [E]; positivity
  have est := ThresholdUpperScalarRate.condition y1 qp ep qpay half
    (Ecap.trans (by nlinarith only [mul_le_mul_of_nonneg_right b2 (pow_nonneg yp.le 160),pow_nonneg yp.le 160]))
    Wcap conditional
  change L≤_
  linarith
#print axioms first_rate
end ThresholdUpperFirstRate
