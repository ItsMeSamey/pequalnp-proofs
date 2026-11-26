import ThresholdThirdPower
namespace ThresholdCoarseDensity
theorem small_ratio {t E : ℝ} (cut : (2:ℝ)^200≤t) (small : E^5≤t^3) :
    (2:ℝ)^50*E≤t := by
  have t0 : 0≤t := by linarith
  have ts := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2^200) cut 2
  have prod := mul_le_mul_of_nonneg_right ts (pow_nonneg t0 3)
  by_contra! neg
  have bad := pow_lt_pow_left₀ neg t0 (by decide : 5≠0)
  have es := mul_le_mul_of_nonneg_left small (show (0:ℝ)≤2^250 by norm_num)
  nlinarith only [prod,bad,es,pow_nonneg t0 3]

/-- B is twice the usual K. -/
theorem parameters {t s E B h d : ℝ} (cut : (2:ℝ)^200≤t) (one : 1≤E)
    (ratio : (2:ℝ)^50*E≤t) (s0 : 0≤s) (ex : s≤t+E)
    (budget : B=s^2+7*s+14-t^2) (delta : d^2≤B) (d0 : 0≤d)
    (hubs : h=s+1-d) :
    t≤2*h ∧ h≤2*t ∧ B≤12*t*E ∧ 4≤h := by
  have t0 : 1≤t := by linarith
  have E0 : 0≤E := by linarith
  have B0 : 0≤B := le_trans (sq_nonneg d) delta
  have lb : t≤s+4 := by
    by_contra! lt
    have gap := mul_pos (sub_pos.mpr lt) (show 0<t+(s+4) by linarith)
    nlinarith
  have ex2 := pow_le_pow_left₀ s0 ex 2
  have ee := mul_le_mul_of_nonneg_right (show E≤t by linarith) E0
  have te := mul_le_mul_of_nonneg_left one (show 0≤t by linarith)
  have ecap := mul_le_mul_of_nonneg_right ratio (show 0≤t by linarith)
  have bound : B≤12*t*E := by nlinarith only [budget,ex2,ex,ee,te,ratio,cut,one]
  have hd : d≤t/4 := by
    by_contra! bad
    have pos := mul_pos (sub_pos.mpr bad) (show 0<d+t/4 by linarith)
    nlinarith only [pos,delta,bound,ecap]
  exact ⟨by linarith,by linarith,bound,by linarith⟩

theorem coarse {h L P q M C : ℝ} (h0 : 0<h) (L1 : h≤256*L) (L2 : 128*L≤h)
    (P0 : 0≤P) (sand : P*L≤h*L^2+h*C) (csmall : 65536*C≤h^2)
    (qsmall : 128*q≤h^2) (split : M=q+P) : 32*M≤h^2 := by
  have L0 : 0≤L := by linarith
  have lhs := mul_le_mul_of_nonneg_left L1 P0
  have aa := mul_le_mul_of_nonneg_right L2 L0
  have bb := mul_le_mul_of_nonneg_left aa h0.le
  have cc := mul_le_mul_of_nonneg_left csmall h0.le
  have small := mul_le_mul_of_nonneg_left qsmall h0.le
  have big := mul_le_mul_of_nonneg_right L2 (sq_nonneg h)
  have finish : h*(32*M)≤h*h^2 := by
    nlinarith only [lhs,sand,bb,cc,small,big,pow_nonneg h0.le 3,congrArg (fun z : ℝ => z*h) split]
  exact (mul_le_mul_iff_right₀ h0).mp finish

theorem budgets {t E h B q C : ℝ} (ht : 0≤t) (hh : 0≤h)
    (one : 1≤E) (ratio : (2:ℝ)^50*E≤t) (th : t≤2*h)
    (bound : B≤12*t*E) (cost : C≤B+3*h) (qle : 2*q≤B) :
    65536*C≤h^2 ∧ 128*q≤h^2 := by
  have lin := mul_le_mul_of_nonneg_right th (show 0≤E by linarith)
  have tiny := mul_le_mul_of_nonneg_left (show (2:ℝ)^50*E≤2*h by linarith) hh
  have hE := mul_le_mul_of_nonneg_left one hh
  constructor <;> nlinarith only [lin,tiny,hE,cost,qle,bound,hh,sq_nonneg h]

theorem divisor (h : Nat) (hh : 256≤h) :
    h≤256*(h/128) ∧ 128*(h/128)≤h := by omega
end ThresholdCoarseDensity
