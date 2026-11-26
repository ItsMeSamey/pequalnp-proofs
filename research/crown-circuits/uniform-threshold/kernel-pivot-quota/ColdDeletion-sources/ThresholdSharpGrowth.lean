import ThresholdReceiverScale
import ThresholdSharpTerminalRatio
namespace ThresholdSharpGrowth

theorem small_multiple (t E B K : ℝ) (tp : 0<t) (ep : 0≤E) (kp : 0≤K)
    (branch : E^5≤B*t^3) (cut : K^5*B≤t^2) : K*E≤t := by
  have a := mul_le_mul_of_nonneg_left branch (pow_nonneg kp 5)
  have b := mul_le_mul_of_nonneg_right cut (pow_nonneg tp.le 3)
  have p : (K*E)^5≤t^5 := by nlinarith only [a,b]
  by_contra! bad
  exact (not_lt.mpr p) (pow_lt_pow_left₀ bad tp.le (by decide))

theorem dense (t E B g w : ℝ) (tp : 0≤t) (ep : 0≤E) (bp : 0≤B)
    (wp : 0≤w) (branch : E^5≤B*t^3) (rows : t≤4*g)
    (size : w≤3000*E) (cut : (3000:ℝ)^15*4^10*B^3≤t) : w^3≤g^2 := by
  have p1 := pow_le_pow_left₀ wp size 15
  have p2 := pow_le_pow_left₀ (pow_nonneg ep 5) branch 3
  have p3 := pow_le_pow_left₀ tp rows 10
  have p4 := mul_le_mul_of_nonneg_right cut (pow_nonneg tp 9)
  have p5 := mul_le_mul_of_nonneg_left p2 (show (0:ℝ)≤3000^15 by norm_num)
  have power : (w^3)^5≤(g^2)^5 := by nlinarith only [p1,p3,p4,p5]
  by_contra! bad
  exact (not_lt.mpr power) (pow_lt_pow_left₀ bad (sq_nonneg g) (by decide))

theorem coarse_degree (T w F g D2 P Q : ℝ) (wt : w^2≤P) (fc : 6*w^2*F≤Q^2)
    (pos : 0≤T) (qp : 0≤Q) (moment : 2*T^2≤w^2*(T+6*F))
    (degree : D2=2*T+2*g) : T≤P+Q ∧ D2≤2*(P+Q)+2*g := by
  have linear := mul_le_mul_of_nonneg_right wt pos
  have bound : T≤P+Q := by
    by_contra! bad
    have pp : 0≤P := (sq_nonneg w).trans wt
    have tt : Q<T := by linarith
    have one := mul_pos (sub_pos.mpr tt) (show 0<T+Q by linarith)
    have two := mul_nonneg (show 0≤T-P by linarith) pos
    nlinarith only [moment,linear,fc,one,two]
  exact ⟨bound,by linarith⟩

theorem rows_close (h g J eps : ℝ) (hp : 0≤h) (ep : 0≤eps)
    (error : (h-g)^5≤J^5*h^4) (cut : J^5≤eps^5*h) :
    (1-eps)*h≤g := by
  have prod := mul_le_mul_of_nonneg_right cut (pow_nonneg hp 4)
  have cap : (h-g)^5≤(eps*h)^5 := by nlinarith only [error,prod]
  by_contra! bad
  have greater : eps*h<h-g := by linarith
  exact (not_lt.mpr cap) (pow_lt_pow_left₀ greater (mul_nonneg ep hp) (by decide))

theorem terminal_close {n : ℕ} {A eps : ℝ} (large : 128≤n) (ep : 0<eps)
    (epsCut : 18≤eps^2*(n:ℝ)) (fixedCut : A≤(n:ℝ)^2)
    (sur : (ThresholdThirdDeletion.surplus n)^10≤A*(n:ℝ)^3) :
    ∃ m : ℕ, 2≤m ∧ m≤n ∧ ThresholdThirdDeletion.RegularOrder m ∧
      ThresholdPublicMinimum.minimum m+3*(n-m)≤ThresholdPublicMinimum.minimum n ∧
      (n:ℝ)-(m:ℝ)≤3*Real.sqrt (2*(n:ℝ)) ∧
      (1-eps)*(n:ℝ)≤(m:ℝ) ∧ ThresholdThirdDeletion.surplus m≤ThresholdThirdDeletion.surplus n := by
  have one : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  exact ThresholdSharpTerminalRatio.ratio large ep epsCut
    (ThresholdSharpTerminalRatio.bounded_to_sqrt one fixedCut sur)

#print axioms small_multiple
#print axioms dense
#print axioms coarse_degree
#print axioms rows_close
#print axioms terminal_close
end ThresholdSharpGrowth
