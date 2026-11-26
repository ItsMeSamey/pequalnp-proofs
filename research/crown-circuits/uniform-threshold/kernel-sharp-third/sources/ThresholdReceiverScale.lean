import ThresholdThirdPower
namespace ThresholdReceiverScale

theorem good_half (t E h l d a g : ℝ)
    (ep : 0≤E) (small : (2:ℝ)^50*E≤t) (th : t≤2*h)
    (wide : d^2≤32*t*E) (few : l≤730*E) (ands : a≤930*E)
    (count : h≤l+g+d+2*a) : h≤2*g := by
  have tp : 0≤t := by nlinarith [small]
  have dsq := mul_le_mul_of_nonneg_left small tp
  have dsmall : 16*d≤t := by
    by_contra! bad
    have pos := mul_pos (sub_pos.mpr bad) (show 0<16*d+t by linarith)
    nlinarith only [pos,wide,dsq]
  nlinarith only [dsmall,th,few,ands,count,small,ep]

theorem receiver_size (w l a E : ℝ) (one : 1≤E)
    (bound : w≤l+2*a+1) (few : l≤730*E) (ands : a≤930*E) : w≤3000*E := by linarith

theorem receiver_dense (t E h g w : ℝ) (ht : (2:ℝ)^200≤t)
    (ep : 0≤E) (gp : 0≤g) (wp : 0≤w) (small : E^5≤t^3)
    (th : t≤2*h) (half : h≤2*g) (size : w≤3000*E) : w^3≤g^2 := by
  have tp : 0≤t := by linarith
  have tpos : 0<t := by linarith
  have p1 := pow_le_pow_left₀ wp size 15
  have p2 := pow_le_pow_left₀ (pow_nonneg ep 5) small 3
  have p3 := pow_le_pow_left₀ tp (show t≤4*g by linarith) 10
  have coef : (3000:ℝ)^15*4^10 ≤ t := by
    exact le_trans (by norm_num : (3000:ℝ)^15*4^10≤2^200) ht
  have p4 := mul_le_mul_of_nonneg_right coef (pow_nonneg tp 9)
  have power : (w^3)^5≤(g^2)^5 := by
    nlinarith only [p1,p2,p3,p4]
  by_contra! no
  exact (not_lt.mpr power) (pow_lt_pow_left₀ no (sq_nonneg g) (by decide))

end ThresholdReceiverScale
