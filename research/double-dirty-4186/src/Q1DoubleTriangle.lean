import Q1DoubleTriangleCase112
import Q1DoubleTriangleCasesA
import Q1DoubleTriangleCasesB
import Q1DoubleTriangleCasesC
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge (w k l x y z r s t gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^r ≤ w+k+x) (fs : 2^s ≤ w+l+y) (ft : 2^t ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w r s gain)
    (ac : pairRule (w+k+x) (k+l+z) k r t gain)
    (bc : pairRule (w+l+y) (k+l+z) l s t gain)
    (sa : smallRule (w+k+x) r w s k t gain)
    (sb : smallRule (w+l+y) s w r l t gain)
    (sc : smallRule (k+l+z) t k r l s gain) :
    2*(r+s+t) ≤ w+k+l+x+y+z+2+gain := by
  by_cases h : 5 ≤ max r (max s t)
  · have htail := exponential_tail _ h
    rcases le_total s t with hst | hts
    · rw [max_eq_right hst] at htail
      rcases le_total r t with hrt | htr
      · rw [max_eq_right hrt] at htail; omega
      · rw [max_eq_left htr] at htail; omega
    · rw [max_eq_left hts] at htail
      rcases le_total r s with hrs | hsr
      · rw [max_eq_right hrs] at htail; omega
      · rw [max_eq_left hsr] at htail; omega
  · have hr : r ≤ 4 := by omega
    have hs : s ≤ 4 := by omega
    have ht : t ≤ 4 := by omega
    clear h
    interval_cases r <;> interval_cases s <;> interval_cases t
    all_goals first
      | exact charge112 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge122 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge123 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge133 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge212 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge213 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge221 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge222 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge223 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge232 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge233 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge313 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge322 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge323 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge331 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge332 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge333 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | exact charge334 _ _ _ _ _ _ _ hw hk hl fr fs ft ab ac bc sa sb sc
      | clear ab ac bc sa sb sc; norm_num at fr fs ft ⊢ <;> omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
