import Q1DoubleTriangleRules
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge112 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^1 ≤ w+k+x) (fs : 2^1 ≤ w+l+y) (ft : 2^2 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 1 1 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 1 2 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 1 2 gain)
    (sa : smallRule (w+k+x) 1 w 1 k 2 gain)
    (sb : smallRule (w+l+y) 1 w 1 l 2 gain)
    (sc : smallRule (k+l+z) 2 k 1 l 1 gain) :
    2*(1+1+2) ≤ w+k+l+x+y+z+2+gain := by
  clear ab ac bc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
