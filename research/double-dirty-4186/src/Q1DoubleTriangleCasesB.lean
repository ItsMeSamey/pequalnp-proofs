import Q1DoubleTriangleRules
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge123 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^1 ≤ w+k+x) (fs : 2^2 ≤ w+l+y) (ft : 2^3 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 1 2 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 1 3 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 2 3 gain)
    (sa : smallRule (w+k+x) 1 w 2 k 3 gain)
    (sb : smallRule (w+l+y) 2 w 1 l 3 gain)
    (sc : smallRule (k+l+z) 3 k 1 l 2 gain) :
    2*(1+2+3) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge133 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^1 ≤ w+k+x) (fs : 2^3 ≤ w+l+y) (ft : 2^3 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 1 3 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 1 3 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 3 3 gain)
    (sa : smallRule (w+k+x) 1 w 3 k 3 gain)
    (sb : smallRule (w+l+y) 3 w 1 l 3 gain)
    (sc : smallRule (k+l+z) 3 k 1 l 3 gain) :
    2*(1+3+3) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge213 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^2 ≤ w+k+x) (fs : 2^1 ≤ w+l+y) (ft : 2^3 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 2 1 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 2 3 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 1 3 gain)
    (sa : smallRule (w+k+x) 2 w 1 k 3 gain)
    (sb : smallRule (w+l+y) 1 w 2 l 3 gain)
    (sc : smallRule (k+l+z) 3 k 2 l 1 gain) :
    2*(2+1+3) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge233 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^2 ≤ w+k+x) (fs : 2^3 ≤ w+l+y) (ft : 2^3 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 2 3 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 2 3 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 3 3 gain)
    (sa : smallRule (w+k+x) 2 w 3 k 3 gain)
    (sb : smallRule (w+l+y) 3 w 2 l 3 gain)
    (sc : smallRule (k+l+z) 3 k 2 l 3 gain) :
    2*(2+3+3) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge323 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^3 ≤ w+k+x) (fs : 2^2 ≤ w+l+y) (ft : 2^3 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 3 2 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 3 3 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 2 3 gain)
    (sa : smallRule (w+k+x) 3 w 2 k 3 gain)
    (sb : smallRule (w+l+y) 2 w 3 l 3 gain)
    (sc : smallRule (k+l+z) 3 k 3 l 2 gain) :
    2*(3+2+3) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 12000 in
theorem charge331 (w k l x y z gain : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (fr : 2^3 ≤ w+k+x) (fs : 2^3 ≤ w+l+y) (ft : 2^1 ≤ k+l+z)
    (ab : pairRule (w+k+x) (w+l+y) w 3 3 gain)
    (ac : pairRule (w+k+x) (k+l+z) k 3 1 gain)
    (bc : pairRule (w+l+y) (k+l+z) l 3 1 gain)
    (sa : smallRule (w+k+x) 3 w 3 k 1 gain)
    (sb : smallRule (w+l+y) 3 w 3 l 1 gain)
    (sc : smallRule (k+l+z) 1 k 3 l 3 gain) :
    2*(3+3+1) ≤ w+k+l+x+y+z+2+gain := by
  clear sa sb sc
  norm_num [pairRule, richPair, singleForce, smallRule] at * <;> omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
