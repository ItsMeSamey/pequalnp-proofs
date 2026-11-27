import Q1DoubleOneLeak
import Q1DoubleTriangleRules

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

/-- Enumerate every feasible saving up to the two batches' total size. Testing
whether an unpaid option exists is equivalent to testing their minimum. -/
def allowedGain (a b c r s g : ℕ) : Bool := by
  letI : Decidable (Triangle.pairRule a b c r s g) := by
    unfold Triangle.pairRule Triangle.singleForce Triangle.richPair
    infer_instance
  exact decide (Triangle.pairRule a b c r s g)

def pairOptions (a b c r s : ℕ) : List ℕ :=
  (List.range (r+s+1)).filter (allowedGain a b c r s)

theorem option_of_rule {a b c r s gain : ℕ} (small : gain ≤ r+s)
    (rule : Triangle.pairRule a b c r s gain) : gain ∈ pairOptions a b c r s := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr (by omega), by simpa [allowedGain] using rule⟩

structure Profile where
  k : ℕ
  x : ℕ
  z : ℕ
  b : ℕ
  w : ℕ
  r : ℕ
  s : ℕ
  h : ℕ
deriving DecidableEq, Repr

def Profile.budget (p : Profile) := p.k+p.x+p.z+p.b+p.w+1

def Profile.bad (p : Profile) : Bool :=
  let A := p.k+p.x+p.w
  let B := p.b+p.w
  let Y := p.k+p.z
  let cost := 2*(p.r+p.s+p.h)
  decide (p.budget < cost ∧ 2^p.r ≤ A ∧ 2^p.s ≤ B ∧ 2^p.h ≤ Y) &&
    (pairOptions A Y p.k p.r p.h).any (fun i => decide (p.budget+i < cost)) &&
    (pairOptions A B p.w p.r p.s).any (fun i => decide (p.budget+i < cost))

/-- Inclusive integer interval represented as a list, with an empty interval when hi<lo. -/
def span (lo hi : ℕ) : List ℕ := (List.range (hi+1-lo)).map (lo+·)

private theorem in_span {v lo hi : ℕ} (hl : lo ≤ v) (hh : v ≤ hi) : v ∈ span lo hi := by
  apply List.mem_map.mpr
  exact ⟨v-lo,List.mem_range.mpr (by omega),by omega⟩

/-- Enumerate only positive-deficit candidates that already satisfy all three
transversal bounds. For each batch triple these are short intervals. -/
def row (r s h : ℕ) : List Profile :=
  let U := 2*(r+s+h)-2
  (span 3 (U-4)).flatMap fun k =>
  (span 1 (U-k-3)).flatMap fun w =>
    let loX := 2^r-k-w
    let loZ := max 1 (2^h-k)
    let loB := max 2 (2^s-w)
    (span loX (U-k-w-loZ-loB)).flatMap fun x =>
    (span loZ (U-k-w-x-loB)).flatMap fun z =>
    (span loB (U-k-w-x-z)).filterMap fun b =>
      let p : Profile := ⟨k,x,z,b,w,r,s,h⟩
      if p.bad then some p else none

def rowBand (r s : ℕ) : List Profile := (List.range 5).flatMap (row r s)
def leftover (p : Profile) : Bool := decide (p = ⟨3,0,1,2,2,2,2,2⟩ ∨ p = ⟨3,0,1,3,1,2,2,2⟩)

/-- A positive unpaid deficit is bounded before the finite search is used. -/
theorem small_of_bad (p : Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z)
    (hb : 2 ≤ p.b) (hw : 1 ≤ p.w) (bad : p.bad = true) :
    p.k+p.x+p.z+p.b+p.w ≤ 22 ∧ p.r < 5 ∧ p.s < 5 ∧ p.h < 5 := by
  have floors := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp bad).1).1
  obtain ⟨deficit,hr,hs,hh⟩ := of_decide_eq_true floors
  unfold Profile.budget at deficit
  by_cases r : 5 ≤ p.r
  · by_cases s : p.r ≤ p.s
    · by_cases h : p.s ≤ p.h
      · have := pow_six (m := p.h) (by omega); omega
      · have := pow_six (m := p.s) (by omega); omega
    · by_cases h : p.r ≤ p.h
      · have := pow_six (m := p.h) (by omega); omega
      · have := pow_six r; omega
  · by_cases s : 5 ≤ p.s
    · by_cases h : p.s ≤ p.h
      · have := pow_six (m := p.h) (by omega); omega
      · have := pow_six s; omega
    · by_cases h : 5 ≤ p.h
      · have := pow_six h; omega
      · omega

theorem in_row (p : Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z)
    (hb : 2 ≤ p.b) (hw : 1 ≤ p.w) (bad : p.bad = true) : p ∈ row p.r p.s p.h := by
  have hbounds := bad
  have floors := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hbounds).1).1
  obtain ⟨deficit,ar,bs,yh⟩ := of_decide_eq_true floors
  unfold Profile.budget at deficit
  unfold row
  apply List.mem_flatMap.mpr
  refine ⟨p.k,in_span hk (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p.w,in_span hw (by omega),?_⟩
  have z : max 1 (2^p.h-p.k) ≤ p.z := max_le hz (by omega)
  have b : max 2 (2^p.s-p.w) ≤ p.b := max_le hb (by omega)
  apply List.mem_flatMap.mpr
  refine ⟨p.x,in_span (by omega) (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p.z,in_span z (by omega),?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨p.b,in_span b (by omega),?_⟩
  change (if p.bad then some p else none) = some p
  simp [bad]

-- Independent kernel reductions keep each arithmetic certificate bounded.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0_0 : (rowBand 0 0).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0_1 : (rowBand 0 1).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0_2 : (rowBand 0 2).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0_3 : (rowBand 0 3).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0_4 : (rowBand 0 4).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1_0 : (rowBand 1 0).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1_1 : (rowBand 1 1).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1_2 : (rowBand 1 2).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1_3 : (rowBand 1 3).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1_4 : (rowBand 1 4).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2_0 : (rowBand 2 0).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2_1 : (rowBand 2 1).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2_2 : (rowBand 2 2).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2_3 : (rowBand 2 3).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2_4 : (rowBand 2 4).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3_0 : (rowBand 3 0).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3_1 : (rowBand 3 1).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3_2 : (rowBand 3 2).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3_3 : (rowBand 3 3).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3_4 : (rowBand 3 4).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4_0 : (rowBand 4 0).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4_1 : (rowBand 4 1).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4_2 : (rowBand 4 2).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4_3 : (rowBand 4 3).all leftover = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4_4 : (rowBand 4 4).all leftover = true := by decide +kernel

theorem bad_exact (p : Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z)
    (hb : 2 ≤ p.b) (hw : 1 ≤ p.w) (bad : p.bad = true) :
    p = ⟨3,0,1,2,2,2,2,2⟩ ∨ p = ⟨3,0,1,3,1,2,2,2⟩ := by
  obtain ⟨_,hr,hs,hh⟩ := small_of_bad p hk hz hb hw bad
  have verify (r s : ℕ) (ra : r<5) (sa : s<5) : (rowBand r s).all leftover=true := by
    interval_cases r <;> interval_cases s
    · exact checked_0_0
    · exact checked_0_1
    · exact checked_0_2
    · exact checked_0_3
    · exact checked_0_4
    · exact checked_1_0
    · exact checked_1_1
    · exact checked_1_2
    · exact checked_1_3
    · exact checked_1_4
    · exact checked_2_0
    · exact checked_2_1
    · exact checked_2_2
    · exact checked_2_3
    · exact checked_2_4
    · exact checked_3_0
    · exact checked_3_1
    · exact checked_3_2
    · exact checked_3_3
    · exact checked_3_4
    · exact checked_4_0
    · exact checked_4_1
    · exact checked_4_2
    · exact checked_4_3
    · exact checked_4_4
  have present : p ∈ rowBand p.r p.s :=
    List.mem_flatMap.mpr ⟨p.h,List.mem_range.mpr hh,in_row p hk hz hb hw bad⟩
  exact of_decide_eq_true ((List.all_eq_true.mp (verify _ _ hr hs)) p present)

/-- Apply both pair tests using independently available cover bounds. Their savings
are never added. In the only unpaid profiles, the external four-slot certificate
supplies three shared exact patterns and the first batch is nonempty. -/
theorem pay_large (p : Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z) (hb : 2 ≤ p.b)
    (hw : 1 ≤ p.w) (saving : ℕ)
    (ar : 2^p.r ≤ p.k+p.x+p.w) (bs : 2^p.s ≤ p.b+p.w) (yh : 2^p.h ≤ p.k+p.z)
    (armExt : ∃ i ∈ pairOptions (p.k+p.x+p.w) (p.k+p.z) p.k p.r p.h, i ≤ saving)
    (armArm : ∃ i ∈ pairOptions (p.k+p.x+p.w) (p.b+p.w) p.w p.r p.s, i ≤ saving)
    (exactFour : p.k = 3 → p.k+p.z = 4 → p.h = 2 → p.r = 0) :
    2*(p.r+p.s+p.h) ≤ p.budget+saving := by
  by_contra! short
  obtain ⟨i,hi,iv⟩ := armExt
  obtain ⟨j,hj,jv⟩ := armArm
  have bad : p.bad = true := by
    simp only [Profile.bad, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨⟨⟨by omega,ar,bs,yh⟩,i,hi,by omega⟩,j,hj,by omega⟩
  rcases bad_exact p hk hz hb hw bad with rfl | rfl <;>
    have absurd := exactFour rfl rfl rfl <;> contradiction

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
