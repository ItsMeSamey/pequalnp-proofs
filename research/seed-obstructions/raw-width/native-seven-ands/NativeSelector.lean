import ResolveUnion

namespace ThresholdStarWindow

open Research.Graph9822Resolution

/-- Each entry is a physical AND write address, independent of later reads. -/
def andSites : List Gate → Nat → List Nat
  | [], _ => []
  | g :: tail, i =>
    if g.isAnd then i :: andSites tail (i+1) else andSites tail (i+1)

def andCount (gs : List Gate) := (gs.filter (fun g => g.isAnd)).length

theorem andSites_length (gs : List Gate) (i : Nat) : (andSites gs i).length = andCount gs := by
  induction gs generalizing i with
  | nil => rfl
  | cons g tail ih =>
    cases h : g.isAnd <;> simp [andSites, andCount, h, ih]

private theorem congr_on_and (gs : List Gate) (i : Nat) (s t w : Wire)
    (h : ∀ j ∈ andSites gs i, s j = t j) : resolve gs i s w = resolve gs i t w := by
  induction gs generalizing i w with
  | nil => rfl
  | cons g tail ih =>
    have rest : ∀ j ∈ andSites tail (i+1), s j = t j := by
      intro j hj
      apply h
      cases hg : g.isAnd <;> simp [andSites, hg, hj]
    have gateEq : resolved g (s i) (w g.left) (w g.right) =
        resolved g (t i) (w g.left) (w g.right) := by
      cases hg : g.isAnd
      · simp [resolved, hg]
      · rw [h i (by simp [andSites, hg])]
    simp only [resolve, gateEq]
    exact ih _ _ rest

/-- Each raw wire is an OR of primitive bits. Empty lists encode zero,
and a true bias supplies an optional constant one. -/
def bankWire (raw : Nat → List Nat) (bias : Wire) (m : Nat) : Wire := fun j =>
  bias j || (raw j).any (fun k => m.testBit k)

private theorem bank_union_dom (raw : Nat → List Nat) (bias : Wire) (p a b : Nat)
    (sub : p &&& (a ||| b) = p) : ∀ j, bankWire raw bias p j = true →
        wireUnion (bankWire raw bias a) (bankWire raw bias b) j = true := by
  intro j hj
  change (bias j || (raw j).any _) = true at hj
  simp only [Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · simp [wireUnion, bankWire, hj]
  · obtain ⟨k, hk, hp⟩ := List.any_eq_true.mp hj
    have hb := congrArg (fun n : Nat => n.testBit k) sub
    simp only [Nat.testBit_and, Nat.testBit_or, hp, Bool.true_and] at hb
    simp only [Bool.or_eq_true] at hb
    rcases hb with ha | hb
    · have hit : (raw j).any (fun k => a.testBit k) = true := List.any_eq_true.mpr ⟨k, hk, ha⟩
      simp [wireUnion, bankWire, hit]
    · have hit : (raw j).any (fun k => b.testBit k) = true := List.any_eq_true.mpr ⟨k, hk, hb⟩
      simp [wireUnion, bankWire, hit]

/-- Distinct indexed negative rows require distinct physical AND-choice words
if their union dominates an accepted positive row. Fanout is arbitrary. -/
theorem selector_capacity (gs : List Gate) (start out : Nat)
    (raw : Nat → List Nat) (bias : Wire) {n : Nat} (neg : Fin n → Nat)
    (reject : ∀ j, eval gs start (bankWire raw bias (neg j)) out = false)
    (clash : ∀ j k, j ≠ k → ∃ p : Nat, p &&& (neg j ||| neg k) = p ∧
      eval gs start (bankWire raw bias p) out = true) : n ≤ 2 ^ andCount gs := by
  classical
  choose choice _hprefix agree using fun j => attains gs start (bankWire raw bias (neg j))
  let addrs := andSites gs start
  let code (j : Fin n) (k : Fin addrs.length) := choice j addrs[k.val]
  have inj : Function.Injective code := by
    intro j k h
    by_contra ne
    obtain ⟨p, cover, yes⟩ := clash j k ne
    have same : resolve gs start (choice j) (bankWire raw bias (neg k)) =
        resolve gs start (choice k) (bankWire raw bias (neg k)) := by
      apply congr_on_and
      intro l hl
      let idx : Fin addrs.length := ⟨addrs.idxOf l, List.idxOf_lt_length_iff.mpr hl⟩
      have eq := congrFun h idx
      simpa [code, idx, addrs, List.getElem_idxOf] using eq
    have hpos := lower gs start (choice j) _ _ (bank_union_dom raw bias p _ _ cover) out yes
    rw [resolve_union] at hpos
    change (resolve gs start (choice j) _ out || resolve gs start (choice j) _ out) = true at hpos
    rw [same, agree j, agree k, reject j, reject k] at hpos
    contradiction
  simpa [Fintype.card_fun, addrs, andSites_length] using Fintype.card_le_of_injective code inj

end ThresholdStarWindow
#print axioms ThresholdStarWindow.selector_capacity
