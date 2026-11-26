import Std
namespace MomentTrade

inductive Cube (α : Type) : Nat → Type where
  | leaf (a : α) : Cube α 0
  | fork {n} (lo hi : Cube α n) : Cube α (n+1)

inductive Mask : Nat → Type where
  | nil : Mask 0
  | cons {n} (take : Bool) (tail : Mask n) : Mask (n+1)

def degree : Mask n → Nat
  | .nil => 0
  | .cons false m => degree m
  | .cons true m => degree m + 1

-- Each selected coordinate contributes its Boolean value as a factor.
def moment : Cube Int n → Mask n → Int
  | .leaf a, .nil => a
  | .fork lo hi, .cons false m => moment lo m + moment hi m
  | .fork _ hi, .cons true m => moment hi m

def mass (f : Int → Nat) : Cube Int n → Nat
  | .leaf a => f a
  | .fork lo hi => mass f lo + mass f hi

def nonzero : Cube Int n → Prop
  | .leaf a => a ≠ 0
  | .fork lo hi => nonzero lo ∨ nonzero hi

def zeroMask : (n : Nat) → Mask n
  | 0 => .nil
  | n+1 => .cons false (zeroMask n)

theorem deg_zeroMask (n : Nat) : degree (zeroMask n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def pos (a : Int) := a.toNat
def neg (a : Int) := (-a).toNat

theorem total (w : Cube Int n) :
    moment w (zeroMask n) = ((mass pos w : Nat) : Int) - (mass neg w : Nat) := by
  induction w with
  | leaf a =>
    simp only [moment, zeroMask, mass, pos, neg]
    omega
  | fork lo hi hl hh =>
    simp only [zeroMask, moment, mass, hl, hh]
    omega

theorem nonzero_mass (w : Cube Int n) (h : nonzero w) :
    0 < mass pos w + mass neg w := by
  induction w with
  | leaf a =>
    change a ≠ 0 at h
    simp only [mass, pos, neg]
    omega
  | fork lo hi hl hh =>
    rcases h with h | h
    · specialize hl h
      simp only [mass]
      omega
    · specialize hh h
      simp only [mass]
      omega

theorem moment_inactive (w : Cube Int n) (h : ¬nonzero w) (m : Mask n) :
    moment w m = 0 := by
  induction w with
  | leaf a =>
    cases m
    change ¬a ≠ 0 at h
    exact Classical.byContradiction h
  | fork lo hi hl hh =>
    have l := hl (fun q => h (Or.inl q))
    have u := hh (fun q => h (Or.inr q))
    cases m with
    | cons b tail =>
      cases b <;> simp [moment, l, u]

def Vanishes (w : Cube Int n) (r : Nat) :=
  ∀ m : Mask n, degree m ≤ r → moment w m = 0

theorem trade_bound (w : Cube Int n) (r : Nat) (hw : nonzero w) (hz : Vanishes w r) :
    2^r ≤ mass pos w ∧ 2^r ≤ mass neg w := by
  induction w generalizing r with
  | leaf a =>
    have v := hz .nil (Nat.zero_le _)
    exact False.elim (hw v)
  | fork lo hi il iu =>
    have common (m) (hm : degree m ≤ r) : moment lo m + moment hi m = 0 :=
      hz (.cons false m) hm
    by_cases hl : nonzero lo
    · by_cases hu : nonzero hi
      · cases r with
        | zero =>
          have e := total (.fork lo hi)
          have z := hz (zeroMask _) (by rw [deg_zeroMask]; omega)
          have nz := nonzero_mass (.fork lo hi) hw
          rw [z] at e
          simp only [Nat.pow_zero]
          omega
        | succ k =>
          have zh : Vanishes hi k := fun m hm => hz (.cons true m) (Nat.succ_le_succ hm)
          have zl : Vanishes lo k := by
            intro m hm
            have e := common m (by omega)
            rw [zh m hm] at e
            omega
          obtain ⟨lp,ln⟩ := il k hl zl
          obtain ⟨up,un⟩ := iu k hu zh
          simp only [Nat.pow_succ, mass]
          omega
      · have zl : Vanishes lo r := by
          intro m hm
          have e := common m hm
          rw [moment_inactive hi hu m] at e
          omega
        obtain ⟨lp,ln⟩ := il r hl zl
        simp only [mass]
        omega
    · have hu := hw.resolve_left hl
      have zh : Vanishes hi r := by
        intro m hm
        have e := common m hm
        rw [moment_inactive lo hl m] at e
        omega
      obtain ⟨up,un⟩ := iu r hu zh
      simp only [mass]
      omega
end MomentTrade
