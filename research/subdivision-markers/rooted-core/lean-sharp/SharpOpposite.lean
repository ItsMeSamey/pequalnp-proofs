import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The sharp full-selector estimate. The code-packing proof punctures one
coordinate of an odd word. This avoids choosing bases of kernels or quotients. -/
namespace SharpOpposite
open scoped BigOperators
abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := Fin n → Bit

private theorem word_self {n} (x : Word n) : x+x=0 := by
  funext k
  exact CharTwo.add_self_eq_zero (x k)

private theorem word_add_zero_iff {n} {x y : Word n} (h : x+y=0) : x=y := by
  funext k
  exact CharTwo.add_eq_zero.mp (congrFun h k)

def good {n} (J : Word n →ₗ[Bit] Word n) (x : Word n) : Prop :=
  ∀ i, x i * J x i = 0

structure Data (n t : ℕ) where
  J : Word n →ₗ[Bit] Word n
  L : Word n →ₗ[Bit] Word t
  a : Word n
  symmetric : ∀ x y, ∑ i, x i * J y i = ∑ i, y i * J x i
  alternating : ∀ x, ∑ i, x i * J x i = 0
  full : J a = 1 + a
  ones : J 1 = 1
  distinct : L 1 ≠ 0
  unique : ∀ s, good J s → (L s = L a ∨ L s = L (a+1)) → s = a ∨ s = a+1

variable {n t : ℕ}

def unitWord (i : Fin n) : Word n := fun k => if i = k then 1 else 0

def word (D : Data n t) (z : Word n) : Word n := z + D.J z

def slice (D : Data n t) (z : Word n) : Prop := D.L z = 0 ∨ D.L z = D.L 1

private theorem point₀ : ∀ a z j : Bit, (a+z)*(1+a+j)=(a+z)*(z+j) := by decide
private theorem point₁ : ∀ a z j : Bit, (a+z+1)*(1+a+j+1)=(a+z+1)*(z+j) := by decide
private theorem bitSplit : ∀ b : Bit, b=0 ∨ b+1=0 := by decide

private theorem conflict₀ (D : Data n t) (z : Word n) (k : Fin n) :
    (D.a+z) k * D.J (D.a+z) k = (D.a+z) k * word D z k := by
  simpa [map_add, D.full, word] using point₀ (D.a k) (z k) (D.J z k)

private theorem conflict₁ (D : Data n t) (z : Word n) (k : Fin n) :
    (D.a+z+1) k * D.J (D.a+z+1) k = (D.a+z+1) k * word D z k := by
  simpa [map_add, D.full, D.ones, word] using point₁ (D.a k) (z k) (D.J z k)

theorem word_even (D : Data n t) (z : Word n) : ∑ i, word D z i = 0 := by
  have hz : ∑ i, D.J z i = ∑ i, z i := by
    simpa [D.ones] using D.symmetric 1 z
  simp [word, Finset.sum_add_distrib, hz, CharTwo.add_self_eq_zero]

private theorem collapse (D : Data n t) (z : Word n) (hs : slice D z)
    (hg : good D.J (D.a+z)) : z=0 ∨ z=1 := by
  have ht : D.L (D.a+z) = D.L D.a ∨ D.L (D.a+z) = D.L (D.a+1) := by
    rcases hs with h|h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  rcases D.unique _ hg ht with h|h
  · exact Or.inl (add_left_cancel (show D.a+z=D.a+0 by simpa using h))
  · exact Or.inr (add_left_cancel h)

private theorem twoTerms (f : Word n) (i j : Fin n) :
    ∑ k, f k * ((unitWord i + unitWord j) k) = f i + f j := by
  simp [unitWord, mul_add, Finset.sum_add_distrib, mul_ite]

private theorem kill (f : Word n) (i j : Fin n) (hi : f i = 0) (hj : f j = 0)
    (k : Fin n) : f k * ((unitWord i + unitWord j) k) = 0 := by
  by_cases h : i=k
  · subst k; simp [hi]
  by_cases h' : j=k
  · subst k; simp [hj]
  simp [unitWord, h, h']

/-- The even code on the projected score kernel has no two-site word.
Taking `i=j` also treats the kernel of the map to codewords. -/
theorem two_sites (D : Data n t) (z : Word n) (hs : slice D z) (i j : Fin n)
    (hw : word D z = unitWord i + unitWord j) : z=0 ∨ z=1 := by
  have hsum := D.alternating (D.a+z)
  simp_rw [conflict₀ D z, hw] at hsum
  rw [twoTerms] at hsum
  have hij : (D.a+z) i = (D.a+z) j := CharTwo.add_eq_zero.mp hsum
  rcases bitSplit ((D.a+z) i) with hi|hi
  · apply collapse D z hs
    intro k
    rw [conflict₀, hw]
    exact kill _ i j hi (hij ▸ hi) k
  · have hg : good D.J (D.a+(z+1)) := by
      rw [← add_assoc]
      intro k
      rw [conflict₁, hw]
      exact kill _ i j hi (show (D.a+z) j + 1=0 by rw [← hij]; exact hi) k
    have hs' : slice D (z+1) := by
      rcases hs with h|h
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simp [h, word_self])
    rcases collapse D (z+1) hs' hg with h|h
    · exact Or.inr (word_add_zero_iff h)
    · exact Or.inl (add_right_cancel (show z+1=0+1 by simpa using h))

def support (x : Word n) : Finset (Fin n) := Finset.univ.filter (fun i => x i = 1)

private theorem bit_indicator : ∀ b : Bit, (if b=1 then (1 : Bit) else 0) = b := by decide
private theorem bit_ne_one : ∀ b : Bit, b ≠ 1 → b = 0 := by decide

theorem even_weight (D : Data n t) (z : Word n) : Even (support (word D z)).card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  simpa only [support, Finset.natCast_card_filter, bit_indicator] using
    (show (∑ i, word D z i) = 0 from word_even D z)

/-- Every nonzero word on the projected score kernel has Hamming weight at least four. -/
theorem minimum_weight (D : Data n t) (z : Word n) (hs : slice D z)
    (hn : word D z ≠ 0) : 4 ≤ (support (word D z)).card := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, word D z k ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  have hm : k ∈ support (word D z) := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    exact hk (bit_ne_one _ h)
  have hpos := Finset.card_pos.mpr ⟨k,hm⟩
  obtain ⟨c,hc⟩ := even_weight D z
  by_contra! hsmall
  have htwo : (support (word D z)).card = 2 := by omega
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp htwo
  have hw : word D z = unitWord i + unitWord j := by
    funext l
    have hl : word D z l = 1 ↔ l=i ∨ l=j := by
      have he : l ∈ support (word D z) ↔ l ∈ ({i,j} : Finset _) := by rw [hpair]
      simpa [support] using he
    by_cases hi : i=l
    · subst l; simp [unitWord, Ne.symm hij, hl.mpr (Or.inl rfl)]
    by_cases hj : j=l
    · subst l; simp [unitWord, hij, hl.mpr (Or.inr rfl)]
    have hzero := bit_ne_one _ (fun h => (hl.mp h).elim (Ne.symm hi) (Ne.symm hj))
    simp [unitWord, hi, hj, hzero]
  rcases two_sites D z hs i j hw with h|h
  · exact hn (by simp [word,h])
  · exact hn (by simp [word,h,D.ones,word_self])

private theorem word_add (D : Data n t) (x y : Word n) :
    word D (x+y) = word D x + word D y := by simp [word, map_add]; abel

private theorem parity_error (D : Data n t) (x : Word n) (i : Fin n) :
    ∑ k, (word D x + unitWord i) k = 1 := by
  simp [unitWord, Finset.sum_add_distrib, word_even]

private theorem recover_head {m} (x y : Word (m+1))
    (hp : ∑ i, x i = ∑ i, y i) (ht : ∀ k : Fin m, x k.succ = y k.succ) : x=y := by
  simp only [Fin.sum_univ_succ, ht] at hp
  have h0 : x 0 = y 0 := add_right_cancel hp
  funext i
  exact Fin.cases h0 ht i

/-- A single-error word with its first bit punctured and its original score
identifies both the selector and the error coordinate. -/
private theorem packing {m} (D : Data (m+1) t) :
    Function.Injective (fun p : Word (m+1) × Fin (m+1) =>
      ((fun k : Fin m => (word D p.1 + unitWord p.2) k.succ), D.L p.1)) := by
  rintro ⟨x,i⟩ ⟨y,j⟩ h
  have ht := congrArg Prod.fst h
  have hl : D.L x = D.L y := congrArg Prod.snd h
  have he : word D x + unitWord i = word D y + unitWord j :=
    recover_head _ _ ((parity_error D x i).trans (parity_error D y j).symm) (congrFun ht)
  have hs : D.L (x+y)=0 := by simp [hl, word_self]
  have hw : word D (x+y) = unitWord i + unitWord j := by
    rw [word_add]
    calc
      word D x + word D y = (word D x + unitWord i) + word D y + unitWord i := by
        rw [add_right_comm (word D x) (unitWord i), add_assoc, word_self, add_zero]
      _ = unitWord i + unitWord j := by
        rw [he]
        rw [add_right_comm (word D y) (unitWord j), word_self, zero_add]
        exact add_comm _ _
  have hxy : x=y := by
    rcases two_sites D (x+y) (Or.inl hs) i j hw with hz|hz
    · exact word_add_zero_iff hz
    · exact (D.distinct (hz ▸ hs)).elim
  subst y
  have hij : unitWord i = unitWord j := add_left_cancel he
  have hn : i=j := by
    by_contra hne
    have := congrFun hij i
    simp [unitWord, Ne.symm hne] at this
  subst j
  rfl

/-- With `t+1` score bits the number of ordinary sites is at most `2^t`. -/
theorem sharp_bound (D : Data n (t+1)) : n ≤ 2^t := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have h := Fintype.card_le_of_injective _ (packing D)
    simp only [Word, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
    change 2^(m+1)*(m+1) ≤ 2^m*2^(t+1) at h
    have h' : 2^(m+1)*(m+1) ≤ 2^(m+1)*2^t := by
      calc
        _ ≤ 2^m*2^(t+1) := h
        _ = _ := by simp only [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_left h' (by positivity)

end SharpOpposite
