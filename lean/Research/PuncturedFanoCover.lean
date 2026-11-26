import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Fin

namespace PuncturedFanoCover
open Fin.NatCast

abbrev Label := Fin 7

def punctured : Finset Label := Finset.univ.erase 1

def incident (r c : Label) : Prop := r = c ∨ r = c + 1 ∨ r = c + 3

def neighbors (C : Finset Label) : Finset Label :=
  Finset.univ.filter fun r => ∃ c ∈ C, r = c ∨ r = c + 1 ∨ r = c + 3

theorem strict_expansion {C : Finset Label} (h : C.Nonempty) (hmiss : 1 ∉ C) :
    C.card < (neighbors C).card := by
  have selfSub : C ⊆ neighbors C := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, Or.inl rfl⟩
  by_contra! hle
  have heq := Finset.eq_of_subset_of_card_le selfSub hle
  have closed (c : Label) (hc : c ∈ C) : c + 1 ∈ C := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, Or.inr (Or.inl rfl)⟩
  obtain ⟨c, hc⟩ := h
  have orbit (n : ℕ) : c + (n : Label) ∈ C := by
    induction n with
    | zero => simpa using hc
    | succ k ih => simpa [Nat.cast_succ, add_assoc] using closed _ ih
  let k : Label := 1 - c
  have hk : c + k = 1 := by simp [k]
  have hk' := orbit k.val
  have hcast : (k.val : Label) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [hcast] at hk'
  exact hmiss (hk ▸ hk')

theorem unique_min_cover (R C : Finset Label) (hc : C ⊆ punctured)
    (cover : ∀ c ∈ punctured, ∀ r, incident r c → r ∈ R ∨ c ∈ C)
    (budget : R.card + C.card ≤ 6) : R = ∅ ∧ C = punctured := by
  have hsize : punctured.card = 6 := by decide
  by_cases hall : C = punctured
  · subst C
    simp_all
  have hn : (punctured \ C).Nonempty := by
    by_contra! hempty
    exact hall (Finset.Subset.antisymm hc (Finset.sdiff_eq_empty_iff_subset.mp hempty))
  have hm : 1 ∉ punctured \ C := by simp [punctured]
  have hsub : neighbors (punctured \ C) ⊆ R := by
    intro r hr
    obtain ⟨_, c, hc', he⟩ := Finset.mem_filter.mp hr
    obtain ⟨hp, hnc⟩ := Finset.mem_sdiff.mp hc'
    exact (cover c hp r he).resolve_right hnc
  have hlt := strict_expansion hn hm
  have hle := Finset.card_le_card hsub
  have hdiff := Finset.card_sdiff_add_card_eq_card hc
  omega

end PuncturedFanoCover
