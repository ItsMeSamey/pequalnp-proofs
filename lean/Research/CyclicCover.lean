import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Fin

namespace CyclicCover
open Fin.NatCast
theorem mem_of_succ_closed {n : ℕ} {C : Finset (Fin (n + 1))} (h : C.Nonempty)
    (closed : ∀ c ∈ C, c + 1 ∈ C) (gap : Fin (n + 1)) : gap ∈ C := by
  obtain ⟨c, hc⟩ := h
  have orbit (j : ℕ) : c + (j : Fin (n + 1)) ∈ C := by
    induction j with
    | zero => simpa using hc
    | succ k ih => simpa [Nat.cast_succ, add_assoc] using closed _ ih
  let k : Fin (n + 1) := gap - c
  have hk : c + k = gap := by simp [k]
  have hk' := orbit k.val
  have hcast : (k.val : Fin (n + 1)) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [hcast] at hk'
  exact hk ▸ hk'

theorem cyclic_expansion {n : ℕ} {C N : Finset (Fin (n + 1))}
    (h : C.Nonempty) {gap : Fin (n + 1)} (hmiss : gap ∉ C)
    (selfSub : C ⊆ N) (hsucc : ∀ c ∈ C, c + 1 ∈ N) : C.card < N.card := by
  by_contra! hle
  have heq := Finset.eq_of_subset_of_card_le selfSub hle
  exact hmiss (mem_of_succ_closed h (by simpa [heq] using hsucc) gap)

theorem unique_cover {n : ℕ} (available R C : Finset (Fin (n + 1)))
    {gap : Fin (n + 1)} (hgap : gap ∉ available) (hc : C ⊆ available)
    (cover : ∀ c ∈ available, c ∈ C ∨ c ∈ R ∧ c + 1 ∈ R)
    (budget : R.card + C.card ≤ available.card) : R = ∅ ∧ C = available := by
  by_cases hall : C = available
  · subst C
    simp_all
  have hn : (available \ C).Nonempty := by
    by_contra! hempty
    exact hall (Finset.Subset.antisymm hc (Finset.sdiff_eq_empty_iff_subset.mp hempty))
  have hm : gap ∉ available \ C := by simp [hgap]
  have hpair (c) (h : c ∈ available \ C) : c ∈ R ∧ c + 1 ∈ R :=
    (cover c (Finset.mem_sdiff.mp h).1).resolve_left (Finset.mem_sdiff.mp h).2
  have hlt := cyclic_expansion hn hm (fun c h => (hpair c h).1) (fun c h => (hpair c h).2)
  have hdiff := Finset.card_sdiff_add_card_eq_card hc
  omega
end CyclicCover
