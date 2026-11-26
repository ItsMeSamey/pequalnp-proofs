import CrownExact
import ParentRestriction

namespace CrownMixed
open FreeAndNet
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]

/-- An additional essential flag which stays false throughout the mixed crown
promise costs an additional OR whenever a positive input avoids that flag. -/
theorem folded_remote_or_lower (N : Naming I α) (t : Net α) (j : α)
    (hn : 3 ≤ Fintype.card I) (rep : N.Rep t)
    (off : ∀ p q, N.val p q j = false)
    (positive : ∃ v : α → Bool, v j = false ∧ t.eval v = true)
    (essential : ∃ v w : α → Bool, (∀ i, i ≠ j → v i = w i) ∧ t.eval v ≠ t.eval w) :
    3 * Fintype.card I + 1 ≤ t.cost + N.pairs + 4 := by
  obtain ⟨v,hv,hot⟩ := positive
  obtain ⟨w,x,agree,ne⟩ := essential
  obtain ⟨u,save,same⟩ := restrict_sensitive t {j} ⟨v,by simpa using hv,hot⟩ (by
    intro i hi
    obtain rfl : i = j := Finset.mem_singleton.mp hi
    exact ⟨w,x,agree,by simp,ne⟩)
  have preserve : N.Rep u := fun p q => (same (N.val p q) (by simpa using off p q)).trans (rep p q)
  have lower := mixed_or_lower N u hn preserve
  simp only [Finset.card_singleton] at save
  omega

end CrownMixed
