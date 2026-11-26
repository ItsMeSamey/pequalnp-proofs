import Mathlib.Data.Finset.Card

namespace CrownCollisions
variable {G W : Type*} [LinearOrder G] [DecidableEq W]

/-- For two adjacent collision edges, the earliest firing gate must read
one of three fixed wires. -/
theorem adjacent_triggers (P : G → Finset W) {a b c : G}
    (ac : a < c) (ab : a ≠ b) (bc : b ≠ c)
    (small : ∀ g, (P g).card ≤ 2) (pac : Disjoint (P a) (P c))
    (shared₁ : (P a ∩ P b).Nonempty) (shared₂ : (P b ∩ P c).Nonempty) :
    ∃ T : Finset W, T.card ≤ 3 ∧
      ∀ (S : Finset G) (on : W → Prop) (k : G),
        S.card = 2 → (a ∈ S ∨ b ∈ S) → (b ∈ S ∨ c ∈ S) →
        (∀ g, g ∈ S ↔ ∃ v ∈ P g, on v) →
        k ∈ S → (∀ j ∈ S, k ≤ j) → ∃ v ∈ T, v ∈ P k ∧ on v := by
  obtain ⟨p,hp⟩ := shared₁
  obtain ⟨q,hq⟩ := shared₂
  obtain ⟨pa,pb⟩ := Finset.mem_inter.mp hp
  obtain ⟨qb,qc⟩ := Finset.mem_inter.mp hq
  have pq : p ≠ q := fun h => Finset.disjoint_left.mp pac pa (h ▸ qc)
  have mid : P b = {p,q} := by
    symm
    apply Finset.eq_of_subset_of_card_le (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl|h
      · exact pb
      · simpa only [Finset.mem_singleton.mp h] using qb)
    simpa [pq] using small b
  refine ⟨P b ∪ (P a).erase p,?_,?_⟩
  · have H := Finset.card_union_le (P b) ((P a).erase p)
    rw [Finset.card_erase_of_mem pa] at H
    have := small a
    have := small b
    omega
  intro S on k card cover₁ cover₂ eval hk earliest
  have pair {u v : G} (huv : u ≠ v) (hu : u ∈ S) (hv : v ∈ S) :
      S = {u,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl|h
      · exact hu
      · simpa only [Finset.mem_singleton.mp h] using hv)
    simp [huv,card]
  by_cases hb : b ∈ S
  · obtain ⟨v,hv,hon⟩ := (eval b).mp hb
    refine ⟨v,Finset.mem_union_left _ hv,?_,hon⟩
    rw [mid] at hv
    rcases Finset.mem_insert.mp hv with rfl|hqv
    · have ha := (eval a).mpr ⟨_,pa,hon⟩
      rw [pair ab ha hb] at hk
      rcases Finset.mem_insert.mp hk with rfl|hk
      · exact pa
      · simpa only [Finset.mem_singleton.mp hk] using pb
    · obtain rfl := Finset.mem_singleton.mp hqv
      have hc := (eval c).mpr ⟨_,qc,hon⟩
      rw [pair bc hb hc] at hk
      rcases Finset.mem_insert.mp hk with rfl|hk
      · exact qb
      · simpa only [Finset.mem_singleton.mp hk] using qc
  · have ha := cover₁.resolve_right hb
    have hc := cover₂.resolve_left hb
    have hka := earliest a ha
    rw [pair ac.ne ha hc] at hk
    have eq : k = a := by
      rcases Finset.mem_insert.mp hk with h|h
      · exact h
      · exact False.elim (ac.not_ge ((Finset.mem_singleton.mp h) ▸ hka))
    subst k
    obtain ⟨v,hv,hon⟩ := (eval a).mp ha
    have hp : v ≠ p := fun eq => hb ((eval b).mpr ⟨_,eq ▸ pb,hon⟩)
    exact ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hp,hv⟩),hv,hon⟩

end CrownCollisions
