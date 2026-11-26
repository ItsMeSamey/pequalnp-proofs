import Mathlib.Data.Finset.Card

namespace CrownCollisions

variable {G : Type*} [DecidableEq G]

/-- The middle two vertices of a length-three path are the unique pair that
covers its edges while each active gate has at most one inactive neighbor. -/
theorem path_forces_pair (A : Finset G) (side : A.card ≤ 2)
    (edge : G → G → Prop) (sym : ∀ i j, edge i j → edge j i)
    (cover : ∀ i j, edge i j → i ∈ A ∨ j ∈ A)
    (unique : ∀ i ∈ A, ∀ j ∉ A, ∀ k ∉ A, edge i j → edge i k → j = k)
    {a b c d : G} (ab : edge a b) (bc : edge b c) (cd : edge c d)
    (ac : a ≠ c) (ad : a ≠ d) (bd : b ≠ d) (bc_ne : b ≠ c)
    (ab_ne : a ≠ b) (cd_ne : c ≠ d) : A = {b,c} := by
  have middle (p q r s : G) (pq : edge p q) (qr : edge q r) (rs : edge r s)
      (pr : p ≠ r) (ps : p ≠ s) (qs : q ≠ s) (rs' : r ≠ s) : q ∈ A := by
    by_contra hq
    have hp := (cover p q pq).resolve_right hq
    have hr := (cover q r qr).resolve_left hq
    have hs : s ∈ A := by
      by_contra hs
      exact qs (unique r hr q hq s hs (sym q r qr) rs)
    have sub : ({p,r,s} : Finset G) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have card := Finset.card_le_card sub
    have val : ({p,r,s} : Finset G).card = 3 := by simp [pr,ps,rs']
    omega
  have hb := middle a b c d ab bc cd ac ad bd cd_ne
  have hc := middle d c b a (sym _ _ cd) (sym _ _ bc) (sym _ _ ab) bd.symm ad.symm ac.symm ab_ne.symm
  have sub : ({b,c} : Finset G) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le sub (by simpa [bc_ne] using side)).symm

end CrownCollisions
