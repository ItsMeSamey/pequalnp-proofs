import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

/-- External root labels are actual gate indices. Exchanging left and right arms is
explicit in the two one-sided constructors. -/
inductive LeakShape (P Q : Finset ℕ) : Prop
  | privateArms (left : P = ∅) (right : Q = ∅)
  | singleLeft (e : ℕ) (left : P = {e}) (right : Q = ∅)
  | singleRight (e : ℕ) (left : P = ∅) (right : Q = {e})
  | manyLeft (left : 2 ≤ P.card) (right : Q = ∅)
  | manyRight (left : P = ∅) (right : 2 ≤ Q.card)
  | triangle (e : ℕ) (left : P = {e}) (right : Q = {e})

theorem classifyLeaks (P Q : Finset ℕ)
    (cross : ∀ p ∈ P, ∀ q ∈ Q, p = q) : LeakShape P Q := by
  classical
  by_cases lp : P = ∅
  · by_cases rq : Q = ∅
    · exact .privateArms lp rq
    · by_cases one : Q.card = 1
      · obtain ⟨e, he⟩ := Finset.card_eq_one.mp one
        exact .singleRight e lp he
      · exact .manyRight lp (by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr rq)
          omega)
  · by_cases rq : Q = ∅
    · by_cases one : P.card = 1
      · obtain ⟨e, he⟩ := Finset.card_eq_one.mp one
        exact .singleLeft e he rq
      · exact .manyLeft (by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr lp)
          omega) rq
    · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr lp
      obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr rq
      have equal := cross p hp q hq
      subst q
      apply LeakShape.triangle p
      · ext x
        constructor
        · exact fun hx => Finset.mem_singleton.mpr (cross x hx p hq)
        · intro hx
          exact (Finset.mem_singleton.mp hx) ▸ hp
      · ext x
        constructor
        · exact fun hx => Finset.mem_singleton.mpr (cross p hp x hx).symm
        · intro hx
          exact (Finset.mem_singleton.mp hx) ▸ hq

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
