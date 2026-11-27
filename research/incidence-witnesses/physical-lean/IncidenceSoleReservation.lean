import Research.CircuitRewire

namespace IncidenceSoleReservation
open CircuitRewire

theorem equal_except {Z : Type*} (m s x reserved : ℕ) (g : ℕ → Gate)
    (A B : ℕ → Set Z)
    (inputs : ∀ i < m, i ≠ x → A i = B i)
    (ord : ∀ j < s, (g j).left < m+j ∧ (g j).right < m+j)
    (only : ∀ j < s, j ≠ reserved → (g j).left ≠ x ∧ (g j).right ≠ x)
    (wa : ∀ j < s, A (m+j) = (g j).eval A)
    (wb : ∀ j < s, B (m+j) = (g j).eval B)
    (agree : reserved<s → A (m+reserved) = B (m+reserved)) :
    ∀ i < m+s, i ≠ x → A i = B i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi ne
    by_cases raw : i < m
    · exact inputs i raw ne
    · let j := i-m
      have idx : m+j=i := by dsimp [j]; omega
      have js : j<s := by omega
      by_cases eq : j=reserved
      · rw [←idx,eq]; exact agree (eq ▸ js)
      · have a := only j js eq
        obtain ⟨hl,hr⟩ := ord j js
        have l := ih (g j).left (by omega) (by omega) a.1
        have r := ih (g j).right (by omega) (by omega) a.2
        rw [←idx,wa j js,wb j js]
        unfold Gate.eval
        rw [l,r]

theorem sibling_high (m s x reserved out : ℕ) (g : ℕ → Gate)
    (A B : ℕ → Set Unit)
    (inputs : ∀ i < m, i ≠ x → A i = B i)
    (ord : ∀ j < s, (g j).left < m+j ∧ (g j).right < m+j)
    (only : ∀ j < s, j ≠ reserved → (g j).left ≠ x ∧ (g j).right ≠ x)
    (wa : ∀ j < s, A (m+j) = (g j).eval A)
    (wb : ∀ j < s, B (m+j) = (g j).eval B)
    (rs : reserved<s) (meet : (g reserved).op=.meet)
    (distinct : (g reserved).right ≠ x)
    (bound : out<m+s) (different : out≠x) (flip : A out≠B out) :
    () ∈ A (g reserved).right := by
  have sib : A (g reserved).right = B (g reserved).right := by
    apply equal_except m reserved x reserved g A B inputs
      (fun j hj => ord j (hj.trans rs))
      (fun j hj => only j (hj.trans rs))
      (fun j hj => wa j (hj.trans rs))
      (fun j hj => wb j (hj.trans rs))
      (fun impossible => False.elim ((Nat.lt_irrefl _) impossible))
      _ (ord reserved rs).2 distinct
  by_contra low
  have empty : A (g reserved).right = ∅ := by
    ext u
    cases u
    simp [low]
  apply flip
  apply equal_except m s x reserved g A B inputs ord only wa wb _ out bound different
  intro _
  rw [wa reserved rs,wb reserved rs]
  simp [Gate.eval, meet, Op.eval, ←sib, empty]

end IncidenceSoleReservation
