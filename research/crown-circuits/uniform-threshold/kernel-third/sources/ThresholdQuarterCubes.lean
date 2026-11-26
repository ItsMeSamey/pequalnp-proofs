import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

namespace ThresholdQuarterCubes

structure TwoPins (I : Type*) where
  first : I
  second : I
  firstBit : Bool
  secondBit : Bool
  consistent : first = second → firstBit = secondBit

def Fits {I : Type*} (p : TwoPins I) (v : I → Bool) : Prop :=
  v p.first = p.firstBit ∧ v p.second = p.secondBit

private def force {I : Type*} [DecidableEq I] (p : TwoPins I) (v : I → Bool)
    (i : I) : Bool := if i = p.first then p.firstBit else if i = p.second then p.secondBit else v i

private theorem fits_force {I : Type*} [DecidableEq I] (p : TwoPins I) (v : I → Bool) :
    Fits p (force p v) := by
  constructor
  · simp [force]
  · by_cases h : p.second = p.first
    · simpa [force,h] using p.consistent h.symm
    · simp [force,h]

theorem at_most_four {I E : Type*} [Fintype I] [Fintype E] (p : E → TwoPins I)
    (unique : ∀ v : I → Bool, ∀ e f : E, Fits (p e) v → Fits (p f) v → e = f) :
    Fintype.card E ≤ 4 := by
  classical
  let enc := fun a : E × (I → Bool) =>
    (force (p a.1) a.2, (a.2 (p a.1).first, a.2 (p a.1).second))
  have inject : Function.Injective enc := by
    rintro ⟨e,v⟩ ⟨f,w⟩ h
    have same : force (p e) v = force (p f) w := congrArg Prod.fst h
    have ef : e = f := unique _ e f (fits_force _ _) (same.symm ▸ fits_force (p f) w)
    subst f
    have bits : (v (p e).first,v (p e).second) = (w (p e).first,w (p e).second) :=
      congrArg Prod.snd h
    have vw : v = w := by
      funext i
      by_cases h1 : i = (p e).first
      · subst i; exact congrArg Prod.fst bits
      by_cases h2 : i = (p e).second
      · subst i; exact congrArg Prod.snd bits
      simpa [force,h1,h2] using congrFun same i
    rw [vw]
  have count := Fintype.card_le_of_injective enc inject
  have le : Fintype.card E * Fintype.card (I → Bool) ≤
      4 * Fintype.card (I → Bool) := by
    simpa only [Fintype.card_prod,Fintype.card_bool,show 2*2=4 by decide,
      Nat.mul_comm (Fintype.card (I → Bool)) 4] using count
  exact Nat.le_of_mul_le_mul_right le Fintype.card_pos

/-- An edge can light exactly its two native consumer-port occurrences
    before any AND has fired. False and true are distinct physical port positions. -/
def Hits {I : Type*} (p : TwoPins I) (i : I) (b : Bool) : Prop :=
  (i = p.first ∧ b = p.firstBit) ∨ (i = p.second ∧ b = p.secondBit)

theorem fits_hit {I : Type*} {p : TwoPins I} {σ : I → Bool} (h : Fits p σ)
    {i : I} {b : Bool} (hit : Hits p i b) : σ i = b := by
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact h.1
  · exact h.2

/-- 'trace' follows a true pin backward through OR-only nodes until an
    earlier fired AND or one of the selected raw-edge port occurrences. -/
theorem no_active {a : Nat} {p q : TwoPins (Fin a)} {σ : Fin a → Bool}
    (hp : Fits p σ) (hq : Fits q σ) (active : Fin a → Prop)
    (trace : ∀ i, active i → ∀ b : Bool, Hits p i b ∨ Hits q i b ∨
      ∃ j : Fin a, j.val < i.val ∧ active j) : ∀ i, ¬active i := by
  intro i
  have aux (n : Nat) : ∀ i : Fin a, i.val = n → ¬active i := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro j ej on
      have chosen (b : Bool) : σ j = b := by
        rcases trace j on b with h | h | ⟨k,lt,hk⟩
        · exact fits_hit hp h
        · exact fits_hit hq h
        · exact False.elim (ih k.val (ej ▸ lt) k rfl hk)
      exact Bool.noConfusion ((chosen false).symm.trans (chosen true))
  exact aux i.val i rfl

theorem bound_of_first_active {a : Nat} {E : Type*} [Fintype E] (pins : E → TwoPins (Fin a))
    (active : E → E → Fin a → Prop)
    (accepted : ∀ e f, e ≠ f → ∃ i, active e f i)
    (trace : ∀ e f, e ≠ f → ∀ i, active e f i → ∀ b : Bool,
      Hits (pins e) i b ∨ Hits (pins f) i b ∨ ∃ j : Fin a, j.val < i.val ∧ active e f j) :
    Fintype.card E ≤ 4 := by
  apply at_most_four pins
  intro σ e f he hf
  by_contra ne
  obtain ⟨i,hi⟩ := accepted e f ne
  exact no_active he hf (active e f) (trace e f ne) i hi

end ThresholdQuarterCubes
