import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Card
namespace ThresholdStarPartners

def port {α β : Type*} [DecidableEq α] (value : β → Finset α → Bool)
    (s : Finset α) : Sum α β → Bool
  | .inl x => decide (x ∈ s)
  | .inr b => value b s

/-- If every internal wire agrees with empty at singleton x, only raw x can change. -/
theorem changed_port {α β : Type*} [DecidableEq α] (value : β → Finset α → Bool)
    (x : α) (same : ∀ b, value b {x} = value b ∅) (p : Sum α β)
    (changed : port value {x} p ≠ port value ∅ p) : p = .inl x := by
  cases p with
  | inl a =>
    by_contra h
    have ne : a ≠ x := by intro e; subst a; exact h rfl
    simp [port,ne] at changed
  | inr b => exact False.elim (changed (same b))

/-- A second dead partner must be the first dead raw. A third star input then
disproves the required singleton admission. This covers a shared AND reader. -/
theorem dead_unique {α β : Type*} [DecidableEq α] (value : β → Finset α → Bool)
    (selected : α → Prop) (partner : α → Sum α β)
    (third : ∀ x y : α, x ≠ y → ∃ z, z ≠ x ∧ z ≠ y)
    (admits : ∀ y, selected y → ∀ x, x ≠ y → port value {x} (partner y)=true)
    (quiet : ∀ x, selected x → port value ∅ (partner x)=false →
      ∀ b, value b {x}=value b ∅)
    {x y : α} (sx : selected x) (sy : selected y)
    (dx : port value ∅ (partner x)=false) (dy : port value ∅ (partner y)=false) :
    x = y := by
  by_contra xy
  have change : port value {x} (partner y) ≠ port value ∅ (partner y) := by
    rw [admits y sy x xy,dy]; decide
  have pin := changed_port value x (quiet x sx dx) (partner y) change
  obtain ⟨z,zx,zy⟩ := third x y xy
  have accepted := admits y sy z zy
  rw [pin] at accepted
  simp [port,Ne.symm zx] at accepted

/-- Admission from sole-reader semantics: blocking the partner would make an
accepting pair indistinguishable from its rejecting singleton. -/
theorem admits_singleton {α β : Type*} [DecidableEq α] (value : β → Finset α → Bool)
    (p : Sum α β) (x y : α) (xy : x ≠ y) (out : Finset α → Bool)
    (sem : ∀ s, out s=true ↔ 2 ≤ s.card)
    (frozen : port value {y} p=false → out (insert x {y})=out {y}) :
    port value {y} p=true := by
  cases h : port value {y} p with
  | true => rfl
  | false =>
    have pair : out (insert x {y})=true := (sem _).mpr (by simp [xy])
    have single := (sem {y}).mp ((frozen h).symm.trans pair)
    simp at single

/-- On a fixed star assignment, each ordinary gate agrees if its predecessors
agree. At a bypassed gate the two local rules are x OR Q and x. The unchanged
prefix identifies Q with the bypassed circuit's terminal tap. -/
theorem first_tap {g : Nat} (old new : Fin g → Bool) (tap : Fin g → Bool)
    (output : Fin g) (lost : old output=true) (off : new output=false)
    (localRule : ∀ i, (∀ j, j.val<i.val → old j=new j) → old i≠new i → tap i=true) :
    ∃ i, tap i=true := by
  classical
  let changed := fun k : Nat => ∃ i : Fin g, i.val=k ∧ old i≠new i
  have ex : ∃ k, changed k := ⟨output.val,output,rfl,by simp [lost,off]⟩
  obtain ⟨i,eq,diff⟩ := Nat.find_spec ex
  refine ⟨i,localRule i (fun j lt => ?_) diff⟩
  by_contra d
  have lower := Nat.find_min' ex (show changed j.val from ⟨j,rfl,d⟩)
  omega

/-- Output truth after simultaneous promotion. A tap must be defined from the
new predecessor values, whose singleton cleanliness follows by domination. -/
theorem promoted_accepts {α β : Type*} (old new : α → Bool) (tap : β → α → Bool)
    (below : ∀ s, new s=true → old s=true)
    (clean : ∀ b s, tap b s=true → old s=true)
    (trace : ∀ s, old s=true → new s=false → ∃ b, tap b s=true) (s : α) :
    (new s=true ∨ ∃ b,tap b s=true) ↔ old s=true := by
  constructor
  · rintro (h|⟨b,h⟩)
    · exact below s h
    · exact clean b s h
  · intro h
    cases e : new s with
    | true => exact Or.inl rfl
    | false => exact Or.inr (trace s h e)

#print axioms first_tap
#print axioms promoted_accepts
#print axioms dead_unique
#print axioms admits_singleton
end ThresholdStarPartners
