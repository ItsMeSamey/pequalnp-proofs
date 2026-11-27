import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
namespace IncidenceLabelHistory
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

/-- Labels always name original sites, even if surviving compiled inputs are reindexed. -/
structure Snapshot (α : Type*) where
  live : Finset α
  uses : α → ℕ
  hasAnd : α → Bool

def sole (c : Snapshot α) := c.live.filter (fun x=>c.uses x=1)
def vulnerable (c : Snapshot α) := c.live.filter (fun x=>c.uses x=1 ∧ c.hasAnd x=false)
def drops (a b : Snapshot α) := b.live.filter (fun x=>b.uses x<a.uses x)
def andLost (a b : Snapshot α) := b.live.filter
  (fun x=>a.uses x=1 ∧ a.hasAnd x=true ∧ b.uses x=1 ∧ b.hasAnd x=false)

theorem drops_le_debit (a b : Snapshot α) :
    (drops a b).card≤∑x∈b.live,(a.uses x-b.uses x) := by
  classical
  calc
    _ = ∑x∈b.live, if b.uses x<a.uses x then 1 else 0 := by simp [drops,Finset.sum_boole]
    _ ≤ _ := Finset.sum_le_sum (fun x _=>by split <;> omega)

theorem newly_sole (a b : Snapshot α) (sub : b.live⊆a.live)
    (essential : ∀x∈a.live,0<a.uses x) : sole b ⊆ sole a ∪ drops a b := by
  intro x hx
  obtain ⟨hb,one⟩ := Finset.mem_filter.mp hx
  have pos := essential x (sub hb)
  by_cases eq : a.uses x=1
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨sub hb,eq⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb,by omega⟩)

theorem newly_vulnerable (a b : Snapshot α) (sub : b.live⊆a.live)
    (essential : ∀x∈a.live,0<a.uses x) :
    vulnerable b ⊆ vulnerable a ∪ (drops a b ∪ andLost a b) := by
  intro x hx
  obtain ⟨hb,one,cold⟩ := Finset.mem_filter.mp hx
  have pos := essential x (sub hb)
  by_cases eq : a.uses x=1
  · cases old : a.hasAnd x with
    | false => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨sub hb,eq,old⟩)
    | true =>
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb,eq,old,one,cold⟩))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb,by omega⟩))

/-- The actual cumulative set of sites whose previous access pattern changed. -/
def history (c : ℕ→Snapshot α) : ℕ→Finset α
  | 0 => ∅
  | i+1 => history c i ∪ (drops (c i) (c (i+1)) ∪ andLost (c i) (c (i+1)))

theorem census (c : ℕ→Snapshot α) (t : ℕ)
    (sub : ∀i<t,(c (i+1)).live⊆(c i).live)
    (essential : ∀i<t,∀x∈(c i).live,0<(c i).uses x) :
    sole (c t)⊆sole (c 0)∪history c t ∧
      vulnerable (c t)⊆vulnerable (c 0)∪history c t := by
  induction t with
  | zero => simp [history]
  | succ j ih =>
    obtain ⟨so,vu⟩ := ih (fun i x=>sub i (by omega)) (fun i x=>essential i (by omega))
    have ns := newly_sole _ _ (sub j (by omega)) (essential j (by omega))
    have nv := newly_vulnerable _ _ (sub j (by omega)) (essential j (by omega))
    constructor
    · intro x hx
      rcases Finset.mem_union.mp (ns hx) with old|d
      · have hh := so old
        simp only [history,Finset.mem_union] at hh ⊢; tauto
      · simp only [history,Finset.mem_union]; tauto
    · intro x hx
      rcases Finset.mem_union.mp (nv hx) with old|d
      · have hh := vu old
        simp only [history,Finset.mem_union] at hh ⊢; tauto
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ d)

theorem charged (c : ℕ→Snapshot α) (credit : ℕ→ℕ) (t : ℕ)
    (per : ∀i<t, ((drops (c i) (c (i+1))) ∪ (andLost (c i) (c (i+1)))).card≤2*credit i) :
    (history c t).card≤2*∑i∈Finset.range t,credit i := by
  induction t with
  | zero => simp [history]
  | succ i ih =>
    have old := ih (fun j hj=>per j (by omega))
    have add := per i (by omega)
    have bound := Finset.card_union_le (history c i)
      (drops (c i) (c (i+1)) ∪ andLost (c i) (c (i+1)))
    rw [Finset.sum_range_succ]
    change (history c i ∪ (drops (c i) (c (i+1)) ∪ andLost (c i) (c (i+1)))).card ≤ _
    omega

def guards (c : ℕ → Snapshot α) : ℕ→Finset α
  | 0 => vulnerable (c 0)
  | i+1 => guards c i ∪ vulnerable (c (i+1))

theorem guarded_labels (c : ℕ→Snapshot α) (t : ℕ)
    (sub : ∀i<t,(c (i+1)).live⊆(c i).live)
    (essential : ∀i<t,∀x∈(c i).live,0<(c i).uses x) :
    guards c t ⊆ vulnerable (c 0) ∪ history c t := by
  induction t with
  | zero => simp [guards,history]
  | succ i ih =>
    have prev := ih (fun j h=>sub j (by omega)) (fun j h=>essential j (by omega))
    obtain ⟨_,now⟩ := census c (i+1) sub essential
    intro x hx
    rcases Finset.mem_union.mp hx with before|after
    · have hh := prev before
      simp only [history,Finset.mem_union] at hh ⊢; tauto
    · exact now after

theorem protected_census401 (c : ℕ→Snapshot α) (t : ℕ) (credit : ℕ→ℕ)
    (core nearby : Finset α)
    (sub : ∀i<t,(c (i+1)).live⊆(c i).live)
    (essential : ∀i<t,∀x∈(c i).live,0<(c i).uses x)
    (per : ∀i<t,(drops (c i) (c (i+1)) ∪ andLost (c i) (c (i+1))).card≤2*credit i)
    (budget : ∑i∈Finset.range t,credit i ≤1616) (oldCount : (sole (c 0)).card≤9843)
    (noOld : vulnerable (c 0)=∅) (coreSize : core.card≤806) (nearSize : nearby.card≤564) :
    (sole (c t)).card≤13075 ∧ (core ∪ nearby ∪ guards c t).card≤4602 := by
  have old := (census c t sub essential).1
  have h := charged c credit t per
  have all := guarded_labels c t sub essential
  rw [noOld,Finset.empty_union] at all
  have s := Finset.card_le_card old
  have g := Finset.card_le_card all
  have u := Finset.card_union_le (sole (c 0)) (history c t)
  have v := Finset.card_union_le core nearby
  have w := Finset.card_union_le (core ∪ nearby) (guards c t)
  omega
#print axioms protected_census401
end IncidenceLabelHistory
