import IncidenceMarkTransition
import IncidenceLabelHistory
namespace IncidenceRoundProtection
open IncidenceMarkTransition IncidenceLabelHistory
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

/-- At every prefix, these are sets of original labels. The actual protected
    set includes the core, all previously marked sites and their fixed triples,
    and every label ever observed with a sole OR reader. -/
def protectedSet (core M : Finset α) (G : α→Finset α) (c : ℕ→Snapshot α) (i : ℕ) :=
  core ∪ reserve M G ∪ guards c i

theorem bounds401 (N : α→Finset α) (all deleted M core : Finset α) (G : α→Finset α)
    (c : ℕ→Snapshot α) (t : ℕ) (credit : ℕ→ℕ)
    (live : (c t).live=all \ deleted) (safe : Safe N (c t).live M G)
    (scope : ∀x∈M,N x⊆all) (degree : ∀x∈M,(N x).card=402)
    (low : ∀x∈M,((c t).live ∩ N x).card≤26)
    (codegree : ∀x∈M,∀y∈M,x≠y → (N x∩N y).card≤1) (limited : deleted.card≤38808)
    (sub : ∀i<t,(c (i+1)).live⊆(c i).live)
    (essential : ∀i<t,∀x∈(c i).live,0<(c i).uses x)
    (per : ∀i<t,(drops (c i) (c (i+1)) ∪ andLost (c i) (c (i+1))).card≤2*credit i)
    (budget : ∑i∈Finset.range t,credit i≤1616) (initial : (sole (c 0)).card≤9843)
    (noneInitial : vulnerable (c 0)=∅) (coreBound : core.card≤806) :
    (sole (c t)).card≤13075 ∧ (protectedSet core M G c t).card≤4602 := by
  have guardCap := guard_count401 N all deleted M G scope degree
    (fun x hx=>live ▸ low x hx) codegree limited safe.triple
  exact protected_census401 c t credit core _ sub essential per budget initial noneInitial coreBound guardCap

theorem plan_next (N : α→Finset α) (core M : Finset α) (G : α→Finset α)
    (c : ℕ→Snapshot α) (t : ℕ) (safe : Safe N (c t).live M G)
    (D : Finset α) (small : D.card≤24) (avoid : Disjoint D (protectedSet core M G c t))
    (after : (c (t+1)).live=(c t).live \ D) :
    let fresh := M ∪ (c (t+1)).live.filter (fun x=>((c (t+1)).live ∩ N x).card≤26)
    ∃G', (∀x∈M,G' x=G x) ∧ Safe N (c (t+1)).live fresh G' ∧
      protectedSet core M G c t⊆protectedSet core fresh G' c (t+1) ∧
      ∀x∈D,x∈(c t).live → 3≤((c (t+1)).live ∩ N x).card := by
  have sub : reserve M G⊆protectedSet core M G c t :=
    fun _ h=>Finset.mem_union_left _ (Finset.mem_union_right _ h)
  obtain ⟨G',st,sa,keep,three⟩ := transition N _ M G safe D (avoid.mono_right sub) small
  rw [after]
  refine ⟨G',st,sa,?_,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with a|h
    · rcases Finset.mem_union.mp a with onCore|wasGuard
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ onCore)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (keep wasGuard))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  · intro x xd xl
    apply three x xl
    intro inM
    exact Finset.disjoint_left.mp avoid xd (sub (Finset.mem_union_left _ inM))
#print axioms bounds401
#print axioms plan_next
end IncidenceRoundProtection
