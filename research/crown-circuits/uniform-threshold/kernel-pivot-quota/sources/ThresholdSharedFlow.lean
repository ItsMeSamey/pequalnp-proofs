import ThresholdSharedOrBudget
namespace ThresholdSharedFlow
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ResidualSurplus
variable {C : Circuit} {n : Nat} (L : Layout C n)
def on (U : Id C) (w : Nat) : Bool :=
  if h : w<n then false else
  if b : w-n<C.gates.length then
    let i : Id C := ⟨w-n,b⟩
    if i=U then true else match L.op i with
    | .and => on U (L.left i) && on U (L.right i)
    | .or => on U (L.left i) || on U (L.right i)
  else false
termination_by w
decreasing_by all_goals first
  | have z := (L.atIndex i).leftEarlier; dsimp [i] at z; omega
  | have z := (L.atIndex i).rightEarlier; dsimp [i] at z; omega

def active (U i : Id C) := on L U (n+i.val)
def inCount (U i : Id C) :=
  (on L U (L.left i)).toNat+(on L U (L.right i)).toNat
def slots (a i : Id C) :=
  (decide (L.left i=n+a.val)).toNat+(decide (L.right i=n+a.val)).toNat
def fan (a : Id C) := ∑ i : Id C, slots L a i
def leak (U : Id C) := ∑ i : Id C,
  if L.op i=.and ∧ active L U i=false then inCount L U i else 0
theorem row_eq (U i : Id C) : active L U i =
    if i=U then true else match L.op i with
    | .and => on L U (L.left i) && on L U (L.right i)
    | .or => on L U (L.left i) || on L U (L.right i) := by
  unfold active
  rw [on]
  simp
theorem earlier_off (U : Id C) (w : Nat) (early : w<n+U.val) : on L U w=false := by
  rw [on]
  split
  · rfl
  · rename_i h
    split
    · rename_i b
      let i : Id C := ⟨w-n,b⟩
      have eq : n+i.val=w := by dsimp [i]; omega
      have ne : i≠U := fun e => by rw [e] at eq; omega
      have hl := (L.atIndex i).leftEarlier
      have hr := (L.atIndex i).rightEarlier
      rw [eq] at hl hr
      have l := earlier_off U (L.left i) (by omega)
      have r := earlier_off U (L.right i) (by omega)
      change (if i=U then true else _) = false
      rw [if_neg ne]
      dsimp only [i] at l r
      cases L.op i <;> simp [l,r]
    · rfl
termination_by w
decreasing_by all_goals dsimp [i] at hl hr ⊢ <;> omega

theorem oriented {U W : Id C} (ne : U≠W) (act : active L U W=true) : U<W := by
  by_contra hn
  have diff : U.val≠W.val := fun h => ne (Fin.ext h)
  change ¬U.val<W.val at hn
  have off := earlier_off L U (n+W.val) (by omega)
  simp [active,off] at act

private theorem pin_sum (U : Id C) (w : Nat) (bound : w<n+C.gates.length) :
    (on L U w).toNat = ∑ a : Id C, if active L U a=true then (decide (w=n+a.val)).toNat else 0 := by
  by_cases h : w<n
  · have none (a : Id C) : w≠n+a.val := by omega
    rw [on]
    simp [h,none]
  · let j : Id C := ⟨w-n,by omega⟩
    have eq : w=n+j.val := by dsimp [j]; omega
    have test (a : Id C) : (w=n+a.val) ↔ a=j := by
      rw [eq]; constructor
      · intro h; apply Fin.ext; omega
      · rintro rfl; rfl
    rw [Finset.sum_eq_single j]
    · rw [eq]
      change (active L U j).toNat=_
      cases e : active L U j <;> simp [e]
    · intro a ha ne; simp [test,ne]
    · simp

theorem conservation (U : Id C) : (∑ i : Id C, inCount L U i) =
    ∑ a : Id C, if active L U a then fan L a else 0 := by
  calc
    _ = ∑ i : Id C, ∑ a : Id C, if active L U a then slots L a i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have small := i.isLt
      have l := (L.atIndex i).leftEarlier
      have r := (L.atIndex i).rightEarlier
      rw [inCount,pin_sum L U (L.left i) (by omega),pin_sum L U (L.right i) (by omega),
        ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _; cases active L U a <;> simp [slots]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _; cases ha : active L U a <;> simp [ha,fan]
def reserve (U i : Id C) :=
  if i=U then 0 else if active L U i then (if L.op i=.and then 2 else 1) else 0

def budget (U i : Id C) :=
  if active L U i then
    if i=U then fan L i else if L.op i=.and then fan L i-2 else fan L i-1
  else 0

theorem probe_flow (U : Id C) : leak L U ≤ ∑ i : Id C, budget L U i := by
  let B := fun i : Id C => if L.op i=.and ∧ active L U i=false then inCount L U i else 0
  have costs (i : Id C) : B i+reserve L U i ≤ inCount L U i := by
    have sem := row_eq L U i
    by_cases e : i=U <;> cases h : L.op i <;>
      cases l : on L U (L.left i) <;> cases r : on L U (L.right i) <;>
      simp_all [B,reserve,inCount]
  have localBound (i : Id C) :
      (if active L U i then fan L i else 0) ≤ reserve L U i+budget L U i := by
    by_cases e : i=U
    · subst i; cases a : active L U U <;> simp [reserve,budget,a]
    · cases a : active L U i <;> cases h : L.op i <;> simp [reserve,budget,e,a,h] <;> omega
  have p := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Id C))) => costs i)
  have q := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Id C))) => localBound i)
  rw [Finset.sum_add_distrib,conservation] at p
  rw [Finset.sum_add_distrib] at q
  change (∑ i : Id C, B i) ≤ _
  omega

theorem opposite_off {U W : Id C} (ne : U≠W) (act : active L U W=true) :
    active L W U=false := by
  exact earlier_off L W _ (by have h := oriented L ne act; change U.val<W.val at h; omega)

#print axioms probe_flow
#print axioms opposite_off
end ThresholdSharedFlow
