import ThresholdBoundaryFormula
import ThresholdSocketRoute

namespace ThresholdBoundaryFormula
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins
open ThresholdEffectiveColumns ThresholdOverrideCut T2SoleOrSplice ThresholdSocketRoute
variable {C : Circuit} {n k : Nat} (L : Layout C n)

def count (side : Bool) (t : Tree C k) := if side then t.yCount else t.xCount

private theorem count_gate (side : Bool) (op : ReadOnceLCA.Op) (a b : Tree C k) :
    count side (.gate op a b)=count side a+count side b := by cases side <;> rfl

private theorem count_atom (side : Bool) (x y : Fin k) (ne : x≠y) (a : Bool ⊕ Fin k) :
    count (C:=C) side (atom x y a) =
      if a=.inr (if side then y else x) then 1 else 0 := by
  cases a with
  | inl b => cases side <;> rfl
  | inr z =>
    by_cases a : z=x <;> by_cases b : z=y <;> cases side <;>
      simp_all [count,atom,ReadOnceLCA.Formula.xCount,ReadOnceLCA.Formula.yCount]

theorem counts_route (M : LexMinimum n C) (O : Override C k) (socket : Fin k → Pin C)
    (loc : ∀ p z, O p=some (.inr z) → socket z=p)
    (x y : Fin k) (ne : x≠y) (side : Bool) (i : Id C) :
    count side (formula L O x y i)≤1 ∧
    (0<count side (formula L O x y i) →
      ∃ b, (i,b)∈route L M (socket (if side then y else x))) := by
  classical
  let z := if side then y else x
  let t := fun b : Bool => operand L O x y (i,b) (fun j _ => formula L O x y j)
  have port (b : Bool) : count side (t b)≤1 ∧
      (0<count side (t b) → (i,b)∈route L M (socket z)) := by
    dsimp only [t]
    unfold operand
    cases e : O (i,b) with
    | some a =>
      rw [count_atom side x y ne]
      change (if a=.inr z then 1 else 0)≤1 ∧ ((0 < (if a=.inr z then 1 else 0)) → (i,b)∈route L M (socket z))
      by_cases same : a=.inr z
      · subst a
        have start := loc (i,b) z e
        simp [start,route]
      · simp [same]
    | none =>
      by_cases fed : ∃ j : Id C,source L (i,b)=n+j.val
      · by_cases marked : boundary (n:=n) fed.choose
        · cases side <;> simp [fed,marked,count,ReadOnceLCA.Formula.xCount,ReadOnceLCA.Formula.yCount]
        · simp only [dif_pos fed,if_neg marked]
          obtain ⟨small,carry⟩ := counts_route M O socket loc x y ne side fed.choose
          refine ⟨small,fun pos => ?_⟩
          obtain ⟨d,mem⟩ := carry pos
          exact next_mem L M (socket z) (q:=(fed.choose,d)) mem marked fed.choose_spec
      · cases side <;> simp [fed,count,ReadOnceLCA.Formula.xCount,ReadOnceLCA.Formula.yCount]
  rw [formula,count_gate]
  change count side (t false)+count side (t true)≤1 ∧ _
  obtain ⟨a,pa⟩ := port false
  obtain ⟨b,pb⟩ := port true
  constructor
  · by_contra bad
    have badpin := side_unique (unique_rows L M (socket z))
      (pa (by omega)) (pb (by omega)) rfl
    exact Bool.false_ne_true (congrArg Prod.snd badpin)
  · intro pos
    change 0<count side (t false)+count side (t true) at pos
    by_cases l : 0<count side (t false)
    · exact ⟨false,pa l⟩
    · exact ⟨true,pb (by omega)⟩
termination_by i.val
decreasing_by exact feeds_later L (show feeds L _ _ from fed.choose_spec)

theorem patch_local (forced : Finset (Id C)) (socket : Fin k → Pin C)
    (p : Pin C) (x : Fin k) (eq : ThresholdPhysicalFirstCut.patch forced socket p=some (.inr x)) :
    socket x=p := by
  classical
  unfold ThresholdPhysicalFirstCut.patch at eq
  split at eq
  · simp at eq
  · split at eq
    next ex =>
      have same : ex.choose=x := by simpa using eq
      exact same ▸ ex.choose_spec
    next => contradiction

theorem physical_counts (M : LexMinimum n C) (forced : Finset (Id C))
    (socket : Fin k → Pin C) (x y : Fin k) (ne : x≠y) (i : Id C) :
    let t := formula L (ThresholdPhysicalFirstCut.patch forced socket) x y i
    t.xCount≤1 ∧ t.yCount≤1 :=
  ⟨(counts_route L M _ socket (patch_local forced socket) x y ne false i).1,
   (counts_route L M _ socket (patch_local forced socket) x y ne true i).1⟩

end ThresholdBoundaryFormula
