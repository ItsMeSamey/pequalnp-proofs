import ThresholdPivotLocality
namespace ThresholdPivotStar
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins T2SoleOrSplice
open ThresholdEffectiveColumns ThresholdPhysicalFirstCut ThresholdOverrideCut ResidualSurplus
variable {C : Circuit} {n k : Nat} (L : Layout C n) (D : Star C n k L) (M : LexMinimum n C)

/-- Domination suffices to transfer singleton activation even at an erased source. -/
theorem below_original (s : Finset (Fin k)) (hs : s.Nonempty) (i : Id C) :
    changed L D s i=true → original L D s (n+i.val)=true := by
  classical
  by_cases f : i=D.pivot ∨ i=D.shared
  · intro _
    rcases f with rfl|rfl
    · exact nonempty_pivot L D s hs
    · exact nonempty_shared L D s hs
  have nf : i∉({D.pivot,D.shared} : Finset _) := by simpa using f
  let O := patch {D.pivot,D.shared} D.privatePin
  have port (b : Bool) : ThresholdOverrideCut.read L O s (i,b) (fun j _ => ThresholdOverrideCut.eval L O s j)=true →
      original L D s (source L (i,b))=true := by
    by_cases ex : ∃ x,D.privatePin x=(i,b)
    · have feed := D.socketFeed ex.choose
      rw [ex.choose_spec] at feed
      intro hot
      rw [feed,selected_row L D s ex.choose]
      simpa [ThresholdOverrideCut.read,O,patch,nf,ex,ThresholdOccurrenceEval.value] using hot
    · have untouched : O (i,b)=none := by simp [O,patch,nf,ex]
      by_cases yes : ∃ j : Id C,source L (i,b)=n+j.val
      · simp only [ThresholdOverrideCut.read,untouched,dif_pos yes]
        have eq := yes.choose_spec
        have dec := feeds_later L (show feeds L yes.choose (i,b) from eq)
        intro hit
        rw [eq]
        exact below_original s hs yes.choose hit
      · simp [ThresholdOverrideCut.read,untouched,yes]
  have raw := (L.atIndex i).eval (vector (s.map D.raw)) (by simp [vector])
  change ThresholdOverrideCut.eval L O s i=true → _
  rw [ThresholdOverrideCut.eval]
  change _ → (C.wires _).getD (n+i.val) false=true
  rw [raw]
  have left := port false
  have right := port true
  cases L.op i <;> simp_all [act,original,source,Bool.or_eq_true,Bool.and_eq_true] <;> grind
termination_by i.val
decreasing_by exact dec

noncomputable def cold := Finset.univ.filter (fun x : Fin k =>
  original L D {x} (n+(first L D M x).val)=false)

theorem cold_quota (out : Id C) (obs : C.output=n+out.val)
    (twice : ∀ w : Fin n,(readers C w.val).length=2)
    (inj : 3≤k → Function.Injective (first L D M)) :
    (cold L D M).card ≤ (if 3≤k then 1 else 2) := by
  classical
  by_cases hk : 3≤k
  · rw [if_pos hk]
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have quiet (z : Fin k) (hz : z∈cold L D M) : changed L D {z} (first L D M z)=
        changed L D ∅ (first L D M z) := by
      have off := (Finset.mem_filter.mp hz).2
      have single : changed L D {z} (first L D M z)=false := by
        cases v : changed L D {z} (first L D M z)
        · rfl
        · have yes := below_original L D {z} (Finset.singleton_nonempty _) _ v
          simp [off] at yes
      have zero : changed L D ∅ (first L D M z)=false := by
        cases v : changed L D ∅ (first L D M z)
        · rfl
        · have yes := monotone L (patch {D.pivot,D.shared} D.privatePin)
            ∅ {z} (Finset.empty_subset _) (first L D M z) v
          change changed L D {z} (first L D M z)=true at yes
          simp [single] at yes
      rw [single,zero]
    exact silent_unique L D M out obs twice (inj hk) x y (quiet x hx) (quiet y hy)
  · rw [if_neg hk]
    change (cold L D M).card≤_
    exact (show (cold L D M).card≤k by simpa [cold] using Finset.card_le_univ (cold L D M)).trans (by omega)
end ThresholdPivotStar
