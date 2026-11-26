import ThresholdStarProbeReadback
namespace ThresholdSlotEvaluation
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdSharedFlow
variable {C : Circuit} {n : Nat} (L : Layout C n)

def read (s : Id C → Bool → Bool) (V : Nat → Bool) (i : Id C) (b : Bool) (w : Nat) :=
  if w<n then s i b else V w

structure Trace (s : Id C → Bool → Bool) (V : Nat → Bool) : Prop where
  row : ∀ i, V (n+i.val)=act (L.op i)
    (read (n:=n) s V i false (L.left i)) (read (n:=n) s V i true (L.right i))

/-- Every physical gate activated by the single-root override stays true in
any occurrence-specific trace in which that root evaluates to true. -/
theorem probe_lower {s : Id C → Bool → Bool} {V : Nat → Bool}
    (T : Trace L s V) (u : Id C) (hot : V (n+u.val)=true) (i : Id C) :
    active L u i=true → V (n+i.val)=true := by
  suffices aux : ∀ w, w<n+C.gates.length → on L u w=true → V w=true by
    exact aux _ (by have := i.isLt; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound a
    by_cases raw : w<n
    · rw [on] at a; simp [raw] at a
    let j : Id C := ⟨w-n,by omega⟩
    have eq : n+j.val=w := by dsimp [j]; omega
    by_cases ov : j=u
    · rw [←eq,ov]; exact hot
    have rr := row_eq L u j
    rw [if_neg ov] at rr
    change on L u (n+j.val)=_ at rr
    rw [eq] at rr
    have side (b : Bool) (z : Nat) (lt : z<w) :
        on L u z=true → read (n:=n) s V j b z=true := by
      intro hit
      by_cases hz : z<n
      · rw [on] at hit; simp [hz] at hit
      simpa [read,hz] using ih z lt (by omega) hit
    have hl := side false (L.left j) (eq ▸ (L.atIndex j).leftEarlier)
    have hr := side true (L.right j) (eq ▸ (L.atIndex j).rightEarlier)
    rw [←eq,T.row]
    rw [rr] at a
    cases op : L.op j <;> simp_all [act,Bool.or_eq_true,Bool.and_eq_true] <;> grind
end ThresholdSlotEvaluation
