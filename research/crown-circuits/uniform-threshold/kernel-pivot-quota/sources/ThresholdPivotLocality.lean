import ThresholdPivotStar
import ThresholdSilentBoundary
import Batteries.Tactic.OpenPrivate
namespace ThresholdPivotStar
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins T2SoleOrSplice
open ThresholdEffectiveColumns ThresholdPhysicalFirstCut ThresholdOverrideCut
open private read_agree from ThresholdOverrideCut
variable {C : Circuit} {n k : Nat} (L : Layout C n) (D : Star C n k L) (M : LexMinimum n C)
noncomputable def first (x : Fin k) := column L M (D.privatePin x).1
noncomputable def markValue (s : Finset (Fin k)) (i : Id C) :=
  by classical exact if boundary (n:=n) i then changed L D s i else false

theorem first_mark (x : Fin k) : boundary (n:=n) (first L D M x) :=
  (trace_ok L M (D.privatePin x).1).2

private theorem basin (d : Id C) (s t : Finset (Fin k))
    (prior : ∀ j,j<d → markValue L D s j=markValue L D t j)
    (fresh : ∀ x,first L D M x=d → (x∈s ↔ x∈t))
    (i : Id C) (le : i≤d) (owned : column L M i=d) :
    changed L D s i=changed L D t i := by
  let O := patch {D.pivot,D.shared} D.privatePin
  have pin (b : Bool) := read_agree L O s t (i,b)
    (fun x e => fresh x ((fresh_route L M _ _ _ x e).trans owned))
    (fun _ j edge => by
      have lt := feeds_later L (show feeds L j (i,b) from edge)
      by_cases m : boundary (n:=n) j
      · simpa [markValue,m,changed,O] using prior j (lt_of_lt_of_le lt le)
      · have parent := column_of_feed L M j (i,b) m edge
        exact basin d s t prior fresh j (le_trans lt.le le) (parent.trans owned))
  change ThresholdOverrideCut.eval L O s i=ThresholdOverrideCut.eval L O t i
  rw [ThresholdOverrideCut.eval,ThresholdOverrideCut.eval]
  exact congrArg₂ _ (pin false) (pin true)
termination_by i.val
decreasing_by exact lt

theorem mark_locality : ThresholdSilentBoundary.Locality (first L D M) (markValue L D) := by
  intro d s t prior fresh
  by_cases hd : boundary (n:=n) d
  · simpa [markValue,hd] using basin L D M d s t prior fresh d le_rfl (column_of_boundary L M d hd)
  · simp [markValue,hd]

private theorem earlier_mask (d j : Id C) (lt : j<d) (s t : Finset (Fin k))
    (keep : ∀ x,first L D M x≠d → (x∈s ↔ x∈t)) :
    markValue L D s j=markValue L D t j := by
  apply mark_locality L D M j s t
  · intro a aj; exact earlier_mask d a (aj.trans lt) s t keep
  · intro x same; exact keep x (fun eq => lt.ne (same.symm.trans eq))
termination_by j.val
decreasing_by exact aj

theorem earlier_unchanged (d j : Id C) (lt : j<d) (mk : boundary (n:=n) j)
    (base extra : Finset (Fin k)) (owned : ∀ x∈extra,first L D M x=d) :
    changed L D (base∪extra) j=changed L D base j := by
  have h := earlier_mask L D M d j lt (base∪extra) base (fun x ne => by
    have no : x∉extra := fun hit => ne (owned x hit)
    simp [no])
  simpa [markValue,mk] using h

theorem silent_unique (out : Id C) (obs : C.output=n+out.val)
    (twice : ∀ w : Fin n,(readers C w.val).length=2) (inj : Function.Injective (first L D M))
    (x y : Fin k) (sx : changed L D {x} (first L D M x)=changed L D ∅ (first L D M x))
    (sy : changed L D {y} (first L D M y)=changed L D ∅ (first L D M y)) : x=y := by
  apply ThresholdSilentBoundary.at_most_one_silent _ _ (mark_locality L D M) out
    (fun s => by simpa [markValue,show boundary (n:=n) out from Or.inl obs] using threshold L D M twice x out obs s) inj
  · simpa [ThresholdSilentBoundary.Silent,markValue,first_mark] using sx
  · simpa [ThresholdSilentBoundary.Silent,markValue,first_mark] using sy
end ThresholdPivotStar
