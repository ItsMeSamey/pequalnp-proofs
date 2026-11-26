import Mathlib.Data.Finset.Card
namespace ThresholdSilentBoundary

/-- Each boundary has a fixed local Boolean calculation in earlier marked
values and the fresh inputs whose first physical boundary it is. -/
def Locality {k m : Nat} (owner : Fin k → Fin m)
    (val : Finset (Fin k) → Fin m → Bool) :=
  ∀ d A B, (∀ j, j<d → val A j=val B j) →
    (∀ x,owner x=d → (x∈A ↔ x∈B)) → val A d=val B d

def Silent {k m : Nat} (owner : Fin k → Fin m) (val : Finset (Fin k) → Fin m → Bool)
    (x : Fin k) := val {x} (owner x)=val ∅ (owner x)

theorem singleton_equal {k m} (owner : Fin k → Fin m) (val : Finset (Fin k) → Fin m → Bool)
    (locality : Locality owner val) (x : Fin k) (quiet : Silent owner val x) (d : Fin m) :
    val {x} d=val ∅ d := by
  by_cases here : owner x=d
  · exact here ▸ quiet
  · apply locality _ _ _ (fun j hj => singleton_equal owner val locality x quiet j)
    intro y hy
    have ne : y≠x := fun eq => here (eq ▸ hy)
    simp [ne]
termination_by d.val
decreasing_by exact hj

theorem at_most_one_silent {k m} (owner : Fin k → Fin m) (val : Finset (Fin k) → Fin m → Bool)
    (locality : Locality owner val) (out : Fin m)
    (decoder : ∀ A,val A out=true ↔ 2≤A.card)
    (uniq : Function.Injective owner) (x y : Fin k) (sx : Silent owner val x)
    (sy : Silent owner val y) : x=y := by
  by_contra ne
  let rec pair (d : Fin m) : val {x,y} d=val ∅ d := by
    by_cases dx : owner x=d
    · have step := locality d {x,y} {x} (fun j hj => (pair j).trans (singleton_equal owner val locality x sx j).symm)
        (by intro z hz; have ze := uniq (hz.trans dx.symm); subst z; simp)
      exact step.trans (singleton_equal owner val locality x sx d)
    · by_cases dy : owner y=d
      · have step := locality d {x,y} {y} (fun j hj => (pair j).trans (singleton_equal owner val locality y sy j).symm)
          (by intro z hz; have ze := uniq (hz.trans dy.symm); subst z; simp)
        exact step.trans (singleton_equal owner val locality y sy d)
      · apply locality _ _ _ (fun j hj => pair j)
        intro z hz
        have zx : z≠x := fun eq => dx (eq ▸ hz)
        have zy : z≠y := fun eq => dy (eq ▸ hz)
        simp [zx,zy]
  termination_by d.val
  decreasing_by all_goals exact hj
  have yes := (decoder {x,y}).mpr (by simp [ne])
  have impossible := (decoder ∅).mp ((pair out).symm.trans yes)
  simp at impossible

end ThresholdSilentBoundary
