import ExactPlaneWedgeLayout

namespace ExactPlaneWedgeLayout
open ExactPlaneWedgeProduct

/-- Materialize the sorted list itself once; in particular do not call pairAt for every cell. -/
def makeLayout (n : ℕ) : Vector (Pair n) (n.choose 2) :=
  ⟨(pairList n).toArray, by simp [pairList_length]⟩

theorem layout_get (n : ℕ) (i : Fin (n.choose 2)) : (makeLayout n)[i]=pairAt n i := by
  simp [makeLayout,pairAt,List.get_eq_getElem]

def storeWith (lookup : Vector (Pair n) (n.choose 2)) (f : Feature n) : Vector F (dim n) :=
  Vector.ofFn (Fin.cases f.1 (Fin.addCases f.2.1 (Fin.addCases f.2.2.1
    (fun j => f.2.2.2 lookup[j]))))

def makeStore (n : ℕ) : Feature n → Vector F (dim n) :=
  let lookup := makeLayout n
  fun f => storeWith lookup f

theorem makeStore_eq (n : ℕ) : makeStore n=store n := by
  funext f
  apply congrArg Vector.ofFn
  funext i
  change _ = slot n i f
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.addCases (fun a => ?_) (fun k => ?_) j
    · simp [slot] <;> rfl
    · refine Fin.addCases (fun b => ?_) (fun t => ?_) k
      · simp [slot] <;> rfl
      · simp [slot]
        exact congrArg f.2.2.2 (layout_get n t)

theorem storeWith_eq (n : ℕ) : storeWith (makeLayout n)=store n := makeStore_eq n

#print axioms makeStore_eq
end ExactPlaneWedgeLayout
