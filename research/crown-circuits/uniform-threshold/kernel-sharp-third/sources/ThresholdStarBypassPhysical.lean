import ThresholdStarBypass
import ThresholdRegularSource
import Batteries.Tactic.OpenPrivate
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource

open private earlier from ThresholdOrGroups

private theorem any_congr (xs : List Nat) (f g : Env)
    (same : ∀ i∈xs,f i=g i) : xs.any f=xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [same x (by simp),ih (fun j hj => same j (by simp [hj]))]

/-- If the overridden root was already true, the whole block scan agrees on
every stored wire with the original physical execution. The book supplies all
nonraw predecessor references; initially no physical wire needs to be stored. -/
theorem book_agrees {C : Circuit} {n : Nat} (input : List Bool) (len : input.length=n)
    (u : Nat) (sel : Nat → Bool) (hot : (C.wires input).getD u false=true)
    (bs : List Block) (seen : List Nat) (book : Book C n seen bs) (f : Env)
    (agree : ∀ w∈seen,f w=(C.wires input).getD w false) :
    ∀ w∈outputs bs seen,
      run u sel false (fun j => input.getD j false) bs f w=(C.wires input).getD w false := by
  induction bs generalizing seen f with
  | nil => exact agree
  | cons b bs ih =>
    obtain ⟨checked,external,tail⟩ := book
    let p := fun j => (C.wires input).getD j false
    let raw := fun j => input.getD j false
    have eval : row u sel false raw f b = p b.out := by
      by_cases force : b.out=u
      · simpa only [row,force,ite_true,p] using hot.symm
      cases b with
      | meet w x y =>
        change w≠u at force
        have xeq := agree x (external x (by simp [Block.exts]))
        have yeq := agree y (external y (by simp [Block.exts]))
        have real := checked.eval input len
        simpa [row,Block.out,force,p,xeq,yeq,act] using real.symm
      | group pin t =>
        change t.out≠u at force
        have ex := any_congr t.exts f p (fun j hj => agree j (external j hj))
        have small (z : Tree) (shape : z.Checked C n) : ∀ j∈z.raws, j<n := by
          induction z with
          | raw i => simpa [Tree.raws,Tree.Checked] using shape
          | external i => simp [Tree.raws]
          | join i l r hl hr =>
            intro j hj
            exact (List.mem_append.mp hj).elim (hl shape.2.1 j) (hr shape.2.2 j)
        have rawEq := any_congr t.raws raw p (fun j hj =>
          (earlier C.gates input j (by rw [len]; exact small t checked j hj)).symm)
        have real := t.real checked input len
        simpa [row,Block.out,force,ex,rawEq,p] using real.symm
    apply ih (b.out::seen) tail (put f b.out (row u sel false raw f b))
    intro j hj
    by_cases eq : j=b.out
    · subst j; simpa [put,p] using eval
    · have old := agree j ((List.mem_cons.mp hj).resolve_left eq)
      simpa [put,eq] using old

theorem regular_forced_hot {n out : Nat} {gs : List Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) (input : List Bool) (len : input.length=n)
    (u : Nat) (sel : Nat → Bool) (hot : ((source gs out).wires input).getD u false=true) :
    let C := source gs out
    let L := layout n gs out M.eligible
    run u sel false (fun j => input.getD j false) (forest L Fin.val)
      (fun _ => false) C.output = C.eval input := by
  intro C L
  obtain ⟨internal,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,seen⟩ := physical_book L internal Fin.val twice obs
  exact book_agrees input len u sel hot _ [] book (fun _ => false) (by simp) _ seen

#print axioms regular_forced_hot
end ThresholdStarBypass
