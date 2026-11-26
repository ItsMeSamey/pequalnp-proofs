import GateSurplus
import Batteries.Tactic.OpenPrivate

namespace T2RawReader

/-- A sole reader of an input is the only way the input can affect the result. -/
theorem sole_or_clean (P : Bool) (context : Bool → Bool)
    (single : context (false || P) = false) (pair : context (true || P) = true) :
    P = false := by
  cases P <;> simp_all

theorem sole_and_dirty (P : Bool) (context : Bool → Bool)
    (single : context (false && P) = false) (pair : context (true && P) = true) :
    P = true := by
  cases P <;> simp_all

end T2RawReader

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds

/-- Charge every row with an operand forced constant, even when one raw pin
has several distinct consumers. The charge counts rows, not operand slots. -/
def closedReader (Q : Nat → Bool) (z : Item) := !(Q z.2.x && Q z.2.y)

theorem closed_reader_bound (Q : Nat → Bool) (xs : List Item) (s : Counts)
    (safe : ∀ z ∈ xs, KeepsOpen (fun i => Q i = true) z)
    (live : ∀ i ∈ s.kept, Q i = true) :
    (counts xs s).keptGates + (xs.filter (closedReader Q)).length ≤
      s.keptGates + xs.length := by
  induction xs generalizing s with
  | nil => simp [counts]
  | cons z zs ih =>
    have hz := safe z (by simp)
    have hnext : ∀ i ∈ (advance s z).kept, Q i = true := by
      apply open_frontier (fun i => Q i = true) [z] s _ live
      simpa using hz
    have tail := ih (advance s z) (fun j hj => safe j (by simp [hj])) hnext
    have cost : (advance s z).keptGates + (if closedReader Q z then 1 else 0) ≤ s.keptGates+1 := by
      by_cases full : z.1 ∈ s.full
      · by_cases kept : z.1 ∈ s.kept
        · have req := hz (live _ kept)
          cases use : z.2.use with
          | both =>
            simp [use] at req
            simp [advance,step,full,kept,use,useMode,price,closedReader,req.1,req.2]
          | left => simp [advance,step,full,kept,use,useMode,price]; split <;> omega
          | right => simp [advance,step,full,kept,use,useMode,price]; split <;> omega
        · simp [advance,step,full,kept]; split <;> omega
      · simp [advance,step,full]; split <;> omega
    change (counts zs (advance s z)).keptGates + _ ≤ _
    cases h : closedReader Q z <;> simp [h] at cost ⊢ <;> omega

end ResidualSurplus
-- READERBRIDGE
namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
open private bank_reverse read_laws read_earlier open_laws from GateSurplus
theorem items_annotated_length (gs : List Raw) (ts : List Tag) :
    (items ts.length (annotate gs ts)).length = gs.length := by
  have len (rs : List Row) (n : Nat) : (items n rs).length = rs.length := by
    induction rs generalizing n with
    | nil => rfl
    | cons h t ih => simp [items, ih]
  rw [len]
  simpa only [List.length_map] using congrArg List.length (annotation_full gs ts)

theorem reader_deletion_minor {α : Type} (gs : List Raw) (ts : List Tag) (out m : Nat)
    (large small : α → List Bool) (fit : ∀ a, Fits ts (large a))
    (arity : ∀ a, (small a).length = m) (valid : Valid ts.length (annotate gs ts))
    (outOK : out < ts.length + (annotate gs ts).length)
    (nonconstant : ∃ a b, Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large a) ≠
                         Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large b))
    (ren : Nat → Nat)
    (supply : ∀ i, tagRead ts i = none →
      ren i < m ∧ ∀ a, (small a).getD (ren i) false = (large a).getD i false)
    :
    let rs := annotate gs ts
    let s := counts (items ts.length rs).reverse (first out)
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (small a) = Circuit.eval ⟨gs.map (fun (o,x,y) => binary o x y),out⟩ (large a)) ∧
      D.size + ((items ts.length rs).reverse.filter (closedReader (fun i => (tagRead (extendTags gs ts) i).isNone))).length ≤ (items ts.length rs).length := by
  obtain ⟨a,b,hab⟩ := nonconstant
  have ho := open_of_nonconstant gs ts out (large a) (large b) (fit a) (fit b) hab
  have opn := surviving_unpinned gs ts out valid ho outOK
  let rs := annotate gs ts
  let xs := (items ts.length rs).reverse
  let X := fun i a => (run (rs.map Row.pruned) (large a)).getD i false
  have wf a : Valid (large a).length rs := by simpa [(fit a).1.symm,rs] using valid
  have laws : ∀ z ∈ xs, Local X z := by
    intro z hz a
    apply read_laws rs (large a) (wf a) z
    simpa [xs,(fit a).1.symm] using hz
  have src : ∀ i ∈ (counts xs (first out)).kept,
      ren i < m ∧ ∀ a, (small a).getD (ren i) false = X i a := by
    intro i hi
    have open_ := opn i hi
    obtain ⟨bound,agree⟩ := supply i open_
    refine ⟨bound,fun a => (agree a).trans ?_⟩
    have lt : i < ts.length := by
      by_contra! ge
      simp [tagRead,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : ts.length ≤ i)] at open_
    exact (read_earlier _ _ _ (by simpa [(fit a).1.symm] using lt)).symm

  have init : Bank m small X (counts xs (first out)).kept 0 :=
    ⟨[],ren,rfl,by simp,by simpa [run] using src⟩
  obtain ⟨k,⟨prog,w,len,mono,real⟩,hk⟩ := bank_reverse arity xs (first out) (by exact Finset.Subset.rfl) laws init
  let Q := fun i => (tagRead (extendTags gs ts) i).isNone
  have safe : ∀ z ∈ xs, KeepsOpen (fun i => Q i = true) z := by
    intro z hz
    have hp : (fun i => Q i = true) = (fun i => tagRead (extendTags gs ts) i = none) := by
      funext i
      simp [Q]
    rw [hp]
    exact open_laws gs ts valid z (by simpa [xs,rs] using hz)
  have cost := closed_reader_bound Q xs (first out) safe (by simpa [first,Q] using ho)
  obtain ⟨_,val⟩ := real out (by simp [first])
  refine ⟨⟨prog,w out⟩,fun g hg => ⟨(mono g hg).1,(mono g hg).2.le⟩,?_,?_⟩
  · intro a
    apply (val a).trans
    change Circuit.eval ⟨(annotate gs ts).map Row.pruned,out⟩ (large a) =
      Circuit.eval ⟨gs.map (fun (o,x,y) => binary o x y),out⟩ (large a)
    simpa only [annotation_full] using circuit_eval_annotation gs out ts (large a) (fit a)
  · change prog.length + _ ≤ _
    have eq : k = (counts xs (first out)).keptGates := by simpa [first] using hk
    rw [len,eq]
    simpa [xs,first,Q,rs] using cost
#print axioms reader_deletion_minor
end ResidualSurplus
