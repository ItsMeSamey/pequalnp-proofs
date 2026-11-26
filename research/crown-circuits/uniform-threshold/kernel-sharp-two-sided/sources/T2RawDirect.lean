import T2RawReader

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
open private tag_old from GateSurplus

def rawReads (i : Nat) (r : Raw) : Bool := r.2.1 == i || r.2.2 == i

def itemReads (i : Nat) (z : Item) : Bool := z.2.x == i || z.2.y == i

/-- Reader multiplicity is measured in distinct physical gate rows. -/
theorem reader_annotation (gs : List Raw) (ts : List Tag) (i n : Nat) :
    ((items n (annotate gs ts)).filter (itemReads i)).length =
      (gs.filter (rawReads i)).length := by
  induction gs generalizing ts n with
  | nil => rfl
  | cons row gs ih =>
    obtain ⟨o,x,y⟩ := row
    by_cases hx : x = i <;> by_cases hy : y = i <;>
      simp [annotate, items, itemReads, rawReads, hx, hy, ih]

theorem charge_raw_reader (gs : List Raw) (ts : List Tag) (i : Nat)
    (hi : i < ts.length) (closed : tagRead ts i ≠ none) :
    (gs.filter (rawReads i)).length ≤
      ((items ts.length (annotate gs ts)).reverse.filter
        (closedReader (fun j => (tagRead (extendTags gs ts) j).isNone))).length := by
  let Q := fun j => (tagRead (extendTags gs ts) j).isNone
  have qi : Q i = false := by
    change (tagRead (extendTags gs ts) i).isNone = false
    rw [tag_old gs ts i hi]
    cases h : tagRead ts i with
    | none => exact (closed h).elim
    | some b => rfl
  have sub (xs : List Item) : (xs.filter (itemReads i)).length ≤
      (xs.filter (closedReader Q)).length := by
    induction xs with
    | nil => simp
    | cons z zs ih =>
      by_cases hx : z.2.x = i <;> by_cases hy : z.2.y = i
      · simpa [itemReads,closedReader,hx,hy,qi] using ih
      · simpa [itemReads,closedReader,hx,hy,qi] using ih
      · simpa [itemReads,closedReader,hx,hy,qi] using ih
      · cases h : closedReader Q z <;> simp [itemReads,hx,hy,h] <;> omega
  rw [← reader_annotation gs ts i ts.length]
  simpa [List.filter_reverse] using sub (items ts.length (annotate gs ts)).reverse
theorem direct_reader_deletion_minor {α : Type} (gs : List Raw) (ts : List Tag) (out m : Nat)
    (large small : α → List Bool) (fit : ∀ a, Fits ts (large a))
    (arity : ∀ a, (small a).length = m) (valid : Valid ts.length (annotate gs ts))
    (outOK : out < ts.length + (annotate gs ts).length)
    (nonconstant : ∃ a b, Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large a) ≠
                         Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large b))
    (ren : Nat → Nat)
    (supply : ∀ i, tagRead ts i = none →
      ren i < m ∧ ∀ a, (small a).getD (ren i) false = (large a).getD i false)

    (i : Nat) (hi : i < ts.length) (closed : tagRead ts i ≠ none) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (small a) = Circuit.eval ⟨gs.map (fun (o,x,y) => binary o x y),out⟩ (large a)) ∧
      D.size + (gs.filter (rawReads i)).length ≤ gs.length := by
  obtain ⟨D, mono, ev, cost⟩ := reader_deletion_minor gs ts out m large small fit arity valid
    outOK nonconstant ren supply
  refine ⟨D, mono, ev, ?_⟩
  have bound := (Nat.add_le_add_left (charge_raw_reader gs ts i hi closed) D.size).trans cost
  simpa only [items_annotated_length] using bound

#print axioms direct_reader_deletion_minor
end ResidualSurplus

