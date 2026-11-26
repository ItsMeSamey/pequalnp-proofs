import T2RawReader

namespace ResidualSurplus
open private tag_old from GateSurplus

theorem extendTags_append (a b : List Raw) (ts : List Tag) :
    extendTags (a ++ b) ts = extendTags b (extendTags a ts) := by
  induction a generalizing ts with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨o,x,y⟩ := r
    exact ih _

theorem extendTags_length (gs : List Raw) (ts : List Tag) :
    (extendTags gs ts).length = ts.length + gs.length := by
  induction gs generalizing ts with
  | nil => simp [extendTags]
  | cons r rs ih =>
    obtain ⟨o,x,y⟩ := r
    simp [extendTags, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The output tag at a named physical row equals its local fold result,
regardless of the continuation. -/
theorem named_row_tag (pre post : List Raw) (ts : List Tag) (o : Op) (x y : Nat) :
    tagRead (extendTags (pre ++ (o,x,y)::post) ts) (ts.length + pre.length) =
      foldTag o (tagRead (extendTags pre ts) x) (tagRead (extendTags pre ts) y) := by
  rw [extendTags_append, ← extendTags_length pre ts]
  let base := extendTags pre ts
  let a := foldTag o (tagRead base x) (tagRead base y)
  change tagRead (extendTags post (base ++ [a])) base.length = a
  rw [tag_old post _ _ (by simp)]
  simp [tagRead, List.getD_eq_getElem?_getD]

theorem named_and_false (pre post : List Raw) (ts : List Tag) (x y : Nat)
    (closed : tagRead (extendTags pre ts) x = some false ∨
              tagRead (extendTags pre ts) y = some false) :
    tagRead (extendTags (pre ++ (.and,x,y)::post) ts) (ts.length + pre.length) = some false := by
  rw [named_row_tag]
  rcases closed with l | r
  · rw [l]
    cases h : tagRead (extendTags pre ts) y with
    | none => rfl
    | some v => cases v <;> rfl
  · rw [r]
    cases h : tagRead (extendTags pre ts) x with
    | none => rfl
    | some v => cases v <;> rfl

/-- The named row survives annotation as an addressable item, even when it
will disappear from the smaller circuit. -/
theorem named_item (pre post : List Raw) (ts : List Tag) (n : Nat) (o : Op) (x y : Nat) :
    ∃ z ∈ items n (annotate (pre ++ (o,x,y)::post) ts),
      z.1 = n + pre.length ∧ z.2.x = x ∧ z.2.y = y := by
  induction pre generalizing ts n with
  | nil =>
    exact ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩
  | cons a as ih =>
    obtain ⟨p,j,k⟩ := a
    let next := ts ++ [foldTag p (tagRead ts j) (tagRead ts k)]
    obtain ⟨z,hm,eq,hx,hy⟩ := ih next (n+1)
    refine ⟨z, List.mem_cons_of_mem _ hm, ?_, hx, hy⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using eq

#print axioms named_and_false
#print axioms named_item
end ResidualSurplus
