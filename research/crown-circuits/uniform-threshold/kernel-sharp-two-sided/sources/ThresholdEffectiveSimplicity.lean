import ThresholdEffectiveColumns

namespace ThresholdEffectiveSimplicity
open PEqualNP.CircuitLowerBounds T2OrPartition ThresholdOrExtraction ThresholdFanoutBudget
open T2SoleOrSplice ThresholdEffectiveColumns
variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- A physical changing path leaving the added raw's second row cannot
reach a boundary if every first effective column on that row stays fixed.
The path includes its terminal gate, even for an immediate reader. -/
theorem exclude_change (minim : LexMinimum n C) {r q : Id C}
    {p : Id C × Bool} {ps : List (Id C × Bool)} {changed : Id C → Prop}
    (edge : feeds L r p) (rest : Walk L p.1 ps q) (mark : boundary (n:=n) q)
    (pathChange : ∀ v ∈ (p::ps).map Prod.fst, changed v)
    (fixed : ∀ v ∈ effective L minim r, ¬ changed v) : False := by
  obtain ⟨v, hv, path⟩ := effective_cut L minim edge rest mark
  exact fixed v hv (pathChange v path)

/-- When adding a distinct actual AF to a BF singleton, a changing path
must escape A because F is already true. The same condition applies to
adding CF to AF. Its physical construction is an explicit hypothesis. -/
def Escapes (r : Id C) (changed : Id C → Prop) : Prop :=
  ∃ (q : Id C) (p : Id C × Bool) (ps : List (Id C × Bool)),
    feeds L r p ∧ Walk L p.1 ps q ∧ boundary (n:=n) q ∧
    ∀ v ∈ (p::ps).map Prod.fst, changed v

theorem loop_excluded (minim : LexMinimum n C) {a s : Id C} {changed : Id C → Prop}
    (escape : Escapes L a changed)
    (hotShared : ¬ changed s) : effective L minim a ≠ {s} := by
  intro loopEq
  obtain ⟨q,p,ps,edge,rest,mark,h⟩ := escape
  apply exclude_change L minim edge rest mark h
  intro v hv
  rw [loopEq, Finset.mem_singleton] at hv
  simpa [hv] using hotShared

theorem parallel_excluded (minim : LexMinimum n C) {a c : Id C} {changed : Id C → Prop}
    (escape : Escapes L c changed)
    (hotA : ∀ v ∈ effective L minim a, ¬ changed v) :
    effective L minim c ≠ effective L minim a := by
  intro parallelEq
  obtain ⟨q,p,ps,edge,rest,mark,h⟩ := escape
  apply exclude_change L minim edge rest mark h
  simpa [parallelEq] using hotA

end ThresholdEffectiveSimplicity
