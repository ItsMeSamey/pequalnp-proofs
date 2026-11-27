import DDIndexedReaders
import DDLiveDAG
import DDMultiCut
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem step_reader {n : ℕ} {V : DAG} {C : Circuit} {idx : Node → ℕ}
    (direct : ∀ i v, v ∈ V.readers i → idx v ∈ readers n C (idx (.row i)))
    {a b : Node} (h : V.step a b) : idx b ∈ readers n C (idx a) := by
  cases a with
  | arm k => exact h.elim
  | row i => exact direct i b h.2.2

theorem physical_path {n : ℕ} {V : DAG} {C : Circuit} {idx : Node → ℕ}
    (direct : ∀ i v, v ∈ V.readers i → idx v ∈ readers n C (idx (.row i)))
    {a b : Node} (h : Relation.ReflTransGen V.step a b) :
    Influence n C (idx a) (n+idx b) := by
  induction h with
  | refl => exact .source
  | tail _ edge prev =>
    obtain ⟨bound,uses⟩ := Finset.mem_filter.mp (step_reader direct edge)
    exact .step prev (Finset.mem_range.mp bound) uses

theorem physical_strict {n : ℕ} {V : DAG} {C : Circuit} {idx : Node → ℕ}
    (direct : ∀ i v, v ∈ V.readers i → idx v ∈ readers n C (idx (.row i)))
    {a b : Node} (h : Relation.TransGen V.step a b) :
    strictInfluence n C (idx a) (n+idx b) := by
  cases h with
  | single edge =>
    obtain ⟨bound,uses⟩ := Finset.mem_filter.mp (step_reader direct edge)
    exact ⟨_,Finset.mem_range.mp bound,rfl,_,uses,.source⟩
  | tail path edge =>
    obtain ⟨bound,uses⟩ := Finset.mem_filter.mp (step_reader direct edge)
    exact ⟨_,Finset.mem_range.mp bound,rfl,_,uses,physical_path direct path.to_reflTransGen⟩
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
