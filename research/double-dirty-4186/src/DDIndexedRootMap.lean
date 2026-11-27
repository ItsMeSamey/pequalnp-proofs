import DDIndexedOwnership
import DDIndexedReaders
import DDIndexedRoots
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
open Indexed
theorem roots_mapped {n : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ) (arms : Fin 2 → ℕ) (w : ℕ)
    {r : Root} (h : r ∈ (indexed n C p E arms w).roots) :
    nodeIndex n C p r.node ∈ rootIndices n C p E := by
  cases r with
  | ext j =>
    have mem : j ∈ E := by simpa [DAG.roots,indexed] using h
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ mem))
  | arm b =>
    fin_cases b <;> simp [rootIndices,Root.node,nodeIndex]

theorem root_inj {n : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ) (arms : Fin 2 → ℕ) (w : ℕ)
    (present : ∀ j ∈ E, j<C.size ∧ ∃ g, ins n C p j = some g) :
    Set.InjOn (fun r : Root => nodeIndex n C p r.node) ((indexed n C p E arms w).roots : Set Root) := by
  intro a ha b hb eq
  have extMem {j} (h : Root.ext j ∈ (indexed n C p E arms w).roots) : j ∈ E := by
    simpa [DAG.roots,indexed] using h
  cases a with
  | ext i =>
    obtain ⟨hi,gi,ei⟩ := present _ (extMem ha)
    cases b with
    | ext j =>
      obtain ⟨hj,gj,ej⟩ := present _ (extMem hb)
      have := Indexed.owner_unique C p ei ej eq
      subst j;rfl
    | arm t =>
      have := paid_strict C p ei hi
      change rank n C p i = rank n C p C.size + t.val at eq
      omega
  | arm s =>
    cases b with
    | ext j =>
      obtain ⟨hj,gj,ej⟩ := present _ (extMem hb)
      have := paid_strict C p ej hj
      change rank n C p C.size+s.val = rank n C p j at eq
      omega
    | arm t =>
      change _+s.val = _+t.val at eq
      have h : s=t := Fin.ext (Nat.add_left_cancel eq)
      rw [h]
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
