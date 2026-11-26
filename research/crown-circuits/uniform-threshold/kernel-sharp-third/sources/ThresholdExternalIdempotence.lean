import ThresholdSharedPairMinimum
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open ThresholdFactorExpr ThresholdFactorRecipe ThresholdFactorNetwork ThresholdFactorForest
open ThresholdUniqueRaw T2OrPartition T2SoleOrSplice
open private erase_or cost_zero disj_available from ThresholdSharedPairErase
open private save rawBound flatten from ThresholdSharedPairMinimum
namespace ThresholdExternalIdempotence
theorem external_once {C : Circuit} {n} (L : Layout C n) (pin : Id C → Nat)
    (inner : MeetsInternal L) (mini : LexMinimum n C) (hn : 2≤n)
    (p : Nat) (t : Tree) (ht : Block.group p t∈forest L pin) (w : Nat) : t.exts.count w≤1 := by
  by_contra excess
  have hit : w∈t.exts := List.count_pos_iff.mp (by omega)
  have still : w∈t.exts.erase w := List.count_pos_iff.mp (by simp; omega)
  let args := t.raws.map Term.raw ++ (t.exts.erase w).map Term.ref
  have sz : args.length=t.gates.length := by
    have slots := t.slots
    have pos := List.length_pos_of_mem hit
    simp [args,List.length_erase_of_mem hit]; omega
  have zero : (args.map Term.cost).sum=0 := by
    unfold args
    rw [List.map_append,List.sum_append,cost_zero _ Term.raw (fun _ => rfl),cost_zero _ Term.ref (fun _ => rfl)]
  have count := disj_cost args
  cases d : disj args with
  | none =>
    rw [d] at count
    have mem : Term.ref w ∈ args := by simp [args,still]
    simp [count] at mem
  | some q =>
    have cost : q.cost+1=t.gates.length := by simpa [d,sz,zero] using count
    have shape := forest_checked L pin _ ht
    obtain ⟨D,hm,small,correct⟩ := save L pin inner (.group p t) q ht cost (by
      intro seen refs
      apply disj_available _ _ _ d
      intro a ha
      rcases List.mem_append.mp ha with l|r
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp l
        exact rawBound t shape i hi
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp r
        exact refs i (List.mem_of_mem_erase hi)) (by
      intro v len
      let R := fun i => v.getD i false
      let F := fun i => (C.wires v).getD i false
      have sem := disj_sem R F args
      rw [d] at sem
      have untouched : (t.exts.erase w).any F=t.exts.any F := by
        rw [←erase_or _ w F hit]
        cases a : F w
        · simp
        · simp [List.any_eq_true.mpr ⟨w,still,a⟩]
      have raw := ordinary_real (.group p t) shape v len F (fun _ _ => rfl)
      change (treeTerm t).value R F=_ at raw
      rw [flatten] at raw
      exact (by simpa [valOpt,args,List.any_append,List.any_map,Function.comp_def,Term.value,untouched] using sem : q.value R F=_).trans raw)
      (T2BenchmarkNormalize.output_internal mini.eligible)
    have correctT : Computes n D := by
      intro s; rw [correct _ (by simp [vector])]; exact mini.eligible.1 s
    obtain ⟨E,he,sz⟩ := T2BenchmarkNormalize.canNormalize hn D hm correctT
    have least := mini.primary E he
    omega
end ThresholdExternalIdempotence
