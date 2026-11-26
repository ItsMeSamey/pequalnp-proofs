import T2CubeAgreement
import T2CubeDeletion
import T2BenchmarkNormalize

namespace T2RawUsed
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion

/-- A threshold-two output distinct from a raw input must physically read it. -/
theorem positive_readers_of_ne {n out : Nat} (hn : 2 ≤ n) (gs : List Raw)
    (correct : Computes n (source gs out)) (x : Fin n) (notOut : out ≠ x.val) :
    0 < (gs.filter (rawReads x.val)).length := by
  classical
  cases hfilter : gs.filter (rawReads x.val) with
  | cons hd tl => simp
  | nil =>
    exfalso
    have miss : ∀ g ∈ (source gs out).gates, x.val ∉ g.inputs := by
      intro g hg
      change g ∈ gs.map _ at hg
      obtain ⟨⟨op,l,r⟩, hr, rfl⟩ := List.mem_map.mp hg
      intro hx
      have hp : rawReads x.val (op,l,r) = true := by
        change x.val ∈ [l,r] at hx
        rcases List.mem_cons.mp hx with hl | hr
        · simp [rawReads,hl]
        · have hxr : x.val = r := by simpa using hr
          simp [rawReads,hxr]
      have hf : (op,l,r) ∈ gs.filter (rawReads x.val) := List.mem_filter.mpr ⟨hr,hp⟩
      rw [hfilter] at hf
      simp at hf
    let y : Fin n := if x.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
    have hxy : x ≠ y := by
      intro e
      have v := congrArg Fin.val e
      by_cases h : x.val = 0 <;> simp [y,h] at v <;> omega
    have same := (T2RawIsolation.unread_run (source gs out).gates
      (off_insert ({y} : Finset (Fin n)) x) miss).2 out notOut
    change (source gs out).eval (vector {y}) =
      (source gs out).eval (vector (insert x {y})) at same
    have accepts := (correct (insert x {y})).mpr (by simp [hxy])
    have rejects := (correct {y}).mp (same.trans accepts)
    simp at rejects

theorem positive_readers {n out : Nat} (hn : 2 ≤ n) (gs : List Raw)
    (eligible : Eligible n (source gs out)) (x : Fin n) :
    0 < (gs.filter (rawReads x.val)).length := by
  obtain ⟨j,hj⟩ := T2BenchmarkNormalize.output_internal eligible
  change out = n+j.val at hj
  apply positive_readers_of_ne hn gs eligible.1 x
  have hx := x.isLt
  omega

#print axioms positive_readers
end T2RawUsed
