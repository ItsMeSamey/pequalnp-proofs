import ThresholdFourThirdsArithmetic
import T2BenchmarkNormalize
import Batteries.Tactic.OpenPrivate

namespace ThresholdPublicMinimum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2SoleOrSplice
open private run_app run_len run_old from T2SoleOrEval
open private binary_val from GateSurplus

private def add (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n+C.gates.length⟩

private theorem add_works (n : ℕ) (C : Circuit) (o : Op) (i j : ℕ)
    (v : List Bool) (hv : v.length=n) :
    (add n C (binary o i j)).eval v =
      act o ((run C.gates v).getD i false) ((run C.gates v).getD j false) := by
  change (run (C.gates++[binary o i j]) v).getD (n+C.gates.length) false=_
  rw [run_app, binary_val, ← hv, ← run_len, getD_new]

private theorem add_mono {n : ℕ} {C : Circuit} (h : Monotone2 C) (o : Op) (i j : ℕ) :
    Monotone2 (add n C (binary o i j)) := by
  intro g hg
  change g ∈ C.gates ++ [binary o i j] at hg
  rcases List.mem_append.mp hg with old | last
  · exact h g old
  · have e : g = binary o i j := by simpa using last
    subst g
    cases o <;> simp [binary, gateOp]

private def emptyBank (n : ℕ) : Circuit := ⟨[⟨.or,[]⟩],n⟩

/-- Native OR of a list of two-variable conjunctions. -/
private theorem pair_bank {n : ℕ} (xs : List (Fin n × Fin n)) :
    ∃ C : Circuit, Monotone2 C ∧ C.output < n+C.gates.length ∧
      ∀ s : Finset (Fin n), C.eval (vector s)=true ↔
        ∃ p ∈ xs, p.1 ∈ s ∧ p.2 ∈ s := by
  induction xs with
  | nil =>
    refine ⟨emptyBank n, ?_, by simp [emptyBank], ?_⟩
    · intro g hg
      have e : g=⟨.or,[]⟩ := by simpa [emptyBank] using hg
      subst g
      simp
    · intro s
      change ((vector s)++[false]).getD n false=true ↔ _
      have vlen : (vector s).length=n := by simp [vector]
      have hfalse := getD_new (vector s) false
      rw [vlen] at hfalse
      rw [hfalse]; simp
  | cons p xs ih =>
    obtain ⟨C, mono, fit, spec⟩ := ih
    let D := add n C (binary .and p.1 p.2)
    let E := add n D (binary .or C.output D.output)
    refine ⟨E, add_mono (add_mono mono .and _ _) .or _ _, ?_, ?_⟩
    · simp [E, add]
    · intro s
      let v := vector s
      have arity : v.length=n := by simp [v,vector]
      have raw (i : Fin n) : (run C.gates v).getD i.val false = decide (i∈s) := by
        rw [run_old _ _ _ (by simpa [arity] using i.isLt)]
        simp [v,vector,List.getD_eq_getElem?_getD]
      have dval : D.eval v = (decide (p.1∈s) && decide (p.2∈s)) := by
        dsimp only [D]
        rw [add_works _ _ _ _ _ _ arity,raw,raw]
        rfl
      have old : (run D.gates v).getD C.output false = C.eval v := by
        change (run (C.gates ++ [_]) v).getD C.output false=_
        rw [run_app, run_old _ _ _ (by simpa [run_len,arity] using fit)]
        rfl
      change E.eval v=true ↔ _
      dsimp only [E]
      rw [add_works _ _ _ _ _ _ arity,old]
      change (C.eval v || D.eval v)=true ↔ _
      rw [dval,Bool.or_eq_true,Bool.and_eq_true,spec]
      simp [List.mem_cons,or_comm]

theorem benchmark_exists (n : ℕ) : ∃ C : Circuit, Monotone2 C ∧ Computes n C := by
  classical
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1≠p.2)
  obtain ⟨C,hm,_,hs⟩ := pair_bank pairs.toList
  refine ⟨C,hm,fun s => (hs s).trans ?_⟩
  constructor
  · rintro ⟨⟨i,j⟩,hij,hi,hj⟩
    exact Finset.one_lt_card.mpr ⟨i,hi,j,hj,by simpa [pairs] using hij⟩
  · intro h
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp h
    exact ⟨(i,j),by simp [pairs,hij],hi,hj⟩

def Attained (n k : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ Computes n C ∧ C.size=k

private theorem attainable (n : ℕ) : ∃ k, Attained n k := by
  obtain ⟨C, hm, hc⟩ := benchmark_exists n
  exact ⟨C.size,C,hm,hc,rfl⟩

/-- Minimum over all benchmark Monotone2 circuits. -/
noncomputable def minimum (n : ℕ) : ℕ := by
  classical
  exact Nat.find (attainable n)

theorem attained (n : ℕ) : Attained n (minimum n) := by
  classical
  exact Nat.find_spec (attainable n)

theorem le_size {n : ℕ} {C : Circuit} (hm : Monotone2 C) (hc : Computes n C) :
    minimum n ≤ C.size := by
  classical
  exact Nat.find_min' (attainable n) (show Attained n C.size from ⟨C,hm,hc,rfl⟩)

theorem eligible_mono {n : ℕ} {C : Circuit} (h : Eligible n C) : Monotone2 C := by
  intro g hg
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hg
  let j : Fin C.gates.length := ⟨i,hi⟩
  have row := h.2.2 j
  change (C.gates[i].op=GateOp.and ∨ C.gates[i].op=GateOp.or) ∧
    C.gates[i].inputs.length=2 ∧ _ at row
  rw [he] at row
  exact ⟨by simpa using row.1, Nat.le_of_eq row.2.1⟩

theorem lex_size {n : ℕ} {C : Circuit} (hn : 2≤n) (hc : LexMinimum n C) :
    C.size = minimum n := by
  obtain ⟨D,hm,hd,he⟩ := attained n
  have h := hc.benchmark_bound (T2BenchmarkNormalize.canNormalize hn) D hm hd
  rw [he] at h
  exact Nat.le_antisymm h (le_size (eligible_mono hc.eligible) hc.eligible.1)

theorem lex_at_minimum {n : ℕ} (hn : 2≤n) :
    ∃ C : Circuit, LexMinimum n C ∧ C.size=minimum n := by
  obtain ⟨D,hm,hd⟩ := benchmark_exists n
  obtain ⟨E,he,_⟩ := T2BenchmarkNormalize.canNormalize hn D hm hd
  obtain ⟨C,hc⟩ := exists_lexMinimum ⟨E,he⟩
  exact ⟨C,hc,lex_size hn hc⟩

/-- Normalization uses the full two-point row to exclude constants; the live
output cannot be raw because its own singleton must be rejected. -/
theorem base_one : 1 ≤ minimum 2 := by
  obtain ⟨C,hC,he⟩ := lex_at_minimum (by decide : 2≤2)
  obtain ⟨j,_⟩ := T2BenchmarkNormalize.output_internal hC.eligible
  rw [←he]
  change 1≤C.gates.length
  have ht := j.isLt
  omega

noncomputable abbrev intMinimum (n : ℕ) : ℤ := (minimum n : ℤ)

theorem representative_excess {n : ℕ} {C : Circuit} (hn : 2≤n) (hc : LexMinimum n C) :
    ThresholdFourThirds.excess intMinimum n = (C.size : ℤ) - 2 * (n : ℤ) := by
  rw [lex_size hn hc]
  rfl

theorem deletion_price {n : ℕ} {C D : Circuit} (hn : 2≤n+1) (hC : LexMinimum (n+1) C)
    (hm : Monotone2 D) (hD : Computes n D) (budget : D.size+3≤C.size) :
    intMinimum n + 3 ≤ intMinimum (n+1) := by
  have h := (Nat.add_le_add_right (le_size hm hD) 3).trans budget
  rw [lex_size hn hC] at h
  exact_mod_cast h

end ThresholdPublicMinimum
