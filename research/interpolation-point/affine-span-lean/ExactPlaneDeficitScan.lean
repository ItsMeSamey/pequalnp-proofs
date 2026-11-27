import ExactPlaneComputedDeficit
namespace ExactPlaneDeficitScan
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
variable {d N : ℕ}

def eqBits (x y : Key d) : Bool :=
  ((List.finRange d).map (fun i => decide (x i=y i))).all id

theorem eqBits_iff (x y : Key d) : eqBits x y=true ↔ x=y := by
  simp [eqBits]
  exact ⟨funext,fun h i => congrFun h i⟩

def tags : List Plane := [(0,0),(0,1),(1,0),(1,1)]
theorem mem_tags : ∀ t : Plane,t∈tags := by decide

def matching (p : Fin N → Key d) (i : Fin N) : List (Fin N) :=
  (List.finRange N).filter fun j => eqBits (p j) (p i)

def allTags (p : Fin N → Key d) (b : Fin N → Plane) (i : Fin N) : Bool :=
  let seen := (matching p i).map b
  tags.all fun t => seen.contains t

def accepted (p : Fin N → Key d) (b : Fin N → Plane) : Finset (Fin N) :=
  Finset.univ.filter fun i => allTags p b i=true

theorem accepted_eq (p : Fin N → Key d) (b : Fin N → Plane) :
    accepted p b=ExactPlaneComputedDeficit.complete p b := by
  ext i
  simp only [accepted,ExactPlaneComputedDeficit.complete,Finset.mem_filter,Finset.mem_univ,true_and,
    allTags,List.all_eq_true,List.contains_iff_mem,List.mem_map,matching,List.mem_filter,
    List.mem_finRange,true_and,eqBits_iff]
  exact ⟨fun h t => h t (mem_tags t), fun h t _ => h t⟩

/-- Comparison slots for this output-equivalent cached scan. The tag slot
count is an upper bound for short-circuit membership, not the number visited
by the original quantified test in ComputedDeficit.complete. -/
structure Counts where
  keyBits : ℕ
  tagPairs : ℕ
  firstRankSites : ℕ
  secondRankSites : ℕ
  deriving Repr

def counts (p : Fin N → Key d) (b : Fin N → Plane) : Counts where
  keyBits := ∑ _i : Fin N, (List.finRange N).length*(List.finRange d).length
  tagPairs := ∑ i : Fin N,tags.length*(matching p i).length
  firstRankSites := (Finset.univ : Finset (Fin N)).card
  secondRankSites := (accepted p b).card

def computed (p : Fin N → Key d) (b : Fin N → Plane) : ℕ :=
  ExactPlaneComputedDeficit.keyRank p Finset.univ -
    ExactPlaneComputedDeficit.keyRank p (accepted p b)

theorem computed_eq (p : Fin N → Key d) (b : Fin N → Plane) :
    computed p b=ExactPlaneComputedDeficit.computed p b := by
  rw [computed,accepted_eq,ExactPlaneComputedDeficit.computed]

theorem counts_bound (p : Fin N → Key d) (b : Fin N → Plane) :
    let c := counts p b
    c.keyBits=N^2*d ∧ c.tagPairs≤4*N^2 ∧ c.keyBits+2*c.tagPairs≤N^2*(d+8) ∧
      c.firstRankSites=N ∧ c.secondRankSites≤N := by
  intro c
  have key : c.keyBits=N^2*d := by simp [c,counts,pow_two,Nat.mul_assoc]
  have tag : c.tagPairs≤4*N^2 := by
    calc
      c.tagPairs ≤ ∑ _i : Fin N,4*N := by
        change (∑ i : Fin N,tags.length*(matching p i).length) ≤ _
        apply Finset.sum_le_sum
        intro i _
        change 4*(matching p i).length ≤ 4*N
        exact Nat.mul_le_mul_left 4 (by simpa [matching] using
          (List.length_filter_le (fun j => eqBits (p j) (p i)) (List.finRange N)))
      _ = _ := by simp [pow_two]; ring
  refine ⟨key,tag,?_,by simp [c,counts],?_⟩
  · rw [key,Nat.mul_add]
    omega
  · change (accepted p b).card ≤ N
    exact (Finset.card_le_univ (accepted p b)).trans_eq (Fintype.card_fin N)

/-- Materialize the entries once, retaining each matching-list length for the
comparison-slot ledger. The bound concerns comparisons, excluding rank work. -/
def inspect (p : Fin N → Key d) (b : Fin N → Plane) : Finset (Fin N) × Counts :=
  let entries := Vector.ofFn fun i : Fin N =>
    let seen := (matching p i).map b
    (tags.all (fun t => seen.contains t),seen.length)
  let keep := Finset.univ.filter (fun i : Fin N => entries[i].1=true)
  (keep,⟨N*N*d,∑ i : Fin N,tags.length*entries[i].2,N,keep.card⟩)

theorem inspect_eq (p : Fin N → Key d) (b : Fin N → Plane) :
    inspect p b=(accepted p b,counts p b) := by
  simp [inspect,accepted,allTags,counts,Nat.mul_assoc]

def run (p : Fin N → Key d) (b : Fin N → Plane) : ℕ × Counts :=
  let scanned := inspect p b
  (ExactPlaneComputedDeficit.keyRank p Finset.univ - ExactPlaneComputedDeficit.keyRank p scanned.1,
    scanned.2)

theorem run_eq (p : Fin N → Key d) (b : Fin N → Plane) :
    run p b=(ExactPlaneComputedDeficit.computed p b,counts p b) := by
  rw [run,inspect_eq,←computed_eq]
  rfl

#print axioms run_eq
#print axioms computed_eq
#print axioms counts_bound
end ExactPlaneDeficitScan
