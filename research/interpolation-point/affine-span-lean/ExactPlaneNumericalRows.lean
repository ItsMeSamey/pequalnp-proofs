import ExactPlaneConcreteSampler
import ExactPlaneEagerDecision
namespace ExactPlaneNumericalRows
open ExactPlaneFieldSampler ExactPlaneSamplerRank

def words : (r : Nat) → List (V r)
  | 0 => [fun i=>Fin.elim0 i]
  | r+1 => (words r).map (Fin.cons 0) ++ (words r).map (Fin.cons 1)

theorem mem_words : ∀ {r} (x : V r), x ∈ words r := by
  intro r
  induction r with
  | zero => intro x; have eq : x=(fun i : Fin 0=>Fin.elim0 i) := by funext i; exact Fin.elim0 i
            simp [words,eq]
  | succ r ih =>
    intro x
    have decomp : Fin.cons (x 0) (fun i => x i.succ)=x := by
      funext j
      exact Fin.cases (by simp) (fun i=>by simp) j
    have bit : ∀ a : F,a=0 ∨ a=1 := by decide
    rcases bit (x 0) with h|h
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨_,ih _,h ▸ decomp⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,ih _,h ▸ decomp⟩

theorem length_words (r : Nat) : (words r).length=2^r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [words,ih,pow_succ,Nat.mul_two]

def rows (r m : Nat) (entry : V r → V r → V m) : List (Vector F m) :=
  (words r).flatMap fun x => (words r).map fun t => Vector.ofFn (entry x t)

theorem length_rows (r m : Nat) (entry : V r → V r → V m) :
    (rows r m entry).length=(2^r)^2 := by
  simp [rows,List.length_flatMap,length_words,List.sum_replicate,pow_two]

theorem mem_row (r m : Nat) (entry : V r → V r → V m) (x t : V r) :
    Vector.ofFn (entry x t) ∈ rows r m entry := by
  apply List.mem_flatMap.mpr
  exact ⟨x,mem_words _,List.mem_map.mpr ⟨t,mem_words _,rfl⟩⟩

def points (l : List (Vector F m)) : List (V m) := l.map fun v j=>v[j]

theorem hits (r m R : Nat) (entry : V r → V r → V m)
    (K : Type*) [Field K] [Algebra F K] [Fintype K] [Fintype (D K)]
    (elt : V r → K) (dual : V r → D K)
    (elts : Function.Surjective elt) (duals : Function.Surjective dual)
    (agree : ∀ a t j, entry a t j=dual t ((elt a)^j.val))
    (hm : 0<m) (large : m*2^R<Fintype.card K) :
    OntoHits (points (rows r m entry)).toFinset R := by
  classical
  intro k hk f onto y
  obtain ⟨s,hs,ev⟩ := field_hits m R K hm large k hk f onto y
  refine ⟨s,?_,ev⟩
  obtain ⟨⟨z,l⟩,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨a,rfl⟩ := elts z
  obtain ⟨t,rfl⟩ := duals l
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨_,mem_row r m entry a t,by funext j; simpa [sample] using agree a t j⟩

def zeroRow : List (Vector F 0) := [Vector.ofFn fun i=>Fin.elim0 i]

theorem zero_hits (R : Nat) : OntoHits (points zeroRow).toFinset R := by
  have eq : (points zeroRow).toFinset = {0} := by
    ext x
    have h : x=0 := Subsingleton.elim _ _
    simp [h,points,zeroRow]
    exact Subsingleton.elim _ _
  rw [eq]
  exact ExactPlaneFieldSampler.zero_hits R

def run {N d m : Nat} (samples : List (Vector F m))
    (chart : Vector F m → Vector ExactPlaneResidualPivots.Plane N)
    (keys : Vector (Vector F d) N) (tags heights : Vector ExactPlaneResidualPivots.Plane N) :=
  ExactPlaneEagerSelector.runPacked (samples.map chart) keys tags heights
end ExactPlaneNumericalRows
