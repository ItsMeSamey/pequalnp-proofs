import ExactPlaneGaussianMaterialized
import ExactPlaneGaussianDecision
namespace ExactPlaneEagerBank
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneFiveQueries ExactPlaneGaussianPacking
open ExactPlaneGaussianMaterialized
variable {d n : Nat}

abbrev VKey (d : ℕ) := Vector F d
def packed (k : Fin n→Key d) (b h : Fin n→Plane) (i : Fin n) : VKey (d+4) :=
  Vector.ofFn (pack (k i,b i,h i))

def answers (bank : Bank (d+4) n) (y : V (Key d)) : Bool :=
  let r := reduce bank (materialize (pack y,0))
  decide ((readRow r).1=0)

theorem answers_eq (bank : Bank (d+4) n) (y : V (Key d)) :
    answers bank y=(ExactPlaneGaussianCandidate.readBank (readBank bank) y).isSome := by
  have step := read_reduce bank (materialize (pack y,0))
  rw [read_materialize] at step
  unfold answers ExactPlaneGaussianCandidate.readBank
  dsimp only
  rw [step]
  split <;> simp_all

def check (A : List (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) : Bool :=
  let bank := build (packed k b h) A
  let q := answers bank
  q (0,0,one) && q (0,0,two) && !q (0,one,0) && !q (0,two,0) && !q (0,three,0)

theorem packed_read (k : Fin n→Key d) (b h : Fin n→Plane) :
    (fun i j=>(packed k b h i)[j])=(fun i=>pack (k i,b i,h i)) := by
  funext i j
  simp [packed]

theorem check_eq (A : List (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) :
    check A k b h=ExactPlaneGaussianCandidate.check A k b h := by
  simp only [check,answers_eq,read_build,packed_read,ExactPlaneGaussianCandidate.check,
    ExactPlaneGaussianCandidate.bankFor]

/-- This walk retains original input IDs. Both the membership residual
and the inserted row have eagerly materialized key and provenance vectors. -/
def walk (v : Fin n→VKey d) : List (Fin n)→Bank d n × Finset (Fin n)
  | []=>([],∅)
  | i::xs=>
    let prev := walk v xs
    let key := fun j : Fin d=>(v i)[j]
    let residual := reduce prev.1 (materialize (key,0))
    (ExactPlaneGaussianMaterialized.insert prev.1 (materialize (key,Pi.single i 1)),
     if (readRow residual).1=0 then prev.2 else Insert.insert i prev.2)

theorem walk_eq (v : Fin n→VKey d) (xs : List (Fin n)) :
    (readBank (walk v xs).1,(walk v xs).2)=ExactPlaneGaussianIDs.walk (fun i j=>(v i)[j]) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have bank := congrArg Prod.fst ih
    have ids := congrArg Prod.snd ih
    dsimp only at bank ids
    simp only [walk,ExactPlaneGaussianIDs.walk,read_insert,read_reduce,read_materialize,bank,ids]

def basis (A : Finset (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) :=
  (walk (packed k b h) (A.sort (·≤·))).2

theorem basis_eq (A : Finset (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) :
    basis A k b h=ExactPlaneGaussianIDs.basis A k b h := by
  have equal := congrArg Prod.snd (walk_eq (packed k b h) (A.sort (·≤·)))
  simpa only [basis,ExactPlaneGaussianIDs.basis,ExactPlaneGaussianIDs.col,packed_read] using equal
#print axioms check_eq
#print axioms basis_eq
end ExactPlaneEagerBank
