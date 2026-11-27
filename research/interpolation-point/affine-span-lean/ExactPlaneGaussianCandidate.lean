import ExactPlaneGaussianPacking
import ExactPlaneGaussian
namespace ExactPlaneGaussianCandidate
open ExactPlaneGaussianPacking ExactPlaneFiveQueries ExactPlanePhysicalConverse
variable {d : ℕ} {I : Type*} [DecidableEq I]

def readBank (bank : ExactPlaneGaussian.Bank (d+4) I) (y : V (Key d)) : Option (I → F) :=
  let r := ExactPlaneGaussian.reduce bank (pack y,0)
  if r.1=0 then some r.2 else none

def bankFor (A : List I) (k : I → Key d) (b h : I → P) :=
  ExactPlaneGaussian.build (fun i => pack (k i,b i,h i)) A

def query (A : List I) (k : I → Key d) (b h : I → P) (y : V (Key d)) : Option (I → F) :=
  ExactPlaneGaussian.solve A (fun i => pack (k i,b i,h i)) (pack y)

theorem query_iff (A : List I) (k : I → Key d) (b h : I → P) (y : V (Key d)) :
    (query A k b h y).isSome=true ↔ y ∈ physicalSpan k b h A.toFinset := by
  rw [← pack_span]
  exact Option.isSome_iff_exists.trans (ExactPlaneGaussian.solve_hits _ _ _)

def check (A : List I) (k : I → Key d) (b h : I → P) : Bool :=
  let bank := bankFor A k b h
  let q := fun y => (readBank bank y).isSome
  q (0,0,one) && q (0,0,two) && !q (0,one,0) && !q (0,two,0) && !q (0,three,0)

theorem check_iff (A : List I) (k : I → Key d) (b h : I → P) :
    check A k b h=true ↔ ExactTrace k b h A.toFinset := by
  have spec := five_iff A.toFinset k b h
  dsimp only at spec
  rw [spec]
  change (((query A k b h (0,0,one)).isSome && (query A k b h (0,0,two)).isSome &&
    !(query A k b h (0,one,0)).isSome && !(query A k b h (0,two,0)).isSome &&
    !(query A k b h (0,three,0)).isSome) = true ↔ _)
  simp [←query_iff,and_assoc]

def supportQuery (A : List I) (k : I → Key d) (b h : I → P) (y : V (Key d)) :
    Option (Finset I) :=
  (query A k b h y).map (fun mask => A.toFinset.filter (fun i => mask i=1))

def supports (A : List I) (k : I → Key d) (b h : I → P) :=
  let bank := bankFor A k b h
  findSupports fun y => (readBank bank y).map (fun mask => A.toFinset.filter (fun i => mask i=1))

#print axioms check_iff
end ExactPlaneGaussianCandidate
