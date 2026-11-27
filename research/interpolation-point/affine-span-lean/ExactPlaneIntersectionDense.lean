import ExactPlaneIntersectionBasis
namespace ExactPlaneIntersectionDense
open ExactPlaneGaussian (F V)
open ExactPlaneIntersectionBasis ExactPlaneIntersectionKernel
open ExactPlaneGaussianMaterialized
variable {d n : ℕ}

def readVec (x : Vector F d) : V d := fun i => x[i]
@[simp] theorem read_store (x : V d) : readVec (Vector.ofFn x)=x := by
  funext j; simp [readVec,Fin.getElem_fin]

def residue (bank : Bank d n) (x : V d) : V d :=
  (readRow (reduce bank (materialize (x,0)))).1

def cols (v : Fin n → V d) (l r : List (Fin n)) : Vector (Vector F (d+d)) d :=
  let table := Vector.ofFn fun i => Vector.ofFn (v i)
  let left := build (fun i => table[i]) l
  let right := build (fun i => table[i]) r
  Vector.ofFn fun i : Fin d =>
    let unit : V d := Pi.single i 1
    let a := residue left unit
    let b := residue right unit
    Vector.ofFn (Fin.append a b)

theorem read_cols (v : Fin n → V d) (l r : List (Fin n)) (i : Fin d) :
    readVec ((cols v l r)[i])=combined v l r (Pi.single i 1) := by
  simp only [cols,Fin.getElem_fin,Vector.getElem_ofFn,read_store,residue,read_reduce,
    read_build,read_materialize]
  funext j
  refine Fin.addCases (fun a=>?_) (fun b=>?_) j <;>
    simp only [Fin.append_left,Fin.append_right,combined,LinearMap.pi_apply,Fin.addCases_left,
      Fin.addCases_right,LinearMap.comp_apply,LinearMap.proj_apply] <;> rfl

def vectors (v : Fin n → V d) (l r : List (Fin n)) : List (V d) :=
  let col := cols v l r
  let bank := build (fun i => col[i]) (List.finRange d)
  (List.finRange d).map fun i =>
    let tag := (readRow (reduce bank (materialize (readVec col[i],0)))).2
    readVec (Vector.ofFn (fun j => (Pi.single i (1:F) : V d) j-tag j))

theorem vectors_eq (v : Fin n → V d) (l r : List (Fin n)) :
    vectors v l r=(List.finRange d).map (generators (combined v l r)) := by
  unfold vectors
  apply List.map_congr_left
  intro i _
  have cols_eq : (fun j => readVec ((cols v l r)[j])) =
      (fun j => combined v l r (Pi.single j 1)) := funext (read_cols v l r)
  simp only [read_store,read_reduce,read_materialize,read_build]
  funext j
  change (Pi.single i (1:F) : V d) j -
    (ExactPlaneGaussian.reduce
      (ExactPlaneGaussian.build (fun a => readVec ((cols v l r)[a])) (List.finRange d))
      (readVec ((cols v l r)[i]),0)).2 j = _
  rw [cols_eq,read_cols]
  rfl

def basisRows (v : Fin n → V d) (l r : List (Fin n)) :=
  ExactPlaneFeatureStream.select Vector.ofFn (vectors v l r)

theorem basisRows_eq (v : Fin n → V d) (l r : List (Fin n)) :
    basisRows v l r=ExactPlaneIntersectionBasis.basisRows v l r := by
  simp [basisRows,ExactPlaneIntersectionBasis.basisRows,vectors_eq]

#print axioms basisRows_eq
end ExactPlaneIntersectionDense
