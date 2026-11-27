import ExactPlaneGaussian

namespace ExactPlaneGaussianMaterialized
open ExactPlaneGaussian (F)

/-- Counted coordinates in two eager array-backed vectors. No previous-row function
is stored by a reduction step. Duplicate physical sites keep distinct indices. -/
abbrev Row (d n : Nat) := Vector F d × Vector F n
abbrev Bank (d n : Nat) := List (Fin d × Row d n)

def readRow (r : Row d n) : ExactPlaneGaussian.Row d (Fin n) :=
  (fun j => r.1[j], fun j => r.2[j])

def materialize (r : ExactPlaneGaussian.Row d (Fin n)) : Row d n :=
  (Vector.ofFn r.1,Vector.ofFn r.2)

@[simp] theorem read_materialize (r : ExactPlaneGaussian.Row d (Fin n)) :
    readRow (materialize r) = r := by
  ext j <;> simp [readRow,materialize]

def readBank (s : Bank d n) : ExactPlaneGaussian.Bank d (Fin n) :=
  s.map fun p => (p.1,readRow p.2)

def clear (i : Fin d) (p r : Row d n) : Row d n :=
  if r.1[i]=0 then r else
    (Vector.ofFn (fun j : Fin d => r.1[j]+p.1[j]),
     Vector.ofFn (fun j : Fin n => r.2[j]+p.2[j]))

theorem read_clear (i : Fin d) (p r : Row d n) :
    readRow (clear i p r) = ExactPlaneGaussian.clear i (readRow p) (readRow r) := by
  have bit : ∀ a : F, a=0 ∨ a=1 := by decide
  rcases bit (r.1[i]) with e|e <;>
    (simp only [Fin.getElem_fin] at e <;> ext j <;> simp [readRow,clear,ExactPlaneGaussian.clear,Fin.getElem_fin,e])

def reduce : Bank d n → Row d n → Row d n
  | [], r => r
  | (i,p)::s, r => reduce s (clear i p r)

theorem read_reduce (s : Bank d n) (r : Row d n) :
    readRow (reduce s r) = ExactPlaneGaussian.reduce (readBank s) (readRow r) := by
  induction s generalizing r with
  | nil => rfl
  | cons p s ih =>
    rcases p with ⟨i,p⟩
    simpa only [reduce,readBank,List.map_cons,ExactPlaneGaussian.reduce,read_clear] using ih (clear i p r)

def insert (s : Bank d n) (r : Row d n) : Bank d n :=
  let t := reduce s r
  match ExactPlaneGaussian.pivot (readRow t).1 with
  | none => s
  | some i => s ++ [(i,t)]

theorem read_insert (s : Bank d n) (r : Row d n) :
    readBank (insert s r) = ExactPlaneGaussian.insert (readBank s) (readRow r) := by
  unfold insert ExactPlaneGaussian.insert
  rw [← read_reduce]
  cases h : ExactPlaneGaussian.pivot (readRow (reduce s r)).1 <;> simp [h,readBank]

def build (v : Fin n → Vector F d) : List (Fin n) → Bank d n
  | [] => []
  | i::s => insert (build v s)
      (v i,Vector.ofFn (fun j : Fin n => if j=i then 1 else 0))

theorem read_build (v : Fin n → Vector F d) (xs : List (Fin n)) :
    readBank (build v xs) = ExactPlaneGaussian.build (fun i j => (v i)[j]) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [build,read_insert,ih,ExactPlaneGaussian.build]
    congr 1
    apply Prod.ext
    · rfl
    · funext j
      by_cases e : j=i
      · subst j; simp [readRow]
      · simp [readRow,e,Ne.symm e]

def solve (v : Fin n → Vector F d) (xs : List (Fin n)) (y : Vector F d) : Option (Vector F n) :=
  let r := reduce (build v xs) (y,Vector.replicate n 0)
  if (readRow r).1 = 0 then some r.2 else none

theorem read_solve (v : Fin n → Vector F d) (xs : List (Fin n)) (y : Vector F d) :
    (solve v xs y).map (fun a => fun j : Fin n => a[j]) =
      ExactPlaneGaussian.solve xs (fun i j => (v i)[j]) (fun j => y[j]) := by
  let z : Row d n := (y,Vector.replicate n 0)
  have start : readRow z = ((fun j : Fin d => y[j]),0) := by
    ext j <;> simp [readRow,z]
  have step := read_reduce (build v xs) z
  rw [read_build,start] at step
  unfold solve ExactPlaneGaussian.solve
  rw [←step]
  change (if (readRow (reduce (build v xs) z)).1 = 0 then
    some (reduce (build v xs) z).2 else none).map _ = _
  by_cases e : (readRow (reduce (build v xs) z)).1=0 <;> simp only [e,if_true,if_false,Option.map_some,Option.map_none] <;> rfl

#print axioms read_solve
end ExactPlaneGaussianMaterialized
