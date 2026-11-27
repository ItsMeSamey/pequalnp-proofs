import ExactPlaneEagerBank
import ExactPlanePivotCount
namespace ExactPlaneEagerCounts
open ExactPlaneGaussianMaterialized
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneFiveQueries ExactPlaneGaussianPacking
variable {w d n : ℕ}

/-- A pivot visit includes testing its bit even when the vector update is skipped. -/
def reduceC : Bank w n → Row w n → Row w n × ℕ
  | [],r => (r,0)
  | (i,p)::s,r =>
    let z := reduceC s (clear i p r)
    (z.1,z.2+1)

theorem reduceC_eq (s : Bank w n) (r : Row w n) :
    reduceC s r=(reduce s r,s.length) := by
  induction s generalizing r with
  | nil => rfl
  | cons a s ih =>
    rcases a with ⟨i,p⟩
    simp [reduceC,reduce,ih]

def insertC (s : Bank w n) (r : Row w n) : Bank w n × ℕ :=
  let z := reduceC s r
  (match ExactPlaneGaussian.pivot (readRow z.1).1 with
    | none => s
    | some i => s++[(i,z.1)],z.2)

theorem insertC_eq (s : Bank w n) (r : Row w n) :
    insertC s r=(ExactPlaneGaussianMaterialized.insert s r,s.length) := by
  simp [insertC,ExactPlaneGaussianMaterialized.insert,reduceC_eq] <;>
    cases ExactPlaneGaussian.pivot (readRow (reduce s r)).1 <;> rfl

def buildC (v : Fin n → Vector F w) : List (Fin n) → Bank w n × ℕ
  | [] => ([],0)
  | i::xs =>
    let old := buildC v xs
    let z := insertC old.1 (v i,Vector.ofFn (fun j : Fin n => if j=i then 1 else 0))
    (z.1,old.2+z.2)

theorem build_length (v : Fin n → Vector F w) (xs : List (Fin n)) : (build v xs).length≤w := by
  have lim := ExactPlaneGaussian.build_length_le (fun i j => (v i)[j]) xs
  rw [←read_build] at lim
  simpa [readBank] using lim

theorem buildC_spec (v : Fin n → Vector F w) (xs : List (Fin n)) :
    (buildC v xs).1=build v xs ∧ (buildC v xs).2≤xs.length*w := by
  induction xs with
  | nil => simp [buildC,build]
  | cons i xs ih =>
    simp only [buildC,insertC_eq,build,ih.1,List.length_cons,Nat.add_mul,one_mul]
    exact ⟨trivial,Nat.add_le_add ih.2 (build_length _ _)⟩

def answerC (s : Bank (d+4) n) (y : V (Key d)) : Bool × ℕ :=
  let z := reduceC s (materialize (pack y,0))
  (decide ((readRow z.1).1=0),z.2)

theorem answerC_eq (s : Bank (d+4) n) (y : V (Key d)) :
    answerC s y=(ExactPlaneEagerBank.answers s y,s.length) := by
  simp [answerC,ExactPlaneEagerBank.answers,reduceC_eq]

def allC (f : α→Bool×ℕ) : List α → Bool×ℕ
  | [] => (true,0)
  | x::xs =>
    let z := f x
    if z.1 then
      let tail := allC f xs
      (tail.1,z.2+tail.2)
    else (false,z.2)

theorem allC_value (f : α→Bool×ℕ) (xs : List α) :
    (allC f xs).1=xs.all (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (f x).1 <;> simp [allC,h,ih]

theorem allC_bound (f : α→Bool×ℕ) (xs : List α) (m : ℕ) (bound : ∀ x,(f x).2≤m) :
    (allC f xs).2≤xs.length*m := by
  induction xs with
  | nil => simp [allC]
  | cons x xs ih =>
    cases h : (f x).1 <;> simp only [allC,h,Bool.false_eq_true,ite_false,ite_true,
      List.length_cons,Nat.add_mul,one_mul]
    · exact (bound x).trans (Nat.le_add_left ..)
    · simpa only [Nat.add_comm m] using Nat.add_le_add (bound x) ih

def queries (d : ℕ) : List (V (Key d) × Bool) :=
  [((0,0,one),true),((0,0,two),true),((0,one,0),false),((0,two,0),false),((0,three,0),false)]

def queryC (s : Bank (d+4) n) (qy : V (Key d)×Bool) : Bool×ℕ :=
  let z := answerC s qy.1
  (z.1 == qy.2,z.2)

def checkC (A : List (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) : Bool×ℕ :=
  let s := buildC (ExactPlaneEagerBank.packed k b h) A
  let z := allC (queryC s.1) (queries d)
  (z.1,s.2+z.2)

theorem checkC_spec (A : List (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) :
    (checkC A k b h).1=ExactPlaneEagerBank.check A k b h ∧
    (checkC A k b h).2≤(A.length+5)*(d+4) := by
  let v := ExactPlaneEagerBank.packed k b h
  have hs := buildC_spec v A
  constructor
  · unfold checkC ExactPlaneEagerBank.check
    simp only [allC_value,queryC,answerC_eq]
    change (queries d).all (fun x => ExactPlaneEagerBank.answers (buildC v A).1 x.1 == x.2)=_
    rw [hs.1]
    simp [queries,Bool.and_assoc,v]
  · have per (x : V (Key d)×Bool) : (queryC (buildC v A).1 x).2≤d+4 := by
      simp only [queryC,answerC_eq,hs.1]
      exact build_length _ _
    have lim := allC_bound _ (queries d) _ per
    change (buildC v A).2+(allC (queryC (buildC v A).1) (queries d)).2≤_
    rw [Nat.add_mul]
    exact Nat.add_le_add hs.2 lim

def walkC (v : Fin n→Vector F w) : List (Fin n)→(Bank w n × Finset (Fin n))×ℕ
  | [] => (([],∅),0)
  | i::xs =>
    let prev := walkC v xs
    let key := fun j : Fin w => (v i)[j]
    let z := reduceC prev.1.1 (materialize (key,0))
    let ins := insertC prev.1.1 (materialize (key,Pi.single i 1))
    ((ins.1,if (readRow z.1).1=0 then prev.1.2 else Insert.insert i prev.1.2),
      prev.2 + z.2 + ins.2)

private theorem walk_length (v : Fin n→Vector F w) (xs : List (Fin n)) :
    (ExactPlaneEagerBank.walk v xs).1.length≤w := by
  have eq := congrArg Prod.fst (ExactPlaneEagerBank.walk_eq v xs)
  change readBank (ExactPlaneEagerBank.walk v xs).1=(ExactPlaneGaussianIDs.walk _ xs).1 at eq
  have lim := ExactPlaneGaussian.build_length_le (fun i j => (v i)[j]) xs
  rw [←ExactPlaneGaussianIDs.bank] at lim
  rw [←eq] at lim
  simpa only [readBank,List.length_map] using lim

theorem walkC_spec (v : Fin n→Vector F w) (xs : List (Fin n)) :
    (walkC v xs).1=ExactPlaneEagerBank.walk v xs ∧ (walkC v xs).2≤2*xs.length*w := by
  induction xs with
  | nil => simp [walkC,ExactPlaneEagerBank.walk]
  | cons i xs ih =>
    simp only [walkC,reduceC_eq,insertC_eq,ExactPlaneEagerBank.walk,ih.1,List.length_cons]
    constructor
    · trivial
    · have lim := walk_length v xs
      have sum := Nat.add_le_add (Nat.add_le_add ih.2 lim) lim
      calc
        _ ≤ 2*xs.length*w+w+w := sum
        _ = 2*(xs.length+1)*w := by ring

def basisC (A : Finset (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) : Finset (Fin n)×ℕ :=
  let z := walkC (ExactPlaneEagerBank.packed k b h) (A.sort (·≤·))
  (z.1.2,z.2)

theorem basisC_spec (A : Finset (Fin n)) (k : Fin n→Key d) (b h : Fin n→Plane) :
    (basisC A k b h).1=ExactPlaneEagerBank.basis A k b h ∧
    (basisC A k b h).2≤2*A.card*(d+4) := by
  have z := walkC_spec (ExactPlaneEagerBank.packed k b h) (A.sort (·≤·))
  exact ⟨congrArg Prod.snd z.1,by simpa [basisC] using z.2⟩

#print axioms checkC_spec
#print axioms basisC_spec
end ExactPlaneEagerCounts
