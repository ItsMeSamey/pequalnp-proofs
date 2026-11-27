import ExactPlaneChargedOdd
namespace ExactPlaneChargedWords
variable {C : Type*}

/-- Prefix every supplied suffix, counting its one new word cons. -/
def prepend (x : C) : List (List C)→List (List C) × Nat
  | [] => ([],0)
  | v::vs =>
    let r := prepend x vs
    ((x::v)::r.1,r.2+1)

theorem prepend_eq (x : C) (vs : List (List C)) :
    prepend x vs=(vs.map (x::·),vs.length) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [prepend,ih]

def branches (suffix : C→List (List C) × Nat) : List C→List (List C) × Nat
  | [] => ([],0)
  | x::xs =>
    let prev := suffix x
    let ext := prepend x prev.1
    let rest := branches suffix xs
    (ext.1++rest.1,prev.2+ext.2+rest.2)

theorem branches_eq (vs : List (List C)) (k : Nat) (xs : List C) :
    branches (fun _=>(vs,k)) xs=(xs.flatMap (fun x=>vs.map (x::·)),xs.length*(k+vs.length)) := by
  induction xs with
  | nil => simp [branches]
  | cons x xs ih => simp [branches,prepend_eq,ih,Nat.add_mul,Nat.add_comm,Nat.add_assoc]

def words (s : List C) : Nat→List (List C) × Nat
  | 0 => ([[]],0)
  | j+1 => branches (fun _=>words s j) s

theorem words_eq (s : List C) (j : Nat) :
    words s j=(ExactPlaneOddChartList.words s j,j*s.length^j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [words,ih,branches_eq,ExactPlaneOddChartList.words,ExactPlaneOddChartList.length_words,pow_succ]
    congr 1
    ring

def odd (s : List C) : List (List C) × Nat :=
  let a := words s 1
  let b := words s 3
  let c := words s 5
  (a.1++b.1++c.1,a.2+b.2+c.2)

theorem odd_spec [AddMonoid C] (s : List C) :
    (odd s).1.map List.sum=ExactPlaneOddChartList.candidates s ∧
    (odd s).2=ExactPlaneChargedOdd.occurrences s.length := by
  simp [odd,words_eq,ExactPlaneOddChartList.candidates,ExactPlaneChargedOdd.occurrences]
#print axioms odd_spec
end ExactPlaneChargedWords
