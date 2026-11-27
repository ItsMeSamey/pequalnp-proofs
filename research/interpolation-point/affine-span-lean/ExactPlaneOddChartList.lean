import Mathlib.Algebra.BigOperators.Group.List.Basic
namespace ExactPlaneOddChartList
variable {C : Type*}

def words (seed : List C) : Nat→List (List C)
  | 0 => [[]]
  | n+1 => seed.flatMap (fun x=>(words seed n).map (x::·))

theorem mem_words (seed : List C) (n : Nat) (l : List C) :
    l∈words seed n ↔ l.length=n ∧ ∀ x∈l,x∈seed := by
  induction n generalizing l with
  | zero => cases l <;> simp [words]
  | succ n ih =>
    cases l with
    | nil => simp [words,List.mem_flatMap]
    | cons a l =>
      simp only [words,List.mem_flatMap,List.mem_map]
      constructor
      · rintro ⟨x,hx,v,hv,eq⟩
        cases eq
        obtain ⟨size,inside⟩ := (ih _).mp hv
        exact ⟨by simp [size],by simpa using And.intro hx inside⟩
      · rintro ⟨len,inside⟩
        refine ⟨a,inside a (by simp),l,(ih _).mpr ⟨by simpa using len,?_⟩,rfl⟩
        exact fun x h=>inside x (by simp [h])

private theorem flat_length (l : List C) (f : C→List (List C)) (k : Nat)
    (eq : ∀ x,(f x).length=k) : (l.flatMap f).length=l.length*k := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih,eq,Nat.succ_mul,Nat.add_comm]

theorem length_words (seed : List C) (n : Nat) : (words seed n).length=seed.length^n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simpa only [words,pow_succ,Nat.mul_comm] using
      flat_length seed (fun x=>(words seed n).map (x::·)) (seed.length^n) (fun _=>by simp [ih])

def candidates [AddMonoid C] (seed : List C) : List C :=
  (words seed 1 ++ words seed 3 ++ words seed 5).map List.sum

theorem mem_candidates [AddMonoid C] (seed : List C) (g : C) :
    g∈candidates seed ↔ ∃ l : List C,(∀ x∈l,x∈seed) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧ l.sum=g := by
  simp only [candidates,List.mem_map,List.mem_append,mem_words]
  aesop

theorem count_candidates [AddMonoid C] (seed : List C) :
    (candidates seed).length=seed.length+seed.length^3+seed.length^5 := by
  simp [candidates,length_words,Nat.add_assoc]
#print axioms mem_candidates
#print axioms count_candidates
end ExactPlaneOddChartList
