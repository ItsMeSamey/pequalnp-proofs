import ExactPlaneDirectDivisionCount
namespace ExactPlaneModulusCharges
open ExactPlaneIrreducibleSearch (Word words words_length)
open ExactPlaneDirectDivision (divides fastFind slots slots_exact)

/-- Short-circuit universal test. The predicate supplies the cost of each
visited item. The unvisited tail contributes zero. -/
def allCount {α : Type*} (step : α→Bool×ℕ) : List α→Bool×ℕ
  | [] => (true,0)
  | x::xs =>
    let here := step x
    if here.1 then
      let rest := allCount step xs
      (rest.1,here.2+rest.2)
    else (false,here.2)

theorem all_spec {α : Type*} (step : α→Bool×ℕ) (budget : α→ℕ)
    (cap : ∀ x,(step x).2 ≤ budget x) (xs : List α) :
    (allCount step xs).1=xs.all (fun x=>(step x).1) ∧
    (allCount step xs).2≤(xs.map budget).sum := by
  induction xs with
  | nil => simp [allCount]
  | cons x xs ih =>
    cases b : (step x).1
    · simp [allCount,b,(cap x).trans (Nat.le_add_right _ _)]
    · simpa only [allCount,b,ite_true,List.all_cons,Bool.true_and,List.map_cons,List.sum_cons]
        using And.intro ih.1 (Nat.add_le_add (cap x) ih.2)

def degreeRun {n : ℕ} (w : Word n) (j : ℕ) : Bool×ℕ :=
  allCount (fun u=>(!(divides u w),1)) (words (j+1))

theorem degree_spec {n : ℕ} (w : Word n) (j : ℕ) :
    (degreeRun w j).1=(words (j+1)).all (fun u=> !(divides u w)) ∧
    (degreeRun w j).2≤(words (j+1)).length := by
  have ones (l : List (Word (j+1))) : (l.map (fun _=>(1:ℕ))).sum=l.length := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih,Nat.add_comm]
  obtain ⟨eq,le⟩ := all_spec (fun u : Word (j+1)=>(!(divides u w),1))
    (fun _=>1) (fun _=>le_rfl) (words (j+1))
  exact ⟨eq,le.trans_eq (ones _)⟩

def candidate {n : ℕ} (w : Word n) : Bool×ℕ :=
  allCount (degreeRun w) (List.range (n/2))

theorem candidate_spec {n : ℕ} (w : Word n) :
    (candidate w).1=ExactPlaneDirectDivision.good w ∧ (candidate w).2≤slots n := by
  obtain ⟨eq,le⟩ := all_spec (degreeRun w) (fun j=>(words (j+1)).length)
    (fun j=>(degree_spec w j).2) (List.range (n/2))
  refine ⟨?_,?_⟩
  · simpa only [candidate,ExactPlaneDirectDivision.good,(degree_spec w _).1] using eq
  · have sumRange (k : ℕ) : ((List.range k).map fun j=>(words (j+1)).length).sum =
          ∑ j∈Finset.range k,(words (j+1)).length := by
        induction k with
        | zero => simp
        | succ k ih => simp [List.range_succ,Finset.sum_range_succ,ih]
    simpa only [candidate,slots,sumRange] using le

structure Result (α : Type*) where
  answer : Option α
  candidates : ℕ
  divisions : ℕ
  deriving Repr

def scan {n : ℕ} : List (Word n)→Result (Word n)
  | [] => ⟨none,0,0⟩
  | w::ws =>
    let here := candidate w
    if here.1 then ⟨some w,1,here.2⟩ else
      let rest := scan ws
      ⟨rest.answer,rest.candidates+1,here.2+rest.divisions⟩

theorem scan_spec {n : ℕ} (ws : List (Word n)) :
    (scan ws).answer=ws.find? ExactPlaneDirectDivision.good ∧
    (scan ws).candidates≤ws.length ∧ (scan ws).divisions≤(scan ws).candidates*slots n := by
  induction ws with
  | nil => simp [scan]
  | cons w ws ih =>
    obtain ⟨flag,cap⟩ := candidate_spec w
    cases hw : (candidate w).1
    · have bad := flag.symm.trans hw
      simpa only [scan,hw,Bool.false_eq_true,ite_false,List.find?_cons,bad,List.length_cons,
        Nat.succ_mul] using And.intro ih.1 (And.intro (Nat.succ_le_succ ih.2.1)
          ((Nat.add_le_add cap ih.2.2).trans_eq (Nat.add_comm _ _)))
    · have good := flag.symm.trans hw
      simp [scan,hw,List.find?_cons,good,cap]

def search (n : ℕ) := scan (words n)

theorem search_spec (n : ℕ) :
    (search n).answer=fastFind n ∧ (search n).candidates≤2^n ∧
    (search n).divisions≤(search n).candidates*(2^(n/2+1)-2) := by
  have cost := slots_exact n
  have exactSlots : slots n=2^(n/2+1)-2 := by omega
  simpa only [search,fastFind,words_length,exactSlots] using scan_spec (words n)

theorem divisions_bound (n : ℕ) :
    (search n).divisions≤2^n*(2^(n/2+1)-2) :=
  (search_spec n).2.2.trans (Nat.mul_le_mul_right _ (search_spec n).2.1)
#print axioms search_spec
#print axioms divisions_bound
end ExactPlaneModulusCharges
