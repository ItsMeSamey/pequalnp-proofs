import ExactPlaneEagerDecision
namespace ExactPlaneChargedScan
structure Output (C I : Type*) where
  answer : Option (C × Finset I)
  tested : Nat
  siteTests : Nat
  checkPivots : Nat
  recovered : Nat
  basisPivots : Nat

def scan (prep : C→Finset I × Nat) (check : Finset I→Bool × Nat)
    (basis : Finset I→Finset I × Nat) : List C→Output C I
  | [] => ⟨none,0,0,0,0,0⟩
  | q::qs =>
    let A := prep q
    let cond := check A.1
    if cond.1 then
      let B := basis A.1
      ⟨some (q,B.1),1,A.2,cond.2,1,B.2⟩
    else
      let rest := scan prep check basis qs
      ⟨rest.answer,rest.tested+1,A.2+rest.siteTests,cond.2+rest.checkPivots,rest.recovered,rest.basisPivots⟩

theorem answer_eq (prep : C→Finset I × Nat) (check : Finset I→Bool × Nat)
    (basis : Finset I→Finset I × Nat) (qs : List C) :
    (scan prep check basis qs).answer=
      (ExactPlaneExecutableSelector.scan (fun q=>(prep q).1) (fun A=>(check A).1) qs).map
        (fun r=>(r.1,(basis r.2).1)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => cases h : (check (prep q).1).1 <;> simp [scan,ExactPlaneExecutableSelector.scan,h,ih]

theorem counts (prep : C→Finset I × Nat) (check : Finset I→Bool × Nat)
    (basis : Finset I→Finset I × Nat) (qs : List C) (n k b : Nat)
    (pc : ∀ q,(prep q).2=n) (cc : ∀ A,(check A).2≤k) (bc : ∀ A,(basis A).2≤b) :
    let o := scan prep check basis qs
    o.tested≤qs.length ∧ o.siteTests=o.tested*n ∧ o.checkPivots≤o.tested*k ∧
      o.recovered=(if o.answer.isSome then 1 else 0) ∧ o.basisPivots≤o.recovered*b := by
  induction qs with
  | nil => simp [scan]
  | cons q qs ih =>
    dsimp only at ih ⊢
    cases h : (check (prep q).1).1
    · simp only [scan,h,Bool.false_eq_true,ite_false,List.length_cons,Nat.add_mul,one_mul]
      obtain ⟨i,j,l,u,v⟩ := ih
      exact ⟨by omega,by rw [pc,j,Nat.add_comm],by have := cc (prep q).1; omega,u,v⟩
    · simp [scan,h,pc,cc,bc]
end ExactPlaneChargedScan
