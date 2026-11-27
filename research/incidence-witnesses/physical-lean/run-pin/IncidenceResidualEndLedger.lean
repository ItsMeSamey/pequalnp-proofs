import IncidenceResidualPorts
namespace IncidenceResidualEndLedger
open CircuitRewire IncidenceResidualPorts
open scoped BigOperators

theorem endpoint_bound (g : ℕ → Gate) (n s out k : ℕ) (wt : ℕ → ℕ)
    (bad : Finset ℕ) (good : ℕ) (split : good+bad.card=n)
    (hout : out<n+s) (ord : ∀ j<s,(g j).left<n+s ∧ (g j).right<n+s)
    (live : ∀ i<n+s,0<readers g s out i)
    (raw : ∀ i<n,wt i=1) (cap : ∀ i<n+s,wt i≤k)
    (thin : ∀ i∈bad,i<n+s ∧ wt i=1 ∧ 2≤readers g s out i)
    (demand : k*good+(∑ j ∈ Finset.range s,wt (n+j)) ≤
      ∑ j ∈ Finset.range s,(wt (g j).left+wt (g j).right)) :
    2*n-1-(2*n)/(k+1)≤s := by
  classical
  let T := Finset.range (n+s)
  let R := readers g s out
  let ex := fun i => R i-1
  let a := ∑ i ∈ bad,ex i
  let b := ∑ i ∈ T \ bad,ex i
  have sub : bad⊆T := fun i hi => Finset.mem_range.mpr (thin i hi).1
  have paid : bad.card ≤ a := by
    calc
      _ = ∑ i ∈ bad,1 := by simp
      _ ≤ a := Finset.sum_le_sum (fun i hi => by
        have := (thin i hi).2.2; change 1 ≤ readers g s out i-1; omega)
  have part : ∑ i ∈ T,ex i = a+b := by
    dsimp [a,b]; rw [Nat.add_comm,Finset.sum_sdiff sub]
  have un := balance g n s out (fun _=>1) hout ord
  simp only [Nat.mul_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at un
  rw [← Finset.sum_range_add] at un
  have eq (i : ℕ) (hi : i∈T) : ex i+1=R i := by
    have := live i (Finset.mem_range.mp hi); change readers g s out i-1+1=readers g s out i; omega
  change (∑ i ∈ T,R i)=s*(1+1)+1 at un
  rw [← Finset.sum_congr rfl eq,Finset.sum_add_distrib,part] at un
  have liveEq : n+(a+b)=s+1 := by simp [T] at un; omega
  have weighted := balance g n s out wt hout ord
  rw [← Finset.sum_range_add] at weighted
  have expand (i : ℕ) (hi : i∈T) : R i*wt i=ex i*wt i+wt i := by
    rw [← eq i hi,Nat.add_mul,one_mul]
  change (∑ i ∈ T,R i*wt i)=_ at weighted
  rw [Finset.sum_congr rfl expand,Finset.sum_add_distrib] at weighted
  have rawMass : (∑ i ∈ T,wt i)=n+∑ j ∈ Finset.range s,wt (n+j) := by
    dsimp [T]; rw [Finset.sum_range_add]
    have h : (∑ i ∈ Finset.range n, wt i)=∑ _i ∈ Finset.range n,1 :=
      Finset.sum_congr rfl (fun i hi=>raw i (Finset.mem_range.mp hi))
    simp [h]
  rw [rawMass] at weighted
  have mass : (∑ i ∈ T,ex i*wt i) ≤ a+b*k := by
    rw [← Finset.sum_sdiff sub (f:=fun i=>ex i*wt i)]
    have h : (∑ i ∈ bad,ex i*wt i)=a := Finset.sum_congr rfl (fun i hi=>by rw [(thin i hi).2.1,Nat.mul_one])
    rw [h,Nat.add_comm]
    apply Nat.add_le_add_left
    dsimp [b]; rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (cap i (Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1)))
  have lower : k*good ≤ n+a+b*k := by omega
  have kn : k*n≤n+(k+1)*(a+b) := by
    have m := Nat.mul_le_mul_left k paid
    rw [←split,Nat.mul_add]; nlinarith
  by_cases enough : 2*n≤s+1
  · exact (Nat.sub_le _ _).trans (by omega : 2*n-1≤s)
  let d := 2*n-(s+1)
  have eqd : d+(s+1)=2*n := by dsimp [d]; omega
  have m := congrArg (fun j : Nat => (k+1)*j) eqd
  have l := congrArg (fun j : Nat => (k+1)*j) liveEq
  have fit : d*(k+1)≤2*n := by nlinarith [m,l]
  have h := (Nat.le_div_iff_mul_le (by omega : 0<k+1)).2 fit
  change 2*n-(s+1) ≤ 2*n/(k+1) at h
  clear * - h
  omega
#print axioms endpoint_bound
end IncidenceResidualEndLedger
