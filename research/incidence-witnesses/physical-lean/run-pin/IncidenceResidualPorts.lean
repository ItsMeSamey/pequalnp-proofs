import IncidenceResidualWeight
import Research.CircuitRewire
namespace IncidenceResidualPorts
open CircuitRewire
open scoped BigOperators

/-- Include the output socket itself, even if output is also read internally. -/
def readers (g : ℕ → Gate) (s out i : ℕ) : ℕ :=
  (∑ j ∈ Finset.range s, ((if (g j).left=i then 1 else 0) +
     (if (g j).right=i then 1 else 0))) + (if out=i then 1 else 0)

theorem balance (g : ℕ → Gate) (n s out : ℕ) (wt : ℕ → ℕ)
    (hout : out<n+s) (valid : ∀ j<s, (g j).left<n+s ∧ (g j).right<n+s) :
    (∑ i ∈ Finset.range n, readers g s out i * wt i) +
      (∑ j ∈ Finset.range s, readers g s out (n+j)*wt (n+j)) =
    (∑ j ∈ Finset.range s, (wt (g j).left + wt (g j).right)) + wt out := by
  rw [← Finset.sum_range_add]
  simp only [readers,Nat.add_mul,Finset.sum_mul]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  have inner (j : ℕ) (hj : j<s) :
      (∑ i ∈ Finset.range (n+s),
        (((if (g j).left=i then 1 else 0) * wt i) +
         ((if (g j).right=i then 1 else 0) * wt i))) =
        wt (g j).left+wt (g j).right := by
    obtain ⟨hl,hr⟩ := valid j hj
    simp [Finset.sum_add_distrib,ite_mul,hl,hr]
  have outterm : (∑ i ∈ Finset.range (n+s), (if out=i then 1 else 0)*wt i)=wt out := by
    simp [ite_mul,hout]
  rw [outterm]
  exact congrArg (· + wt out) (Finset.sum_congr rfl (fun j hj =>
    inner j (Finset.mem_range.mp hj)))

theorem residual (g : ℕ → Gate) (n s out k : ℕ) (wt : ℕ → ℕ)
    (hout : out<n+s) (valid : ∀ j<s, (g j).left<n+s ∧ (g j).right<n+s)
    (live : ∀ i<n+s, 0<readers g s out i)
    (raw : ∀ i<n, wt i=1) (cap : ∀ j<s, wt (n+j)≤k)
    (demand : let sole := (Finset.range n).filter fun i => readers g s out i=1
      k*sole.card + (∑ j ∈ Finset.range s, wt (n+j)) ≤
        ∑ j ∈ Finset.range s, (wt (g j).left+wt (g j).right)) :
    2*n-1-(2*n)/(k+1)≤s := by
  let R := readers g s out
  let A := Finset.range n
  let B := Finset.range s
  let sole := A.filter fun i => R i=1
  let a := ∑ i ∈ A, (R i-1)
  let b := ∑ j ∈ B, (R (n+j)-1)
  have rA (i : ℕ) (hi : i∈A) : R i-1+1=R i := by
    have lt := Finset.mem_range.mp hi
    have := live i (by omega); dsimp [R]; omega
  have rB (j : ℕ) (hj : j∈B) : R (n+j)-1+1=R (n+j) := by
    have lt := Finset.mem_range.mp hj
    have := live (n+j) (by omega); dsimp [R]; omega
  have sumA : (∑ i ∈ A, R i)=a+n := by
    rw [← Finset.sum_congr rfl rA]
    simp [a,A,Finset.sum_add_distrib]
  have sumB : (∑ j ∈ B, R (n+j))=b+s := by
    rw [← Finset.sum_congr rfl rB]
    simp [b,B,Finset.sum_add_distrib]
  have unity := balance g n s out (fun _ => 1) hout valid
  simp only [Nat.mul_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at unity
  change (∑ i ∈ A,R i)+(∑ j ∈ B,R (n+j))=s*(1+1)+1 at unity
  rw [sumA,sumB] at unity
  have wb : (∑ j ∈ B,R (n+j)*wt (n+j)) ≤ b*k+∑ j ∈ B,wt (n+j) := by
    calc
      _ = ∑ j ∈ B,((R (n+j)-1)*wt (n+j)+wt (n+j)) := Finset.sum_congr rfl (fun j hj => by
        calc
          _ = (R (n+j)-1+1)*wt (n+j) := by rw [rB j hj]
          _ = _ := by simp [Nat.add_mul])
      _ ≤ ∑ j ∈ B,((R (n+j)-1)*k+wt (n+j)) := Finset.sum_le_sum (fun j hj =>
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (cap j (Finset.mem_range.mp hj))) _)
      _ = _ := by simp [b,Finset.sum_add_distrib,Finset.sum_mul]
  have weighted := balance g n s out wt hout valid
  have wa : (∑ i ∈ A,R i*wt i)=a+n := by
    calc
      _ = ∑ i ∈ A,R i := Finset.sum_congr rfl (fun i hi => by rw [raw i (Finset.mem_range.mp hi),Nat.mul_one])
      _ = _ := sumA
  change (∑ i ∈ A,R i*wt i)+(∑ j ∈ B,R (n+j)*wt (n+j))=_ at weighted
  rw [wa] at weighted
  change k*sole.card + (∑ j ∈ B,wt (n+j)) ≤ _ at demand
  have lower : k*sole.card ≤ a+n+b*k := by omega
  have covered : n ≤ sole.card+a := by
    have each : ∀ i∈A, 1 ≤ (if R i=1 then 1 else 0)+(R i-1) := by
      intro i hi; have := rA i hi; split <;> omega
    have sum := Finset.sum_le_sum each
    simpa [Finset.sum_add_distrib,sole,a,A] using sum
  have kn : k*n ≤ n+(k+1)*(a+b) := by
    have h := Nat.mul_le_mul_left k covered
    nlinarith
  by_cases enough : 2*n≤s+1
  · exact (Nat.sub_le _ _).trans (by omega : 2*n-1≤s)
  let d := 2*n-(s+1)
  have eq : d+(s+1)=2*n := by dsimp [d]; omega
  have liveEq : n+(a+b)=s+1 := by omega
  have m := congrArg (fun j : Nat => (k+1)*j) eq
  have l := congrArg (fun j : Nat => (k+1)*j) liveEq
  have fit : d*(k+1)≤2*n := by nlinarith [m,l]
  have h := (Nat.le_div_iff_mul_le (by omega : 0<k+1)).2 fit
  change 2*n-(s+1) ≤ 2*n/(k+1) at h
  clear * - h
  omega
#print axioms balance
#print axioms residual
end IncidenceResidualPorts
