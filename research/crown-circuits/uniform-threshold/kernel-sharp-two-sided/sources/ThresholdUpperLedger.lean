import ThresholdUpperEvaluation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
open scoped BigOperators

private theorem filter_degree {p q} (adj : Fin p → Finset (Fin q)) (j : Fin q) :
    ((List.finRange p).filter (fun i => decide (j∈adj i))).length =
    ∑ i : Fin p, if j∈adj i then 1 else 0 := by
  classical
  rw [← List.sum_ofFn]
  rw [List.ofFn_eq_map]
  induction List.finRange p with
  | nil => rfl
  | cons a l ih =>
    by_cases h : j∈adj a <;> simp [h,ih,Nat.add_comm]

theorem layer_bound {p q n} (adj : Fin p → Finset (Fin q)) (src : List Bit) (gs : List Gate)
    (outTwo : ∀ i,(adj i).card=2) (used : ∀ j,∃ i,j∈adj i) :
    ((layer n adj src).run gs).2.length + q ≤ gs.length + 2*p := by
  classical
  let d := fun j => ((List.finRange p).filter (fun i => decide (j∈adj i))).length
  have pos (j) : 0<d j := by
    obtain ⟨i,ij⟩ := used j
    apply List.length_pos_iff.mpr
    intro emp
    have mem : i∈((List.finRange p).filter (fun i => decide (j∈adj i))) := by simp [ij]
    simp [d,emp] at mem
  have localBound (j) : paid none (operands adj src j)+1≤d j := by
    have le := List.length_filterMap_le (f:=id) (l:=operands adj src j)
    have len : (operands adj src j).length=d j := by simp [operands,d]
    change ((operands adj src j).filterMap id).length-1+1≤d j
    have := pos j
    omega
  have total : (∑ j : Fin q,d j)=2*p := by
    simp_rw [show ∀ j,d j=∑ i : Fin p, if j∈adj i then 1 else 0 from filter_degree adj]
    rw [Finset.sum_comm]
    simp [outTwo,Nat.mul_comm]
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => localBound j)
  rw [Finset.sum_add_distrib,total] at bound
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at bound
  rw [layer_count]
  have conv : ((List.finRange q).map (fun j => paid none (operands adj src j))).sum =
      ∑ j : Fin q, paid none (operands adj src j) := by
    simpa [List.ofFn_eq_map] using (List.sum_ofFn (f:=fun j : Fin q => paid none (operands adj src j)))
  omega

theorem physical_budget {n v w z} (L : Layers n v w z) :
    (circuit L).size ≤ 2*n+v+w+16*z := by
  let a := (layer n L.first ((List.range n).map some)).run []
  let b := (layer n L.second a.1).run a.2
  let c := (layer n L.third b.1).run b.2
  have h1 := layer_bound (n:=n) L.first ((List.range n).map some) [] L.firstTwo L.firstUsed
  have h2 := layer_bound (n:=n) L.second a.1 a.2 L.secondTwo L.secondUsed
  have h3 := layer_bound (n:=n) L.third b.1 b.2 L.thirdTwo L.thirdUsed
  change a.2.length+v≤0+2*n at h1
  change b.2.length+w≤a.2.length+2*v at h2
  change c.2.length+z≤b.2.length+2*w at h3
  have len {α : Type} (items : List α) (f : α → Build Bit) (g : List Gate) :
      ((items.mapM f).run g).1.length=items.length := by
    induction items generalizing g with
    | nil => rfl
    | cons a items ih => rw [List.mapM_cons]; change (_ :: ((items.mapM f).run ((f a).run g).2).1).length=_; simp [ih]
  have lc : c.1.length=z := by
    unfold c layer
    rw [len,List.length_finRange]
  have hm := module_budget n c.1 (List.replicate 9 none) c.2
  rw [lc] at hm
  change ((c.1.foldlM (prefixStep n) (List.replicate 9 none)).run c.2).2.length ≤ _
  omega
end ThresholdThreeLayerUpper
