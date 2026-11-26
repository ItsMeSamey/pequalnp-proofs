import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

namespace ThresholdComponentEdges
open scoped BigOperators

/-- Local bound on twice the edge count, in additive form to avoid truncation. -/
theorem local_bound {j Δ d : Nat} (hj : 2 ≤ j)
    (simple : d ≤ j*(j-1)) (maxdeg : d ≤ j*Δ) :
    d + 2*(Δ+2) ≤ 2+j*(Δ+2) := by
  by_cases h : j ≤ Δ+1
  · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hj
    have h' : 1+a ≤ Δ := by omega
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h'
    have hs : 2+a-1=1+a := by omega
    rw [hs] at simple
    nlinarith [Nat.zero_le (a*b)]
  · nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] [Fintype G.ConnectedComponent] [DecidableEq G.ConnectedComponent]

/-- This uses the actual graph degrees and the number of nonempty connected components.
    No assumptions on the maximum beyond the stated common degree bound are needed. -/
theorem component_edges {Δ : Nat} (noIso : ∀ v, ∃ w, G.Adj v w)
    (bound : ∀ v, G.degree v ≤ Δ) :
    2 * G.edgeFinset.card ≤ 2*Fintype.card G.ConnectedComponent +
      (Fintype.card V - 2*Fintype.card G.ConnectedComponent)*(Δ+2) := by
  classical
  let B := fun c : G.ConnectedComponent =>
    Finset.univ.filter (fun v : V => G.connectedComponentMk v = c)
  have loc {c : G.ConnectedComponent} {x : V} (hx : x ∈ B c) :
      G.degree x + 1 ≤ (B c).card := by
    have same := (Finset.mem_filter.mp hx).2
    have sub : insert x (G.neighborFinset x) ⊆ B c := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hadj
      · exact hx
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ((G.mem_neighborFinset x y).mp hadj)).symm.trans same⟩
    simpa [Finset.card_insert_of_notMem, G.card_neighborFinset_eq_degree] using Finset.card_le_card sub
  have jmin (c : G.ConnectedComponent) : 2 ≤ (B c).card := by
    refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    obtain ⟨w,hw⟩ := noIso v
    have hh : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr hw⟩
    have hv := loc (c := G.connectedComponentMk v) (x := v) (by simp [B])
    rw [G.card_neighborFinset_eq_degree] at hh
    omega
  have comp (c : G.ConnectedComponent) :
      (∑ x ∈ B c, G.degree x) + 2*(Δ+2) ≤ 2+(B c).card*(Δ+2) := by
    apply local_bound (jmin c)
    · calc
        _ ≤ ∑ _x ∈ B c, ((B c).card-1) := Finset.sum_le_sum fun x hx => by
          have := loc hx
          omega
        _ = _ := by simp
    · calc
        _ ≤ ∑ _x ∈ B c, Δ := Finset.sum_le_sum fun x _ => bound x
        _ = _ := by simp
  have fiber (f : V → Nat) : (∑ c, ∑ x ∈ B c, f x) = ∑ x, f x := by
    exact Finset.sum_fiberwise_of_maps_to (g := G.connectedComponentMk)
      (fun i (_ : i ∈ (Finset.univ : Finset V)) => Finset.mem_univ _) f
  have total : (∑ c, (B c).card) = Fintype.card V := by
    simpa using fiber (fun _ => 1)
  have enough := Finset.sum_le_sum (s := Finset.univ) (fun c _ => jmin c)
  have enough' : 2*Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
    simpa [total,Nat.mul_comm] using enough
  have h := Finset.sum_le_sum (s := Finset.univ) (fun c _ => comp c)
  simp only [Finset.sum_add_distrib, fiber, ← Finset.sum_mul, total,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, G.sum_degrees_eq_twice_card_edges] at h
  have split := congrArg (fun x : Nat => x*(Δ+2)) (Nat.sub_add_cancel enough')
  nlinarith

end ThresholdComponentEdges
