import ThresholdPhysicalReceiverGraph
namespace ThresholdPhysicalReceiverGraph
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition ThresholdRegularSource
open ThresholdSimpleIncidence T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdSecondaryReceivers ThresholdHighComponents ThresholdSharedPartition

theorem graph_power {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {g w M : Nat} (size : G.edgeFinset.card=g)
    (wc : Fintype.card V=w) (charge : ThresholdC4.ordered G≤24*M)
    (gp : 0<g) (dense : w^3≤g^2) : g^4≤12*M*w^4 := by
  have pos : 0<G.edgeFinset.card := by rw [size]; exact gp
  obtain ⟨p,_⟩ := Finset.card_pos.mp pos
  have nonempty : Nonempty V := by
    induction p using Sym2.ind with
    | _ a b => exact ⟨a⟩
  have wp : 0<w := wc ▸ Fintype.card_pos_iff.mpr nonempty
  have wg : w≤g := by
    by_contra! bad
    have gap := Nat.pow_lt_pow_left bad (by decide : (2:Nat)≠0)
    have step : w^2≤w^3 := by
      have a := Nat.mul_le_mul_left (w^2) (by omega : 1≤w)
      simpa only [Nat.mul_one,pow_succ w 2] using a
    omega
  have total := ThresholdC4.with_missing24 G (by rw [wc]; exact wp) (by rw [wc,size]; exact wg)
    (by rw [wc,size]; exact dense) charge
  simpa only [wc,size] using total

attribute [local instance] familyAdj

set_option maxHeartbeats 2000000 in
theorem native_power {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out))
    (reg : Regular n gs) (hn : 2≤n) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let g := (good C n H).card
    let w := (receivers C n H).card
    0<g → w^3≤g^2 → g^4≤12*ThresholdHubMissing.M L*w^4 := by
  classical
  intro C L H g w gp dense
  let S := receivers C n H
  let G := ThresholdFamilySimpleGraph.graph S (edgeFamily C n H)
  let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
  obtain ⟨size,cost⟩ := high_graph minim reg hn
  change G.edgeFinset.card=g at size
  change ThresholdC4.ordered G≤24*(ThresholdC4Missing.missing (good C n H) A).card at cost
  have simple := classified_simple hn minim reg
  have sub : good C n H⊆hubs C n := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have miss := missing_global L simple.1 simple.2.1 (good C n H) sub
  exact graph_power G size (Fintype.card_coe S)
    (cost.trans (Nat.mul_le_mul_left 24 miss)) gp dense
end ThresholdPhysicalReceiverGraph
