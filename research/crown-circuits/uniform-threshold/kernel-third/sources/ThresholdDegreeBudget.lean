import ThresholdDegreePeel
import ThresholdGraphCounts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ThresholdOrGroups ThresholdOrExtraction
open ThresholdSimpleIncidence ThresholdRegularSource ThresholdStarTruth T2SoleOrSplice ThresholdPeelSchedule
namespace ThresholdGlobalGlue

theorem original_or_floor {n} (B : Circuit) (bm : Monotone2 B) (full : Computes n B) :
    2*n-4 ≤ ors B.gates := by
  have base := FreeAndNet.threshold_two_circuit_or_lower n B bm full
  have flags : FreeAndNet.CircuitCompiler.orFlag=isOr := by funext g; cases g with | mk op ins => cases op <;> rfl
  simpa only [flags,ors,List.countP_eq_length_filter] using base

attribute [local instance] Classical.propDecidable
theorem physical_degree_budget {B : Circuit} {n} (L : Layout B n) (u : ThresholdGraphCounts.Vtx L)
    (bm : Monotone2 B) (full : Computes n B)
    (two : ∀ w,(endpoints L w).card=2) (inj : Function.Injective (endpoints L))
    (D : Circuit) (dm : Monotone2 D)
    (rep : ∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card)
    (price : ors D.gates+2*n≤ors B.gates+(vertices L).card)
    :
    (graph L).degree u+2*n≤ors B.gates+4+Nat.card (graph L).ConnectedComponent := by
  classical
  let G := graph L
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have comp : 0<Fintype.card G.ConnectedComponent := Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk u⟩
  change G.degree u+2*n≤ors B.gates+4+Nat.card G.ConnectedComponent
  rw [Nat.card_eq_fintype_card]
  by_cases large : 2≤G.degree u
  · have noIso (v) : ∃ w, G.Adj v w := by
      have h : 0<(G.neighborFinset v).card := by rw [G.card_neighborFinset_eq_degree]; exact ThresholdGraphCounts.degree_pos L v two inj
      obtain ⟨w,hw⟩ := Finset.card_pos.mp h
      exact ⟨w,(G.mem_neighborFinset v w).mp hw⟩
    let j := pinEmbedding L
    let f := fun s : Pins B.gates.length => D.eval (List.ofFn (row s))
    have ok : Match D f (Finset.univ.map j) := fun _ _ => rfl
    obtain ⟨R,rm,matchR,pr⟩ := star_peel G j u noIso large (endpoints L) f
      (physical_rows L D rep) (edge_realized L two) D dm ok
    have floor := ThresholdGraphStar.physical_star_floor L two u (G.neighborFinset u)
      (fun a ha => (G.mem_neighborFinset u a).mp ha) R D rm _ matchR rep
      (Finset.mem_map.mpr ⟨u,by simp,rfl⟩)
      (fun a ha => Finset.mem_map.mpr ⟨a,Finset.mem_insert_of_mem ha,rfl⟩)
    rw [G.card_neighborFinset_eq_degree] at floor
    have vc : Fintype.card ↥(vertices L)=(vertices L).card := Fintype.card_coe _
    omega
  · have floor := original_or_floor B bm full
    omega

#print axioms physical_degree_budget
end ThresholdGlobalGlue
