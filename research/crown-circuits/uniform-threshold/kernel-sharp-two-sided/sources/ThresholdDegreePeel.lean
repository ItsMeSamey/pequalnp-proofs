import ThresholdCentralRows
import ThresholdStarRemote
import ThresholdGraphStar
import ThresholdPhysicalRows

namespace ThresholdGlobalGlue
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ThresholdOrGroups
open ThresholdGraphPostorder ThresholdPeelSchedule

theorem star_peel {V E : Type*} [Fintype V] [DecidableEq V] {m : Nat}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    (j : V ↪ Fin m) (u : V) (noIso : ∀ v, ∃ w, G.Adj v w) (large : 2 ≤ G.degree u)
    (ends : E → Pins m) (f : Pins m → Bool) (rows : EdgeRows ends f)
    (edge : ∀ {a b}, G.Adj a b → ∃ e, ends e={j a,j b})
    (C : Circuit) (mono : Monotone2 C) (ok : Match C f ((Finset.univ : Finset V).map j)) :
    ∃ R : Circuit, Monotone2 R ∧ Match R f ((insert u (G.neighborFinset u)).map j) ∧
      ors R.gates + (Fintype.card V - Fintype.card G.ConnectedComponent - G.degree u) ≤ ors C.gates := by
  classical
  obtain ⟨S,ctr,remote,loc,nonempty,paired⟩ := star_seeds G u noIso
  obtain ⟨xs,order,num⟩ := component_seeds G S loc nonempty paired
  obtain ⟨x,z,hx,hz,fx,fz,accept⟩ := central_rows G j u ends f rows edge large
  have centerSub : S (G.connectedComponentMk u) ⊆ Finset.univ.biUnion S := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,hv⟩
  have cs : z ⊆ (Finset.univ.biUnion S).map j :=
    hz.trans (Finset.map_subset_map.mpr (ctr ▸ centerSub))
  obtain ⟨isched,iend⟩ := interior_schedule j G f (path_rows j G f ends rows edge) order z cs fz
  obtain ⟨I,im,imatch,icost⟩ := peel _ _ C mono ok isched
  rw [iend] at imatch
  have keepx : x⊆(S (G.connectedComponentMk u)).map j := ctr ▸ hx
  have keepz : z⊆(S (G.connectedComponentMk u)).map j := ctr ▸ hz
  have remoteOn (c : G.ConnectedComponent) (ne : c ≠ G.connectedComponentMk u)
      (a b : V) (ab : G.Adj a b) (shape : S c={a,b}) :
      f (insert (j b) (insert (j a) x))=true := by
    apply accept a b ab
    · intro eq
      exact ne ((loc c a (by simp [shape])).symm.trans (congrArg G.connectedComponentMk eq))
    · intro eq
      exact ne ((loc c b (by simp [shape])).symm.trans (congrArg G.connectedComponentMk eq))
  obtain ⟨rs,rsched,rend,rlen⟩ := star_remote_schedule G j u S loc remote f x z keepx keepz fx fz remoteOn
  obtain ⟨R,rm,rmatch,rcost⟩ := peel _ _ I im imatch rsched
  rw [rend,ctr] at rmatch
  have card := star_seed_card G u S ctr remote
  have positive : 1≤Fintype.card G.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk u⟩
  have count := charge_count positive card num
  refine ⟨R,rm,rmatch,?_⟩
  simp only [List.length_map] at icost
  omega

#print axioms star_peel
end ThresholdGlobalGlue
