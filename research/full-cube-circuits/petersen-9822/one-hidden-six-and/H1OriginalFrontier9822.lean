import H1OriginalAndSites9822
namespace Research.H1Price
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FreeAndNet.CircuitCompiler
open PEqualNP.Outside.L_meta_9822.Clean PEqualNP.Outside.L_meta_9822.Sectors
def physicalFront (C : Circuit) := (discover 10 C.gates {C.output}).1
def physicalHidden (C : Circuit) := originalAndSites 10 C.gates \ physicalFront C
theorem front_subset (C : Circuit) (cand : Candidate C) (clean : CleanL 10 C.gates)
    (zero : C.gates.countP countsNot=0) : physicalFront C ⊆ originalAndSites 10 C.gates := by
  intro x hx
  have bound : ∀ x∈({C.output} : Finset Nat),x<10+C.gates.length := by simpa using original_output_bound C cand
  rcases frontier_raw_or_and _ 10 _ (actual_binary clean zero) bound x hx with lo|inside
  · exact False.elim (frontier_no_raw C cand clean zero x lo hx)
  · exact inside
theorem original_hidden_binary (C : Circuit) (clean : CleanL 10 C.gates)
    (zero : C.gates.countP countsNot=0) {hidden : Nat} (hm : hidden∈physicalHidden C) :
    ∃ i g l r,C.gates[i]?=some g ∧ hidden=10+i ∧ g.op=.and ∧
      l<hidden ∧ r<hidden ∧ g.inputs=[l,r] := by
  have inSites := (Finset.mem_sdiff.mp hm).1
  obtain ⟨lo,hi⟩ := andSite_bounds inSites
  let i := hidden-10
  have valid : i<C.gates.length := by dsimp [i];omega
  have addr : hidden=10+i := by dsimp [i];omega
  have hit : C.gates[i]?=some C.gates[i] := List.getElem?_eq_getElem valid
  have kind := (andSite_lookup C.gates 10 i C.gates[i] hit).1 (addr ▸ inSites)
  obtain ⟨l,r,hl,hr,inputs⟩ := (actual_binary clean zero i C.gates[i] hit).2
  exact ⟨i,C.gates[i],l,r,hit,addr,kind,by omega,by omega,inputs⟩
theorem front_card (C : Circuit) (cand : Candidate C) (clean : CleanL 10 C.gates)
    (zero : C.gates.countP countsNot=0) (six : C.gates.countP countsAnd=6) :
    (physicalHidden C).card=1 ↔ (physicalFront C).card=5 := by
  have inc := front_subset C cand clean zero
  have sc := andSite_card C.gates 10
  have small := Finset.card_le_card inc
  rw [physicalHidden,Finset.card_sdiff_of_subset inc,sc,six]
  omega
theorem original_frontier (C : Circuit) (cand : Candidate C) (clean : CleanL 10 C.gates)
    (zero : C.gates.countP countsNot=0) (six : C.gates.countP countsAnd=6) (one : (physicalHidden C).card=1) :
    ∃ hidden,physicalHidden C={hidden} ∧ (physicalFront C).card=5 ∧
      hidden∈originalAndSites 10 C.gates ∧ hidden∉physicalFront C ∧
      (∀ k<10,k∉physicalFront C) ∧
      (∀ i g,C.gates[i]?=some g → 10+i∈physicalFront C →
        orFlag g=false ∧ 10+i≠hidden ∧ g.op=.and ∧
        ∃ l r,l<10+i ∧ r<10+i ∧ g.inputs=[l,r]) ∧
      (∀ x∈physicalFront C,∃ i g,C.gates[i]?=some g ∧ x=10+i) := by
  obtain ⟨hidden,sh⟩ := Finset.card_eq_one.mp one
  have hm : hidden∈physicalHidden C := by simp [sh]
  obtain ⟨hs,hf⟩ := Finset.mem_sdiff.mp hm
  have inc := front_subset C cand clean zero
  refine ⟨hidden,sh,(front_card C cand clean zero six).mp one,hs,hf,frontier_no_raw C cand clean zero,?_,?_⟩
  · intro i g hit mem
    have op := (andSite_lookup C.gates 10 i g hit).1 (inc mem)
    exact ⟨by simp [orFlag,op],fun eq => hf (eq ▸ mem),op,(actual_binary clean zero i g hit).2⟩
  · intro x mem
    obtain ⟨lo,hi⟩ := andSite_bounds (inc mem)
    let i := x-10
    have valid : i<C.gates.length := by dsimp [i];omega
    exact ⟨i,C.gates[i],List.getElem?_eq_getElem valid,by dsimp [i];omega⟩
end Research.H1Price
#print axioms Research.H1Price.original_frontier
