import ThresholdAmbientEffectiveGraph
namespace ThresholdAmbientEffectiveGraph
variable {V : Type*} [DecidableEq V] [Fintype V] (S : Finset V)
abbrev Four := {F : Finset ↥S // F.card=4}
def ambientBox (F : Four S) : Finset V := F.val.map (Function.Embedding.subtype _)
noncomputable def boxes := Finset.univ.image (ambientBox S)
theorem box_four (F) (hf : F∈boxes S) : F.card=4 := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hf
  simpa [ambientBox] using x.property
theorem box_injective : Function.Injective (ambientBox S) := by
  intro a b eq
  apply Subtype.ext
  exact Finset.map_injective _ eq
theorem sum_boxes (f : Finset V→Nat) :
    (∑ F∈boxes S,f F)=∑ F : Four S,f (ambientBox S F) := by
  classical
  unfold boxes
  exact Finset.sum_image (fun _ _ _ _ h => box_injective S h)
theorem chart_box (F : Four S) (e : Fin 4 ≃ ↥F.val) :
    Finset.univ.map ((e.toEmbedding.trans (Function.Embedding.subtype (·∈F.val))).trans
      (Function.Embedding.subtype (·∈S)))=ambientBox S F := by
  ext v
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_map.mpr ⟨(e i).val,(e i).property,rfl⟩
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
    refine Finset.mem_map.mpr ⟨e.symm ⟨i,hi⟩,Finset.mem_univ _,?_⟩
    change (e (e.symm ⟨i,hi⟩)).val.val=i.val
    rw [e.apply_symm_apply]
end ThresholdAmbientEffectiveGraph
