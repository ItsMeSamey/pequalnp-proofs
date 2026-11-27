import IncidenceLabelHistory
import IncidenceSurvivingReads
namespace IncidenceCleanupLabels
open IncidenceLabelHistory IncidenceSurvivingReads IncidenceForwardPins CircuitRewire

def touched (g : ℕ→Gate) (removed : Finset ℕ) : Finset ℕ :=
  ((removed ×ˢ (Finset.univ : Finset Bool)).image (readPin g))

theorem touched_le (g : ℕ→Gate) (removed : Finset ℕ) : (touched g removed).card≤2*removed.card := by
  calc
    _ ≤ _ := Finset.card_image_le
    _ = _ := by simp [Finset.card_product,Nat.mul_comm]

def snap (N : ℕ) (f : ℕ→Gate) (L : Finset ℕ) : Snapshot ℕ :=
  ⟨L,fun x=>((pins N).filter (fun p=>readPin f p=x)).card,
   fun x=>decide (((pins N).filter (fun p=>readPin f p=x ∧ (f p.1).op=.meet)).Nonempty)⟩

theorem bill (g h : ℕ→Gate) (s t : ℕ) (liveBefore liveAfter : Finset ℕ)
    (kill : Finset ℕ) (map : Pin→Pin)
    (keep : ∀p∈pins s,p.1∉kill → readPin g p∈liveAfter →
      map p∈pins t ∧ readPin h (map p)=readPin g p)
    (inj : Set.InjOn map (↑((pins s).filter (fun p=>p.1∉kill)) : Set Pin))
    (andPin : ∀p∈pins s,p.1∉kill → (g p.1).op=.meet → (h (map p).1).op=.meet) :
    (drops (snap s g liveBefore) (snap t h liveAfter) ∪
      andLost (snap s g liveBefore) (snap t h liveAfter)).card≤2*kill.card := by
  classical
  apply le_trans (Finset.card_le_card ?_) (touched_le g kill)
  intro x hx
  by_contra miss
  have kept {p : Pin} (e : readPin g p=x) : p.1∉kill := by
    intro gone
    exact miss (Finset.mem_image.mpr ⟨p,Finset.mem_product.mpr ⟨gone,Finset.mem_univ _⟩,e⟩)
  rcases Finset.mem_union.mp hx with less|lost
  · obtain ⟨inLive,d⟩ := Finset.mem_filter.mp less
    have b : ((pins s).filter (fun p=>readPin g p=x)).card≤
        ((pins t).filter (fun p=>readPin h p=x)).card := by
      apply Finset.card_le_card_of_injOn map
      · intro p hp
        obtain ⟨ps,e⟩ := Finset.mem_filter.mp hp
        have ok := keep p ps (kept e) (e ▸ inLive)
        exact Finset.mem_filter.mpr ⟨ok.1,ok.2.trans e⟩
      · apply inj.mono
        intro p hp
        obtain ⟨ps,e⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨ps,kept e⟩
    exact (Nat.not_lt_of_ge b) d
  · obtain ⟨inLive,_,yes,_,no⟩ := Finset.mem_filter.mp lost
    obtain ⟨p,hp⟩ := of_decide_eq_true yes
    obtain ⟨ps,e,op⟩ := Finset.mem_filter.mp hp
    have ok := keep p ps (kept e) (e ▸ inLive)
    apply (of_decide_eq_false no)
    exact ⟨map p,Finset.mem_filter.mpr ⟨ok.1,ok.2.trans e,andPin _ ps (kept e) op⟩⟩
#print axioms bill
end IncidenceCleanupLabels
