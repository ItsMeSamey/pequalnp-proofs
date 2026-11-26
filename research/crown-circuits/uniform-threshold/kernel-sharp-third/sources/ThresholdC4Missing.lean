import ThresholdC4
namespace ThresholdC4Missing
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
def presentations (S : Finset V) := S.offDiag.sigma (fun p => ((S.erase p.1).erase p.2).offDiag)
def support (ends : I → Finset V) (p : Finset I) := p.biUnion ends
def missing (labels : Finset I) (actual : Finset (Finset I)) := labels.powersetCard 2 \ actual

private theorem card_presentations (S : Finset V) (h : S.card≤4) : (presentations S).card≤24 := by
  classical
  have inner (p : V×V) (hp : p∈S.offDiag) : ((S.erase p.1).erase p.2).offDiag.card ≤ 2 := by
    obtain ⟨ha,hb,hn⟩ := Finset.mem_offDiag.mp hp
    have hb' : p.2∈S.erase p.1 := Finset.mem_erase.mpr ⟨Ne.symm hn,hb⟩
    rw [Finset.offDiag_card,Finset.card_erase_of_mem hb',Finset.card_erase_of_mem ha]
    have hs : S.card=0 ∨ S.card=1 ∨ S.card=2 ∨ S.card=3 ∨ S.card=4 := by omega
    rcases hs with h|h|h|h|h <;> rw [h] <;> decide
  have outer : S.offDiag.card ≤12 := by
    rw [Finset.offDiag_card]
    have hs : S.card=0 ∨ S.card=1 ∨ S.card=2 ∨ S.card=3 ∨ S.card=4 := by omega
    rcases hs with h|h|h|h|h <;> rw [h] <;> decide
  calc
    _ = ∑ p ∈ S.offDiag, ((S.erase p.1).erase p.2).offDiag.card := Finset.card_sigma _ _
    _ ≤ ∑ _p ∈ S.offDiag, 2 := Finset.sum_le_sum inner
    _ ≤ 24 := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using
        (Nat.mul_le_mul_right 2 outer)

theorem ordered_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (labels : Finset I) (ends : I → Finset V) (actual : Finset (Finset I))
    (binary : ∀ i∈labels, (ends i).card≤2)
    (realize : ∀ x a, G.Adj x a → ∃ i∈labels, ends i={x,a})
    (unique : ∀ p∈actual, ∀ q∈actual, p⊆labels → q⊆labels → support ends p=support ends q → p=q) :
    ThresholdC4.ordered G ≤ 24*(missing labels actual).card := by
  classical
  have incl : ThresholdC4.tuples G ⊆ (missing labels actual).biUnion (fun p => presentations (support ends p)) := by
    rintro ⟨⟨x,y⟩,a,b⟩ ht
    obtain ⟨xy,ab,xa,ya,xb,yb⟩ := (ThresholdC4.mem_tuples G x y a b).mp ht
    have nx := xa.ne
    have ny := ya.ne
    have bx := xb.ne
    have by' := yb.ne
    obtain ⟨i,hi,ei⟩ := realize x a xa
    obtain ⟨j,hj,ej⟩ := realize y b yb
    obtain ⟨k,hk,ek⟩ := realize x b xb
    obtain ⟨l,hl,el⟩ := realize y a ya
    have ij : i≠j := by
      intro h
      have v : x∈ends j := h ▸ (by simp [ei] : x∈ends i)
      simpa [ej,xy,bx] using v
    have kl : k≠l := by
      intro h
      have v : x∈ends l := h ▸ (by simp [ek] : x∈ends k)
      simpa [el,xy,nx] using v
    have ik : i≠k := by
      intro h
      have v : a∈ends k := h ▸ (by simp [ei] : a∈ends i)
      simpa [ek,nx.symm,ab] using v
    have il : i≠l := by
      intro h
      have v : x∈ends l := h ▸ (by simp [ei] : x∈ends i)
      simpa [el,xy,nx] using v
    let S : Finset V := {x,y,a,b}
    have first : support ends {i,j}=S := by ext z; simp [support,ei,ej,S,or_assoc,or_left_comm,or_comm]
    have second : support ends {k,l}=S := by ext z; simp [support,ek,el,S,or_assoc,or_left_comm,or_comm]
    have pres : (⟨(x,y),(a,b)⟩ : Σ _ : V×V, V×V)∈presentations S := by
      simp [presentations,Finset.mem_offDiag,S,xy,ab,nx.symm,ny.symm,bx.symm,by'.symm]
    have two₁ : {i,j}∈labels.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj),by simp [ij]⟩
    have two₂ : {k,l}∈labels.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hk (Finset.singleton_subset_iff.mpr hl),by simp [kl]⟩
    by_cases seen : ({i,j} : Finset I)∈actual
    · have absent : ({k,l} : Finset I)∉actual := by
        intro also
        have eq := unique _ seen _ also (Finset.mem_powersetCard.mp two₁).1 (Finset.mem_powersetCard.mp two₂).1 (first.trans second.symm)
        have cnt : i∈({k,l} : Finset I) := eq ▸ (by simp : i∈({i,j} : Finset I))
        simpa [ik,il] using cnt
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_sdiff.mpr ⟨two₂,absent⟩,second.symm ▸ pres⟩
    · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_sdiff.mpr ⟨two₁,seen⟩,first.symm ▸ pres⟩
  calc
    _ ≤ _ := Finset.card_le_card incl
    _ ≤ ∑ p ∈ missing labels actual, (presentations (support ends p)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ missing labels actual, 24 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1
      apply card_presentations
      calc
        _ ≤ ∑ i ∈ p, (ends i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ p, 2 := Finset.sum_le_sum (fun i hi => binary i (sub hi))
        _ = 4 := by simp [card]
    _ = _ := by simp [Nat.mul_comm]
end ThresholdC4Missing
