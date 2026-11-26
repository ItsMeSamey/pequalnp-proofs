import ThresholdUpperActualSelection
import ThresholdNativeUpper
namespace ThresholdUpperFiniteAssembly
open ThresholdUpperCatalogue ThresholdUpperSecond ThresholdUpperActualSelection ThresholdUpperInjection
open ThresholdUpperOverlapTwo
theorem incident_count {V : Type*} [LinearOrder V] {U : Finset V} {R : Finset (Finset V)}
    (edges : R⊆edgeUniverse U) (c : V) :
    (incident R c).card≤(neighbors U R c).card := by
  classical
  have cover : incident R c⊆(neighbors U R c).image (fun d=>({c,d}:Finset V)) := by
    intro e he
    obtain ⟨live,hit⟩ := Finset.mem_filter.mp he
    obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp (edges live)
    obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp sz
    subst e
    rcases Finset.mem_insert.mp hit with rfl|hb
    · exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨ab.symm,sub (by simp)⟩,live⟩,rfl⟩
    · have cb := Finset.mem_singleton.mp hb
      subst c
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨ab,sub (by simp)⟩,by simpa [Finset.pair_comm] using live⟩,
        Finset.pair_comm _ _⟩
  exact (Finset.card_le_card cover).trans Finset.card_image_le

def Envelope (n v w z k : Nat) : Prop :=
  ∀ f : Nat, v.choose 2≤f+lossBudget w v/(sampleCount w v-starCost w v k) →
    f≤v.choose 2 →
    Fintype.card (Injection w z)*n+f*failCost w z+
      (3*f*(v+(k-1)^2-1))*pairCost w z 2+
      f.choose 2*max (pairCost w z 3) (pairCost w z 4) ≤ Fintype.card (Injection w z)*f

theorem cost {n v w z k : Nat} (four : 4≤v) (kf : k≤v)
    (room : starCost w v k<sampleCount w v) (fit : w≤Fintype.card (Edges z))
    (budget : Envelope n v w z k) :
    ThresholdPublicMinimum.minimum n≤2*n+v+w+16*z := by
  classical
  let U := (Finset.univ : Finset (Fin w))
  have sz : U.card=w := by simp [U]
  obtain ⟨G,lower⟩ := first_graph U v k four kf (by simpa [sz] using room)
  have fbound : G.F.card≤v.choose 2 := by
    have le := Fintype.card_le_of_injective G.representative G.representative.injective
    simpa only [Fintype.card_coe,Finset.card_powersetCard,G.edges] using le
  have ov := overlap_count G.ambient (show G.F⊆boxes U G.R by rw [G.family]) (k-1)
    (fun a ha => (incident_count G.ambient a).trans (by have h := G.degree a ha; omega))
  rw [G.edges] at ov
  have funds := budget G.F.card (by simpa [sz] using lower) fbound
  have h := second_layers (n:=n) G fit (by
    dsimp only
    rw [two_family]
    have rem := Finset.card_le_card
      (Finset.sdiff_subset (s := G.F.powersetCard 2) (t := overlapTwo G.F))
    rw [Finset.card_powersetCard] at rem
    exact (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ ov) _)
      (Nat.mul_le_mul_right _ rem)).trans funds)
  obtain ⟨v',hv,w',hw,z',hz,⟨L⟩⟩ := h
  exact (ThresholdThreeLayerUpper.public_upper L).trans (by omega)
end ThresholdUpperFiniteAssembly
