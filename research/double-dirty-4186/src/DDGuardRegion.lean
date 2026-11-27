import DDRegionClauses
import DDMixerRoot
import Q1DoubleRouteUnique
import DDFactorAbsorption

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

private theorem distinct_pins (least : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    opnd C j 0 ≠ opnd C j 1 := by
  intro same
  obtain ⟨ops,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C least.1 j hj
  have ab : a=b := by simpa [opnd,pins] using same
  subst b
  have eq (x : Fin n → Bool) : W n C x a = W n C x (n+j) := by
    rcases ops with op | op
    · rw [W_and n C x j hj op a a pins ha ha]
      simp
    · rw [W_or n C x j hj op a a pins ha ha]
      simp
  obtain ⟨A,ok,agree,smaller⟩ := erase_alias C least.1 hj ha eq
  have min := least.2.2 A ok (funext fun x => (agree x).trans (congrFun least.2.1 x))
  omega

theorem route_and_path {m H : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (path : MixerRoute n G C m m H) : AndPath n C m (n+H) := by
  have extend {i t : ℕ} (p : MixerRoute n G C m i t) : m ≤ i →
      AndPath n C m (n+i) → AndPath n C m (n+t) := by
    induction p with
    | stop => exact fun _ h => h
    | next _ rd _ ih =>
      intro mi h
      obtain ⟨hr,pin⟩ := Finset.mem_filter.mp rd.2
      obtain ⟨lt,op⟩ := downstream_reader D ao mi rd.1 rd.2
      exact ih (mi.trans lt.le) (.step h (Finset.mem_range.mp hr) op pin)
  exact extend path le_rfl .source

theorem unique_mixer_pin {m H : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) :
    ∃! p, p ∈ leaves n C H ∧ opnd C p.1 p.2 = n+m := by
  obtain ⟨_,route⟩ := influenced_top_route D edge least form ht affected
  have path := route_and_path D least.1 route
  have neq : n+H ≠ n+m := by
    intro eq
    have hm : H=m := by omega
    subst H
    exact (mixer_info D).2.2 (Finset.mem_filter.mp ht).2.2
  obtain ⟨k,hk,op,pin,tail⟩ := (first_and_reader path).resolve_left neq
  have kr : k ∈ andRegion n C H := in_region.mpr ⟨hk,op,tail⟩
  have exist : ∃ b : Fin 2, opnd C k b = n+m := by
    rcases Q0.reader_pin least.1 hk pin with e | e
    · exact ⟨0,e⟩
    · exact ⟨1,e⟩
  obtain ⟨b,eq⟩ := exist
  have leaf : (k,b) ∈ leaves n C H := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_product.mpr ⟨kr,Finset.mem_univ _⟩,?_⟩
    intro internalPin
    obtain ⟨j,mem,e⟩ := (Finset.mem_filter.mp internalPin).2
    change opnd C k b = n+j at e
    have same : j=m := by omega
    subst j
    exact GateOp.noConfusion ((in_region.mp mem).2.1.symm.trans (mixer_info D).2.1)
  refine ⟨(k,b),⟨leaf,eq⟩,?_⟩
  rintro ⟨j,c⟩ ⟨other,same⟩
  obtain ⟨reg,pin'⟩ := region_pin_mem least.1 other
  change opnd C j c = n+m at same
  change opnd C j c ∈ (gateAt C j).inputs at pin'
  have jread : j ∈ readers n C m := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (in_region.mp reg).1,same ▸ pin'⟩
  have kread : k ∈ readers n C m := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,pin⟩
  have jk := Finset.card_le_one.mp (mixer_unique G C m D edge least form) j jread k kread
  subst j
  have opEq := same.trans eq.symm
  have diff := distinct_pins least hk
  fin_cases c <;> fin_cases b <;> simp_all

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
