import DDSharedArms
import DDExternalOnly
import Q1DoubleAffected

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

private theorem and_before {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {g w : ℕ}
    (p : AndPath n C g w) : n+g ≤ w := by
  induction p with
  | source => exact le_rfl
  | step _ bound _ pin ih => exact ih.trans (Nat.le_of_lt (ao.2.1 _ bound _ pin))

theorem affected_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (double : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    ∃! t, t ∈ centreless G C ∧ MixerRoute n G C m m t := by
  have unique {i j k : ℕ} (mi : m ≤ i) (kind : i=m ∨ i∈junk G C)
      (hj : j∈readers n C i) (hk : k∈readers n C i) : j=k := by
    have bound : (readers n C i).card ≤ 1 := by
      rcases kind with rfl | hg
      · exact mixer_unique G C _ double edge least form
      · apply external_only_single_reader double _ edge least form hg
        intro w pin path
        have lo := and_before least.1 path
        have hi := least.1.2.1 m (mixer_info double).1 w pin
        omega
    by_contra ne
    have := Finset.one_lt_card.mpr ⟨j,hj,k,hk,ne⟩
    omega
  have walk {i t : ℕ} (p : MixerRoute n G C m i t) :
      m ≤ i → ∀ {s}, MixerRoute n G C m i s → t=s := by
    induction p with
    | stop term =>
      intro _ s q
      cases q with
      | stop => rfl
      | next hn _ _ => exact (hn term).elim
    | @next i j t nt edge1 rest ih =>
      intro mi s q
      cases q with
      | stop term => exact (nt term).elim
      | next _ edge2 tail =>
        have eq := unique mi edge1.1 edge1.2 edge2.2
        subst_vars
        obtain ⟨bound,pin⟩ := Finset.mem_filter.mp edge1.2
        have less := least.1.2.1 _ (Finset.mem_range.mp bound) _ pin
        exact ih (by omega) tail
  obtain ⟨t,ht,hp⟩ := affected_exists double edge least
  exact ⟨t,⟨ht,hp⟩,fun s hs => (walk hp le_rfl hs.2).symm⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
