import Q1DoubleTriangleRegion
import Q1DoubleCoalesced
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

noncomputable def exteriorOn (s : OriginalCut G C) (g : ℕ) :=
  ((centreless G C).erase s.top).filter (fun t => g ∈ interior n C t)

def ArmSingle (s : OriginalCut G C) (a : ℕ) : Prop :=
  ∀ g ∈ andRegion n C a, (s.exteriorOn g).card ≤ 1

/-- Project a split-root cap onto actual external top labels. No uniqueness
of branch representatives for a given pair of labels is needed. -/
theorem armSingle_of_reaches (s : OriginalCut G C) (a : ℕ) (side : Fin 2)
    (reaches : ℕ → Finset Virtual.Root)
    (small : ∀ g ∈ andRegion n C a, (reaches g).card ≤ 2)
    (arm : ∀ g ∈ andRegion n C a, Virtual.Root.arm side ∈ reaches g)
    (ext : ∀ g ∈ andRegion n C a, ∀ t ∈ s.exteriorOn g, Virtual.Root.ext t ∈ reaches g) :
    s.ArmSingle a := by
  classical
  intro g hg
  let E := (s.exteriorOn g).image Virtual.Root.ext
  have ne : Virtual.Root.arm side ∉ E := by simp [E]
  have sub : insert (Virtual.Root.arm side) E ⊆ reaches g := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl|h
    · exact arm _ hg
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      exact ext _ hg _ ht
  have inject : Function.Injective Virtual.Root.ext := fun _ _ eq => by injection eq
  have le := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem ne,show E.card=(s.exteriorOn g).card from
    Finset.card_image_of_injective _ inject] at le
  have := small g hg
  omega

/-- Disjoint external dirty regions follow from one-sided incidence, plus
single-reader determinism for a dirty gate external to both arms. -/
theorem star_ext_disjoint (s : OriginalCut G C) {a b : ℕ}
    (sides : (a=s.left ∧ b=s.right) ∨ (a=s.right ∧ b=s.left))
    (one : s.ArmSingle a) (emptyB : externalLabels G C s.top b=∅)
    {i j : ℕ} (hi : i∈(centreless G C).erase s.top)
    (hj : j∈(centreless G C).erase s.top) (ne : i≠j) :
    Disjoint (interior n C i) (interior n C j) := by
  classical
  have ti := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).1
  have tj := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1
  apply exteriorDisjoint s.double s.edge s.least s.form ti tj ne
  intro g gi gj w hw reach
  have info := in_region.mp (Finset.mem_of_mem_erase gi)
  have nopA (eq : w=n+a) : False := by
    have ja := in_region.mpr ⟨info.1,info.2.1,eq ▸ reach⟩
    have ii : i∈s.exteriorOn g := Finset.mem_filter.mpr ⟨hi,gi⟩
    have jj : j∈s.exteriorOn g := Finset.mem_filter.mpr ⟨hj,gj⟩
    exact ne (Finset.card_le_one.mp (one g ja) i ii j jj)
  have nopB (eq : w=n+b) : False := by
    have jb : g∈andRegion n C b := in_region.mpr ⟨info.1,info.2.1,eq ▸ reach⟩
    have label : i∈externalLabels G C s.top b :=
      Finset.mem_filter.mpr ⟨hi,fun dis => Finset.disjoint_left.mp dis jb gi⟩
    simpa [emptyB] using label
  rw [s.pins] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact hw.elim nopA nopB
  · exact hw.elim nopB nopA

theorem shared_leaf_balance (ao : IsAO2 n C) {a t g : ℕ} (ga : g∈andRegion n C a)
    (gt : g∈andRegion n C t) : 2≤((leaves n C a) ∩ (leaves n C t)).card := by
  have info := in_region.mp ga
  have two : 2≤(leaves n C g).card := by
    apply Triangle.two_boundary _ ⟨g,root_mem_region info.1 info.2.1⟩
    intro j hj b
    exact ao.2.1 _ (in_region.mp hj).1 _ (Triangle.opnd_mem_for_region ao (in_region.mp hj).1 b)
  exact two.trans (Finset.card_le_card (Finset.subset_inter (Triangle.leaf_subset ao ga) (Triangle.leaf_subset ao gt)))

theorem external_private_leaf (ao : IsAO2 n C) {a t : ℕ} (ja : a∈junk G C)
    (top : t∈tops G C) : ((leaves n C t) \ (leaves n C a)).Nonempty := by
  obtain ⟨ha,opA,bad⟩ := (S4183.junk_iff G C a).mp ja
  obtain ⟨hr,opT,below⟩ := Finset.mem_filter.mp top
  by_contra h
  apply bad
  intro x hx
  have sup : leaves n C t ⊆ leaves n C a := by
    intro p hp
    by_contra hpa
    exact h ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpa⟩⟩
  exact below x ((region_eval ao (Finset.mem_range.mp hr) opT x).mpr
    (fun p hp => (region_eval ao ha opA x).mp hx p (sup hp)))

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
