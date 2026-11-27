import Q1DoublePrivatePhysical
import DDRegionResources
import Q0FromUnique
import DDGuardIsolation
import DDExternalOnly
import Q1DoublePhysicalLabels

-- Source Q1DoublePrivateLayout.lean at SHA-256 59738fbb782204f140f52730753070394c10b75bb044f6994304ca24bc373b47.
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem externalRegionCharge {m r : ℕ} (d : DoubleDirty G C m) (four : NoFourCycle G)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (top : r∈tops G C)
    (away : ¬Influence n C m (n+r)) (E : Finset (Sym2 (Fin n)))
    (res : E⊆Ustar G C) (acc : E⊆gammaE G C r) :
    2*E.card ≤ ((andRegion n C r).erase r).card+2 := by
  classical
  obtain ⟨hr,op,below⟩ := Finset.mem_filter.mp top
  have bound := Finset.mem_range.mp hr
  let L := leaves n C r
  let F := L.image (leafSupport n C)
  have plain := external_plain least.1 away
  have sem (x : Fin n → Bool) : gateVal n C r x=true ↔ ∀ K∈F, ∃ z∈K, x z=true := by
    rw [region_clause_semantics d least.1 form bound op plain]
    constructor
    · intro hits K hK
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
      exact hits p hp
    · intro hits p hp
      exact hits _ (Finset.mem_image_of_mem (leafSupport n C) hp)
  refine Q0.residual_local_charge E res ?_ four (region_clause_stars d four least L plain) below sem ?_
  · rintro e he a b rfl
    obtain ⟨_,u,v,same,active⟩ := Finset.mem_filter.mp (acc he)
    have sets : pairInput u v = pairInput a b := by
      rcases Sym2.eq_iff.mp same with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · funext w
        simp [pairInput,or_comm]
    rw [sets] at active
    intro K hk
    obtain ⟨z,hz,hit⟩ := (sem _).mp active K hk
    rcases (Q0ReaderDeps.S90.pairInput_true a b z).mp hit with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · have h1 : F.card≤L.card := Finset.card_image_le
    have h2 := region_occurrences_bound least.1 bound op
    have h3 := Finset.card_erase_add_one (root_mem_region (n:=n) bound op)
    change F.card ≤ ((andRegion n C r).erase r).card+2
    apply h1.trans
    change (leaves n C r).card ≤ ((andRegion n C r).erase r).card+2
    omega

noncomputable def privateFoot (n : ℕ) (C : Circuit) (a b H t : ℕ) : Finset ℕ := by
  classical
  exact if t=H then andRegion n C a ∪ andRegion n C b ∪ (andRegion n C H).erase H
    else (andRegion n C t).erase t

theorem completePrivateLayout {m a b H : ℕ} (d : DoubleDirty G C m)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (pinsM : (gateAt C m).inputs=[n+a,n+b]) (ja : a∈junk G C) (jb : b∈junk G C)
    (hH : H∈centreless G C) (aff : Influence n C m (n+H))
    (guardApart : Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C H).erase H))
    (separate : (centreless G C : Set ℕ).PairwiseDisjoint (privateFoot n C a b H)) :
    Positive G C := by
  classical
  obtain ⟨own,real,_,all,_⟩ := originalOwnership G C d least form
  have top (t) (h : t∈centreless G C) : t∈tops G C := (Finset.mem_filter.mp h).1
  have inside (t) (h : t∈centreless G C) :
      (andRegion n C t).erase t ⊆ junk G C := by
    obtain ⟨ht,op,_⟩ := Finset.mem_filter.mp (top t h)
    exact region_except_root_dirty least.1 form (Finset.mem_range.mp ht) op
  let A : Allocation G C := {
    components := centreless G C, pivot := H, dirty := privateFoot n C a b H,
    roots := fun i => {i}, edges := own,
    dirtySub := by
      intro t ht
      by_cases eq : t=H
      · subst t
        simpa [privateFoot] using Finset.union_subset
          (Finset.union_subset (dirty_region_sub least.1 form ja) (dirty_region_sub least.1 form jb)) (inside H ht)
      · simpa [privateFoot,eq] using inside t ht
    rootSub := by intro t ht; simpa using ht
    dirtyDisj := separate
    rootDisj := by intro i _ j _ ne; simpa using ne
    covers := all.symm.subset }
  obtain ⟨t,_,unique⟩ := unique_influenced_top d edge least form
  have same := unique H ⟨top H hH,aff⟩
  refine A.finishPhysicalPrivate d four edge least form pinsM ja jb (top H hH) aff hH ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨ne,ic⟩ := Finset.mem_erase.mp hi
    have away : ¬Influence n C m (n+i) := fun h => ne ((unique i ⟨top i ic,h⟩).trans same.symm)
    have pay := externalRegionCharge d four least form (top i ic) away (own i)
      (fun e h => (real i e h).1) (fun e h => (real i e h).2.2)
    apply A.localOfAmple
    simpa [A,privateFoot,ne] using pay
  · exact fun e he => (real H e he).1
  · exact fun e he => (real H e he).2.2
  · exact arm_regions_disjoint d edge least form (by simp [opnd,pinsM]) (by simp [opnd,pinsM])
  · exact guardApart
  · simp [A,privateFoot]
  · simp [A]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double

-- Source Q1DoublePrivateIsolation.lean at SHA-256 ceb8e1289d81f6e363401e11ba17c27dcbf1e39bb01869b247d7c8f1bb7266f4.
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- Two distinct clean tops cannot share a dirty gate in their AND regions if
every common dirty gate is outside both exceptional arms. -/
theorem exteriorDisjoint {m i j : ℕ} (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (ti : i∈tops G C) (tj : j∈tops G C) (ne : i≠j)
    (out : ∀ g∈(andRegion n C i).erase i, g∈(andRegion n C j).erase j → OutsideArms n C g m) :
    Disjoint ((andRegion n C i).erase i) ((andRegion n C j).erase j) := by
  classical
  have dirty {r : ℕ} (tr : r∈tops G C) : (andRegion n C r).erase r ⊆ junk G C := by
    obtain ⟨hr,op,_⟩ := Finset.mem_filter.mp tr
    exact region_except_root_dirty least.1 form (Finset.mem_range.mp hr) op
  have notDirty {r : ℕ} (tr : r∈tops G C) : r∉junk G C := fun h =>
    ((S4183.junk_iff G C r).mp h).2.2 (Finset.mem_filter.mp tr).2.2
  have descend (k) : ∀ g, C.size-g=k → g∈(andRegion n C i).erase i →
      g∈(andRegion n C j).erase j → False := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro g measure gi gj
      obtain ⟨ni,pi⟩ := Finset.mem_erase.mp gi
      obtain ⟨nj,pj⟩ := Finset.mem_erase.mp gj
      rcases first_and_reader (in_region.mp pi).2.2 with eq | ⟨a,ha,oa,ra,pa⟩
      · exact ni (by omega)
      rcases first_and_reader (in_region.mp pj).2.2 with eq | ⟨b,hb,ob,rb,pb⟩
      · exact nj (by omega)
      have one := external_only_single_reader d (out g gi gj) edge least form (dirty ti gi)
      have ea : a∈readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,ra⟩
      have eb : b∈readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb,rb⟩
      obtain rfl := Finset.card_le_one.mp one a ea b eb
      have ai : a∈andRegion n C i := in_region.mpr ⟨ha,oa,pa⟩
      have aj : a∈andRegion n C j := in_region.mpr ⟨ha,oa,pb⟩
      have erI : a≠i := by
        rintro rfl
        exact notDirty ti (dirty tj (Finset.mem_erase.mpr ⟨ne,aj⟩))
      have erJ : a≠j := by
        rintro rfl
        exact notDirty tj (dirty ti (Finset.mem_erase.mpr ⟨ne.symm,ai⟩))
      have grow := least.1.2.1 a ha _ ra
      have bound : a<C.size := ha
      exact ih (C.size-a) (by omega) a rfl (Finset.mem_erase.mpr ⟨erI,ai⟩) (Finset.mem_erase.mpr ⟨erJ,aj⟩)
  exact Finset.disjoint_left.mpr (fun g hi hj => descend _ g rfl hi hj)

theorem completeNoExternalLeak {m a b H : ℕ} (d : DoubleDirty G C m)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (pinsM : (gateAt C m).inputs=[n+a,n+b]) (ja : a∈junk G C) (jb : b∈junk G C)
    (hH : H∈centreless G C) (aff : Influence n C m (n+H))
    (noLeak : ∀ t∈centreless G C, t≠H →
      Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C t).erase t)) :
    Positive G C := by
  classical
  let A := andRegion n C a ∪ andRegion n C b
  let E := fun t => (andRegion n C t).erase t
  have guard := guard_arm_disjoint d edge least form (Finset.mem_filter.mp hH).1 aff pinsM
  have avoid (t) (ht : t∈centreless G C) : Disjoint A (E t) := by
    by_cases h : t=H
    · subst t; exact guard
    · exact noLeak t ht h
  have out {t g : ℕ} (ht : t∈centreless G C) (hg : g∈E t) : OutsideArms n C g m := by
    intro w hw path
    obtain ⟨bound,op,_⟩ := in_region.mp (Finset.mem_of_mem_erase hg)
    apply (fun h => Finset.disjoint_left.mp (avoid t ht) h hg)
    rw [pinsM] at hw
    rcases List.mem_cons.mp hw with rfl | rest
    · exact Finset.mem_union_left _ (in_region.mpr ⟨bound,op,path⟩)
    · obtain rfl := List.mem_singleton.mp rest
      exact Finset.mem_union_right _ (in_region.mpr ⟨bound,op,path⟩)
  have dis {i j : ℕ} (hi : i∈centreless G C) (hj : j∈centreless G C) (ne : i≠j) :
      Disjoint (E i) (E j) := exteriorDisjoint d edge least form
        (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 ne (fun _ h _ => out hi h)
  apply completePrivateLayout d four edge least form pinsM ja jb hH aff guard
  intro i hi j hj ne
  apply Finset.disjoint_left.mpr
  intro g gi gj
  by_cases ih : i=H
  · subst i
    have jh := ne.symm
    have mix : g∈A ∪ E H := by simpa [privateFoot,A,E] using gi
    have ext : g∈E j := by simpa [privateFoot,E,jh] using gj
    exact (Finset.mem_union.mp mix).elim
      (fun h => Finset.disjoint_left.mp (avoid j hj) h ext)
      (fun h => Finset.disjoint_left.mp (dis hi hj ne) h ext)
  · have ext : g∈E i := by simpa [privateFoot,E,ih] using gi
    by_cases jh : j=H
    · subst j
      have mix : g∈A ∪ E H := by simpa [privateFoot,A,E] using gj
      exact (Finset.mem_union.mp mix).elim
        (fun h => Finset.disjoint_left.mp (avoid i hi) h ext)
        (fun h => Finset.disjoint_left.mp (dis hi hj ne) ext h)
    · exact Finset.disjoint_left.mp (dis hi hj ne) ext (by simpa [privateFoot,E,jh] using gj)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double

-- Source Q1DoubleDispatch.lean at SHA-256 b7d2c2bfd80cddbc0b2466ba39a89017863a1353bb6ce4e4179e5931e3f3a6ea.
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem dispatchPhysical {H m a b : ℕ} (d : DoubleDirty G C m)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (pins : (gateAt C m).inputs=[n+a,n+b]) (ja : a∈junk G C) (jb : b∈junk G C)
    (hH : H∈centreless G C) (aff : Influence n C m (n+H))
    (shape : LeakShape (externalLabels G C H a) (externalLabels G C H b))
    (single : ∀ t, ((externalLabels G C H a={t} ∧ externalLabels G C H b=∅) ∨
      (externalLabels G C H b={t} ∧ externalLabels G C H a=∅)) → Positive G C)
    (star : ((2≤(externalLabels G C H a).card ∧ externalLabels G C H b=∅) ∨
      (2≤(externalLabels G C H b).card ∧ externalLabels G C H a=∅)) → Positive G C)
    (triangle : ∀ t, externalLabels G C H a={t} → externalLabels G C H b={t} → Positive G C) :
    Positive G C := by
  cases shape with
  | privateArms l r => exact completeNoExternalLeak d four edge least form pins ja jb hH aff (noLeakOfEmpty l r)
  | singleLeft t l r => exact single t (.inl ⟨l,r⟩)
  | singleRight t l r => exact single t (.inr ⟨r,l⟩)
  | manyLeft l r => exact star (.inl ⟨l,r⟩)
  | manyRight l r => exact star (.inr ⟨r,l⟩)
  | triangle t l r => exact triangle t l r

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
