import Q1DoubleTrianglePhysical

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux Q0.Factor S4183.S98

variable {n : ℕ} {C : Circuit}

theorem opnd_mem_for_region (ao : IsAO2 n C) {j : ℕ} (hj : j<C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  obtain ⟨_,a,d,ins,_,_⟩ := AO_of_IsAO2 n C ao j hj
  fin_cases b <;> simp [opnd,ins]

theorem subregion {r g : ℕ} (hg : g ∈ andRegion n C r) :
    andRegion n C g ⊆ andRegion n C r := by
  intro i hi
  obtain ⟨bound,op,path⟩ := in_region.mp hi
  exact in_region.mpr ⟨bound,op,extend_and_path path (in_region.mp hg).2.2⟩

theorem upstream_eq_region (ao : IsAO2 n C) {r g : ℕ} (hg : g ∈ andRegion n C r) :
    upstream n C (andRegion n C r) g = andRegion n C g := by
  classical
  let A := andRegion n C r
  let rel (i j : ℕ) := j ∈ A ∧ pinStep n C i j
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨ia,path⟩ := Finset.mem_filter.mp hi
    obtain ⟨bound,op,_⟩ := in_region.mp ia
    refine in_region.mpr ⟨bound,op,?_⟩
    change Relation.ReflTransGen rel i g at path
    clear hg hi
    induction path with
    | refl => exact .source
    | @tail j k _ step ih =>
      obtain ⟨ka,b,wire⟩ := step
      obtain ⟨kb,ko,_⟩ := in_region.mp ka
      exact .step ih kb ko (wire ▸ opnd_mem_for_region ao kb b)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨subregion hg hi,?_⟩
    have paths (d : ℕ) : ∀ j ∈ andRegion n C g, g+1-j = d → Relation.ReflTransGen rel j g := by
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro j mem hd
        rcases first_and_reader (in_region.mp mem).2.2 with eq | ⟨k,bk,op,pin,tail⟩
        · have jg : j=g := by omega
          subst j
          exact .refl
        · have km := in_region.mpr ⟨bk,op,tail⟩
          have lt := ao.2.1 k bk _ pin
          have le := region_wire_le ao km
          have kp := ih (g+1-k) (by omega) k km rfl
          have step : pinStep n C j k := by
            rcases Q0.reader_pin ao bk pin with h|h
            · exact ⟨0,h⟩
            · exact ⟨1,h⟩
          exact (Relation.ReflTransGen.single (show rel j k from ⟨subregion hg km,step⟩)).trans kp
    exact paths _ i hi rfl

/-- A real AND subcones's raw occurrence remains raw within any larger
AND region it is contained in. A wire from another gate in the larger
region would itself extend by one AND step into the subcone. -/
theorem leaf_subset (ao : IsAO2 n C) {g r : ℕ} (hg : g ∈ andRegion n C r) :
    leaves n C g ⊆ leaves n C r := by
  change occurrences n C (andRegion n C g) ⊆ occurrences n C (andRegion n C r)
  rw [← upstream_eq_region ao hg]
  exact upstream_occurrences C _ _

def incomingCuts (n : ℕ) (C : Circuit) (priv branches : Finset ℕ) : Finset Pin :=
  (occurrences n C priv).filter fun p => ∃ j ∈ branches, opnd C p.1 p.2 = n+j

/-- Removing child subcones from the external gate region turns exactly
the crossing input pins into cut pins. Expanding them recovers those
subcones' own physical leaves. -/
theorem external_partition (ao : IsAO2 n C) {a b t : ℕ}
    (ha : a ∈ andRegion n C t) (hb : b ∈ andRegion n C t) :
    let A := andRegion n C a
    let B := andRegion n C b
    let ext := andRegion n C t \ (A∪B)
    leaves n C t = leaves n C a ∪ leaves n C b ∪
      (occurrences n C ext \ incomingCuts n C ext (A∪B)) := by
  classical
  dsimp only
  let A := andRegion n C a
  let B := andRegion n C b
  let T := andRegion n C t
  let E := T \ (A∪B)
  have ea : E ⊆ T := Finset.sdiff_subset
  have ab : A∪B ⊆ T := Finset.union_subset (subregion ha) (subregion hb)
  ext p
  change p ∈ occurrences n C T ↔ p ∈ (occurrences n C A ∪ occurrences n C B ∪
      (occurrences n C E \ incomingCuts n C E (A∪B)))
  constructor
  · intro hp
    obtain ⟨pin,no⟩ := Finset.mem_sdiff.mp hp
    have owner := (Finset.mem_product.mp pin).1
    have smaller (J : Finset ℕ) (sub : J ⊆ T) (h : p.1 ∈ J) : p ∈ occurrences n C J := by
      have pj : p ∈ pins J := Finset.mem_product.mpr ⟨h,Finset.mem_univ _⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨pj,?_⟩
      intro internalPin
      obtain ⟨j,hj,w⟩ := (Finset.mem_filter.mp internalPin).2
      exact no (Finset.mem_filter.mpr ⟨pin,j,sub hj,w⟩)
    by_cases hA : p.1 ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (smaller A (subregion ha) hA))
    by_cases hB : p.1 ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (smaller B (subregion hb) hB))
    have pe : p.1 ∈ E := Finset.mem_sdiff.mpr ⟨owner,by simp [hA,hB]⟩
    apply Finset.mem_union_right _
    apply Finset.mem_sdiff.mpr
    refine ⟨smaller E ea pe,?_⟩
    intro cut
    obtain ⟨j,hj,wire⟩ := (Finset.mem_filter.mp cut).2
    exact no (Finset.mem_filter.mpr ⟨pin,j,ab hj,wire⟩)
  · intro h
    rcases Finset.mem_union.mp h with e | e
    · rcases Finset.mem_union.mp e with xa | xb
      · exact leaf_subset ao ha xa
      · exact leaf_subset ao hb xb
    · obtain ⟨boundary,uncut⟩ := Finset.mem_sdiff.mp e
      obtain ⟨pin,no⟩ := Finset.mem_sdiff.mp boundary
      have pt : p ∈ pins T := Finset.mem_product.mpr ⟨ea (Finset.mem_product.mp pin).1,Finset.mem_univ _⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨pt,?_⟩
      intro internalPin
      obtain ⟨j,hj,wire⟩ := (Finset.mem_filter.mp internalPin).2
      by_cases branch : j ∈ A∪B
      · exact uncut (Finset.mem_filter.mpr ⟨boundary,j,branch,wire⟩)
      · exact no (Finset.mem_filter.mpr ⟨pin,j,Finset.mem_sdiff.mpr ⟨hj,branch⟩,wire⟩)

theorem region_read_closed {r i j : ℕ} (ao : IsAO2 n C)
    (hj : j ∈ andRegion n C r) (hi : i < C.gates.length) (andI : (gateAt C i).op=.and)
    (b : Fin 2) (eq : opnd C j b=n+i) : i ∈ andRegion n C r := by
  obtain ⟨jb,jo,path⟩ := in_region.mp hj
  exact in_region.mpr ⟨hi,andI,extend_and_path
    (show AndPath n C i (n+j) from .step .source jb jo (eq ▸ opnd_mem_for_region ao jb b)) path⟩

theorem private_region_used (ao : IsAO2 n C) (a b t : ℕ) :
    let E := andRegion n C t \ (andRegion n C a ∪ andRegion n C b)
    ∀ j ∈ E.erase t, ∃ p ∈ pins E, opnd C p.1 p.2=n+j := by
  intro E j hj
  obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
  obtain ⟨jt,out⟩ := Finset.mem_sdiff.mp mem
  obtain ⟨p,hp,wire⟩ := region_used ao t _ (Finset.mem_erase.mpr ⟨ne,jt⟩)
  have jinfo := in_region.mp jt
  have own := (Finset.mem_product.mp hp).1
  have outside : p.1 ∉ andRegion n C a ∪ andRegion n C b := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact out (Finset.mem_union_left _ (region_read_closed ao h jinfo.1 jinfo.2.1 p.2 wire))
    · exact out (Finset.mem_union_right _ (region_read_closed ao h jinfo.1 jinfo.2.1 p.2 wire))
  exact ⟨p,Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨own,outside⟩,Finset.mem_univ _⟩,wire⟩

theorem two_external_cuts (ao : IsAO2 n C) {a b t : ℕ}
    (ha : a ∈ andRegion n C t) (hb : b ∈ andRegion n C t) (at' : a ≠ t) (bt : b ≠ t)
    (dis : Disjoint (andRegion n C a) (andRegion n C b)) :
    let AB := andRegion n C a ∪ andRegion n C b
    let E := andRegion n C t \ AB
    2 ≤ (incomingCuts n C E AB).card := by
  classical
  intro AB E
  have pick {i o : ℕ} (hi : i ∈ andRegion n C t) (it : i ≠ t)
      (apart : Disjoint (andRegion n C i) (andRegion n C o))
      (ab : AB = andRegion n C i ∪ andRegion n C o) :
      ∃ p ∈ incomingCuts n C E AB, opnd C p.1 p.2 = n+i := by
    have info := in_region.mp hi
    have root := root_mem_region (n:=n) info.1 info.2.1
    obtain ⟨p,hp,wire⟩ := region_used ao t i (Finset.mem_erase.mpr ⟨it,hi⟩)
    have own := (Finset.mem_product.mp hp).1
    have lt := ao.2.1 p.1 (in_region.mp own).1 _ (opnd_mem_for_region ao (in_region.mp own).1 p.2)
    have no : p.1 ∉ AB := by
      rw [ab]
      intro hp'
      rcases Finset.mem_union.mp hp' with hup | hother
      · have h := region_wire_le ao hup
        omega
      · exact Finset.disjoint_left.mp apart root (region_read_closed ao hother info.1 info.2.1 p.2 wire)
    have ePin : p ∈ pins E := Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨own,no⟩,Finset.mem_univ _⟩
    have iab : i ∈ AB := ab ▸ Finset.mem_union_left _ root
    have bound : p ∈ occurrences n C E := by
      apply Finset.mem_sdiff.mpr
      refine ⟨ePin,?_⟩
      intro inner
      obtain ⟨j,je,wj⟩ := (Finset.mem_filter.mp inner).2
      have ij : i=j := by omega
      exact (Finset.mem_sdiff.mp je).2 (ij ▸ iab)
    exact ⟨p,Finset.mem_filter.mpr ⟨bound,i,iab,wire⟩,wire⟩
  obtain ⟨u,hu,ua⟩ := pick ha at' dis rfl
  obtain ⟨v,hv,vb⟩ := pick hb bt dis.symm (Finset.union_comm _ _)
  have na : a ≠ b := by
    intro eq
    have aroot := root_mem_region (n:=n) (in_region.mp ha).1 (in_region.mp ha).2.1
    have broot := root_mem_region (n:=n) (in_region.mp hb).1 (in_region.mp hb).2.1
    exact Finset.disjoint_left.mp dis aroot (eq ▸ broot)
  have ne : u ≠ v := by
    rintro rfl
    exact na (by omega)
  have sub : ({u,v} : Finset Pin) ⊆ incomingCuts n C E AB := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption
  simpa [ne] using Finset.card_le_card sub

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
