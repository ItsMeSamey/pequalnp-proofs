import ShoreBankCover

namespace OnePerShore.Upper
open PEqualNP.Represents
open scoped BigOperators

/-- Nonuniversal row profiles are either disjoint or equal. -/
def BicliqueResidual {n m} (A : Pred n m) : Prop :=
  ∀ u w, (∃ j, A u j = false) → (∃ j,A w j = false) →
    (∃ j, j ∈ residualProfile A u ∧ j ∈ residualProfile A w) →
      residualProfile A u = residualProfile A w

def uRows {n m} (A : Pred n m) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j,A i j = true
def uCols {n m} (A : Pred n m) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∀ i,A i j = true
def activeRows {n m} (A : Pred n m) : Finset (Fin n) :=
  (nonminimumRows A) \ (uRows A)
def profiles {n m} (A : Pred n m) := (activeRows A).image (residualProfile A)
def owners {n m} (A : Pred n m) (c : Finset (Fin m)) :=
  (activeRows A).filter fun i => residualProfile A i = c

private theorem active_profile {n m} {A : Pred n m} {i} (h : i ∈ activeRows A) :
    (residualProfile A i).Nonempty := by
  obtain ⟨j,w,p,z⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,z⟩⟩

private theorem profile_origin {n m} {A : Pred n m} {c} (h : c ∈ profiles A) :
    ∃ i ∈ activeRows A, residualProfile A i = c := Finset.mem_image.mp h

private theorem active_cold {n m} {A : Pred n m} {u} (hu : u ∈ activeRows A) :
    ∃ j,A u j = false := by
  have h := (Finset.mem_sdiff.mp hu).2
  simpa [uRows] using h

private theorem classes_disjoint {n m} {A : Pred n m} (clean : BicliqueResidual A) :
    (↑(profiles A) : Set (Finset (Fin m))).PairwiseDisjoint id := by
  intro c hc d hd ne
  obtain ⟨i,hi,rfl⟩ := profile_origin hc
  obtain ⟨j,hj,rfl⟩ := profile_origin hd
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact ne (clean i j (active_cold hi) (active_cold hj) ⟨v,hv,hw⟩)

private theorem row_card {n m} {A : Pred n m} (zero : ∃ i j,A i j=false) :
    (uRows A).card + (activeRows A).card = (nonminimumRows A).card := by
  obtain ⟨i,j,h⟩ := zero
  have sub : uRows A ⊆ nonminimumRows A := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,i,(Finset.mem_filter.mp hu).2 j,h⟩
  simpa [activeRows,Nat.add_comm] using Finset.card_sdiff_add_card_eq_card sub

private theorem col_card {n m} {A : Pred n m} (zero : ∃ i j,A i j=false) :
    (uCols A).card + ((profiles A).biUnion id).card = (nonminimumCols A).card := by
  classical
  obtain ⟨r,z,rz⟩ := zero
  have eq : (profiles A).biUnion id = (nonminimumCols A) \ (uCols A) := by
    ext j
    constructor
    · intro h
      obtain ⟨c,hc,hj⟩ := Finset.mem_biUnion.mp h
      obtain ⟨i,hi,rfl⟩ := profile_origin hc
      obtain ⟨pos,w,neg⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨v,hv⟩ := active_cold hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,v,pos,hv⟩,
        fun hu => by simpa [neg] using (Finset.mem_filter.mp hu).2 w⟩
    · intro h
      obtain ⟨ic,nc⟩ := Finset.mem_sdiff.mp h
      obtain ⟨i,v,p,q⟩ := (Finset.mem_filter.mp ic).2
      have ex : ∃ w,A w j=false := by simpa [uCols] using nc
      obtain ⟨w,hw⟩ := ex
      have ia : i ∈ activeRows A := Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,w,p,hw⟩,
          fun hu => by simpa [q] using (Finset.mem_filter.mp hu).2 v⟩
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ ia,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,hw⟩⟩
  rw [eq]
  have sub : uCols A ⊆ nonminimumCols A := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,z,(Finset.mem_filter.mp hj).2 r,rz⟩
  simpa [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card sub

private def PartialBuilt {n m} (A : Pred n m) (k : ℕ) : Prop :=
  (k=0 ∧ A=fun _ _ => false) ∨ Built A k

private theorem partial_or {n m a b} {A B : Pred n m} (ha : PartialBuilt A a)
    (hb : PartialBuilt B b) : PartialBuilt (fun u v => A u v || B u v) (a+b) := by
  rcases ha with ⟨rfl,rfl⟩ | ha
  · simpa using hb
  rcases hb with ⟨rfl,rfl⟩ | hb
  · apply Or.inr; simpa using ha
  exact Or.inr (ha.or hb)

private theorem partial_any {n m} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Pred n m) (k : ι → ℕ) (h : ∀ i∈s,Built (f i) (k i)) :
    PartialBuilt (anyOn s f) (∑ i∈s,k i) := by
  classical
  by_cases hs : s.Nonempty
  · exact Or.inr (built_any s f k hs h)
  · have := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact Or.inl ⟨by simp,by funext u v; simp [anyOn]⟩

private def boxPred {n m} (A : Pred n m) (c : Finset (Fin m)) : Pred n m :=
  fun u v => decide (u ∈ owners A c ∧ v∈c)

private theorem cover_spec {n m} (A : Pred n m) (u : Fin n) (v : Fin m) :
    A u v=true ↔ u∈uRows A ∨ v∈uCols A ∨ ∃ c∈profiles A,u∈owners A c ∧ v∈c := by
  constructor
  · intro p
    by_cases hr : u∈uRows A
    · exact Or.inl hr
    by_cases hc : v∈uCols A
    · exact Or.inr (Or.inl hc)
    have ex : ∃ w,A w v=false := by simpa [uCols] using hc
    obtain ⟨w,hw⟩ := ex
    have ia : u∈activeRows A := Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,w,p,hw⟩,hr⟩
    exact Or.inr (Or.inr ⟨_,Finset.mem_image_of_mem _ ia,Finset.mem_filter.mpr ⟨ia,rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,hw⟩⟩)
  · rintro (hu | hv | ⟨c,_,hu,hv⟩)
    · exact (Finset.mem_filter.mp hu).2 v
    · exact (Finset.mem_filter.mp hv).2 u
    · have e : residualProfile A u=c := (Finset.mem_filter.mp hu).2
      rw [←e] at hv
      exact (Finset.mem_filter.mp hv).2.1

theorem physical_of_biclique_residual {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) (clean : BicliqueResidual A) :
    RepSizeAtMost A (charged A - 1) := by
  classical
  let r : Fin n → Pred n m := fun i u _ => decide (u=i)
  let c : Fin m → Pred n m := fun j _ v => decide (v=j)
  let w := fun s : Finset (Fin m) => (owners A s).card+s.card
  have ar := partial_any (uRows A) r (fun _ => 1) (fun i _ => rowBuilt i)
  have ac := partial_any (uCols A) c (fun _ => 1) (fun j _ => colBuilt j)
  have ab := partial_any (profiles A) (boxPred A) w (by
    intro s hs
    obtain ⟨i,hi,rfl⟩ := profile_origin hs
    exact rectBuilt _ _ ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩ (active_profile hi))
  have whole := partial_or ar (partial_or ac ab)
  have eq : (fun u v => anyOn (uRows A) r u v ||
      (anyOn (uCols A) c u v || anyOn (profiles A) (boxPred A) u v)) = A := by
    funext u v; apply Bool.eq_iff_iff.mpr
    simpa [anyOn,r,c,boxPred] using (cover_spec A u v).symm
  have fiber : (∑ s ∈ profiles A, (owners A s).card) = (activeRows A).card := by
    unfold owners
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_true_of_mem (fun i hi => Finset.mem_image_of_mem _ hi)
  have cols := Finset.card_biUnion (classes_disjoint clean)
  have cost : (∑ _ ∈ uRows A, 1) + ((∑ _ ∈ uCols A, 1) + ∑ s ∈ profiles A,w s) = charged A := by
    simp only [w,Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,mul_one,fiber]
    change (uRows A).card + ((uCols A).card + ((activeRows A).card + ∑ s ∈ profiles A,s.card)) =
      (nonminimumRows A).card + (nonminimumCols A).card
    change ((profiles A).biUnion id).card = ∑ s ∈ profiles A,s.card at cols
    have := row_card zero; have := col_card zero; omega
  rw [eq,cost] at whole
  rcases whole with ⟨_,eq⟩ | b
  · obtain ⟨u,v,h⟩ := pos
    simp [eq] at h
  · exact b.realize

theorem exact_floor_iff {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) :
    RepSizeAtMost A (charged A - 1) ↔ BicliqueResidual A := by
  constructor
  · intro h
    by_cases hp : 0 < charged A
    · exact residual_profiles_at_floor h hp
    · intro u w hu hw hv
      obtain ⟨v,hv,_⟩ := hv
      obtain ⟨p,i,neg⟩ := (Finset.mem_filter.mp hv).2
      have row : u ∈ nonminimumRows A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,i,p,neg⟩
      have := Finset.card_pos.mpr ⟨_,row⟩
      unfold charged at hp
      omega
  · exact physical_of_biclique_residual A pos zero

/-- The constructed upper bound attains the exact gate count, including zero. -/
theorem exact_circuit_of_biclique_residual {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) (clean : BicliqueResidual A) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      C.size = charged A - 1 ∧ Represents A C := by
  obtain ⟨C,legal,size,rep⟩ := physical_of_biclique_residual A pos zero clean
  have low := physical_size_floor (A:=A) (s:=C.size) ⟨C,legal,le_rfl,rep⟩
  exact ⟨C,legal,Nat.le_antisymm size low,rep⟩

end OnePerShore.Upper
