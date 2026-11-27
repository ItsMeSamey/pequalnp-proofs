import Q1DoubleTriangleRules
import Q1DoubleWeighted

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem unique_slot_exact {n r : ℕ} {Slot : Type*}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (hr : 2 ≤ r) (pos mate : Fin r → Fin n)
    (inj : Function.Injective mate) (indep : ∀ i j, ¬ G.Adj (pos i) (pos j))
    (edge : ∀ i, G.Adj (pos i) (mate i))
    (res : ∀ i, s(pos i,mate i) ∈ Ustar G C)
    (clause : Slot → Finset (Fin n)) (u : Slot)
    (anchor : ∀ p ∈ clause u, ∀ q ∈ clause u, p ≠ q →
      ∃ c, ∀ z ∈ clause u, G.Adj c z ∧ s(c,z) ∈ starEdges G C)
    (hits : ∀ i, pos i ∈ clause u ∨ mate i ∈ clause u)
    (miss : ∀ i, pos i ∉ clause u)
    (other : ∀ v, v ≠ u → ∃ i, pos i ∈ clause v)
    (clean : ∀ S : Finset (Fin n), (∀ v, ∃ z ∈ clause v, z ∈ S) →
      ∃ a ∈ S, ∃ b ∈ S, G.Adj a b) :
    clause u = Finset.univ.image mate := by
  classical
  have hm i := (hits i).resolve_left (miss i)
  let i₀ : Fin r := ⟨0, by omega⟩
  let i₁ : Fin r := ⟨1, by omega⟩
  have distinct : mate i₀ ≠ mate i₁ := by
    intro e
    have h := congrArg Fin.val (inj e)
    change 0 = 1 at h
    omega
  obtain ⟨c,hc⟩ := anchor _ (hm i₀) _ (hm i₁) distinct
  apply Finset.Subset.antisymm
  · intro z hz
    by_contra outside
    have hzNe (i : Fin r) : mate i ≠ z := by
      intro e
      exact outside (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e⟩)
    let S := insert z (Finset.univ.image pos)
    have active : ∀ v, ∃ a ∈ clause v, a ∈ S := by
      intro v
      by_cases e : v = u
      · subst v
        exact ⟨z,hz,Finset.mem_insert_self _ _⟩
      · obtain ⟨i,hi⟩ := other v e
        exact ⟨_,hi,Finset.mem_insert_of_mem (Finset.mem_image_of_mem pos (Finset.mem_univ i))⟩
    obtain ⟨a,ha,b,hb,hab⟩ := clean S active
    have adj : ∃ i, G.Adj (pos i) z := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (G.irrefl hab).elim
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
          exact ⟨i,hab.symm⟩
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ⟨i,hab⟩
        · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
          exact (indep i j hab).elim
    obtain ⟨i,hi⟩ := adj
    have he : c = pos i := by
      by_contra ne
      apply hzNe i
      apply Finset.card_le_one.mp (four c (pos i) ne) (mate i) _ z _
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hc _ (hm i)).1,edge i⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hc _ hz).1,hi⟩
    exact (Finset.mem_sdiff.mp (res i)).2 (he ▸ (hc _ (hm i)).2)
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact hm i

theorem common_exact_saving {V : Type*} [DecidableEq V] {r s : ℕ}
    (mate : Fin r → V) (ep : Fin s → Bool → V)
    (disjoint : ∀ i j k l, ep i k = ep j l → i = j)
    (hits : ∀ i, ∃ k, ep i k ∈ Finset.univ.image mate) :
    s ≤ r ∧ ∃ S : Finset V, S.card ≤ r ∧ (∀ i, mate i ∈ S) ∧ ∀ i, ∃ k, ep i k ∈ S := by
  classical
  choose bit hbit using hits
  have pre i : ∃ j, mate j = ep i (bit i) := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hbit i)
    exact ⟨j,hj⟩
  choose idx hidx using pre
  have inj : Function.Injective idx := by
    intro i j e
    exact disjoint i j _ _ ((hidx i).symm.trans ((congrArg mate e).trans (hidx j)))
  exact ⟨by simpa using Fintype.card_le_of_injective idx inj,
    Finset.univ.image mate, by simpa using (Finset.card_image_le (f := mate) (s := Finset.univ)),
    fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i), fun i => ⟨bit i,hbit i⟩⟩

/-- At most twice the number of surplus occurrences can fail to uniquely
reject an endpoint transversal. This includes occurrences rejecting no row. -/
theorem nonunique_slots {R L : Type*} [Fintype R] [Fintype L]
    (reject : L → R → Prop) (allRows : ∀ r, ∃ l, reject l r)
    (oneRow : ∀ l r s, reject l r → reject l s → r = s) :
    ∃ bad : Finset L, bad.card ≤ 2*(Fintype.card L-Fintype.card R) ∧
      ∀ l, l ∉ bad → ∃ r, reject l r ∧ ∀ z, reject z r → z = l := by
  classical
  choose rep repMiss using allRows
  have inj : Function.Injective rep := fun {r s} eq =>
    oneRow (rep r) r s (repMiss r) (eq ▸ repMiss s)
  let used : Finset L := Finset.univ.image rep
  let extra := Finset.univ \ used
  let badRows := Finset.univ.filter (fun r => ∃ l ∈ extra, reject l r)
  have usedCard : used.card = Fintype.card R := by
    simpa [used] using Finset.card_image_of_injective (s := (Finset.univ : Finset R)) inj
  have extraCard : extra.card = Fintype.card L - Fintype.card R := by
    simp [extra,Finset.card_sdiff_of_subset (Finset.subset_univ used),usedCard]
  have pick (r : ↥badRows) : ∃ l : ↥extra, reject l.val r.val := by
    obtain ⟨l,hl,hr⟩ := (Finset.mem_filter.mp r.property).2
    exact ⟨⟨l,hl⟩,hr⟩
  choose f hf using pick
  have fi : Function.Injective f := by
    intro r s eq
    exact Subtype.ext (oneRow _ _ _ (hf r) (eq ▸ hf s))
  have cardRows : badRows.card ≤ extra.card := by
    simpa using Fintype.card_le_of_injective f fi
  refine ⟨extra ∪ badRows.image rep, ?_, ?_⟩
  · have h₁ := Finset.card_union_le extra (badRows.image rep)
    have h₂ := Finset.card_image_le (s := badRows) (f := rep)
    omega
  · intro l hl
    have hUsed : l ∈ used := by
      by_contra out
      exact hl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,out⟩))
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hUsed
    refine ⟨r,repMiss r,?_⟩
    intro z hz
    by_cases hzu : z ∈ used
    · obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hzu
      exact congrArg rep (oneRow _ _ _ (repMiss s) hz)
    · have hze : z ∈ extra := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hzu⟩
      have hr : r ∈ badRows := Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hze,hz⟩
      exact False.elim (hl (Finset.mem_union_right _ (Finset.mem_image_of_mem rep hr)))

/-- If the row selects one distinguished crossing endpoint, every shared
slot is hit. Count such rows by bounding the complement through restriction
to the unrestricted coordinates. -/
theorem crossing_private_rows {r : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    (coords : Finset (Fin r)) (bit : Fin r → Bool) (shared : Finset L)
    (misses : L → (Fin r → Bool) → Prop)
    (reject : ∀ t, ∃ l, misses l t)
    (uniqueRow : ∀ l t u, misses l t → misses l u → t = u)
    (blocks : ∀ l ∈ shared, ∀ t, (∃ i ∈ coords, t i = bit i) → ¬ misses l t) :
    2^r - 2^(r-coords.card) ≤ Fintype.card L - shared.card := by
  classical
  let forced := Finset.univ.filter (fun t : Fin r → Bool => ∃ i ∈ coords, t i = bit i)
  let avoid := Finset.univ \ forced
  let remaining := Finset.univ \ coords
  let priv := Finset.univ \ shared
  have agrees (t : ↥avoid) (i : Fin r) (hi : i ∈ coords) : t.val i ≠ bit i := by
    intro eq
    exact (Finset.mem_sdiff.mp t.property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,eq⟩)
  let restrict (t : ↥avoid) (i : ↥remaining) : Bool := t.val i.val
  have inj : Function.Injective restrict := by
    intro t u h
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ coords
    · have ht := agrees t i hi
      have hu := agrees u i hi
      cases et : t.val i <;> cases eu : u.val i <;> cases eb : bit i <;> simp_all
    · exact congrFun h (⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩⟩ : ↥remaining)
  have cardR : remaining.card = r-coords.card := by
    simp [remaining,Finset.card_sdiff_of_subset (Finset.subset_univ coords)]
  have small : avoid.card ≤ 2^(r-coords.card) := by
    simpa [cardR] using Fintype.card_le_of_injective restrict inj
  have pick (t : ↥forced) : ∃ l : ↥priv, misses l.val t.val := by
    obtain ⟨l,hl⟩ := reject t.val
    have no : l ∉ shared := fun h => blocks l h t.val (Finset.mem_filter.mp t.property).2 hl
    exact ⟨⟨l,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,no⟩⟩,hl⟩
  choose f hf using pick
  have fi : Function.Injective f := by
    intro t u h
    exact Subtype.ext (uniqueRow _ _ _ (hf t) (h ▸ hf u))
  have pr : priv.card = Fintype.card L-shared.card := by
    simp [priv,Finset.card_sdiff_of_subset (Finset.subset_univ shared)]
  have hc : forced.card ≤ priv.card := by simpa using Fintype.card_le_of_injective f fi
  have total := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ forced)
  change avoid.card + forced.card = _ at total
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at total
  omega

/-- Inside the neighborhood of a vertex, every ambient edge is isolated
from every other ambient edge. -/
theorem neighborhood_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (four : NoFourCycle G) {p x y z : Fin n} (hx : G.Adj p x)
    (hy : G.Adj p y) (hz : G.Adj p z) (xy : G.Adj x y) (xz : G.Adj x z) : y = z := by
  apply Finset.card_le_one.mp (four p x (fun e => G.irrefl (e ▸ hx))) y _ z _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy,xy⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,xz⟩

/-- The internal endpoints of distinct crossing edges cannot use opposite
ends of a single rich edge, by inducedness of the second batch. Thus all
crossing endpoints can be selected simultaneously by one rich transversal. -/
theorem crossing_coordinates {V : Type*} {r s : ℕ} (adj : V → V → Prop)
    (A : Fin r → Bool → V) (near : Fin s → V) (cross : Finset (Fin s))
    (aEdge : ∀ i, adj (A i false) (A i true))
    (symm : ∀ {x y}, adj x y → adj y x)
    (bDisjoint : Function.Injective near)
    (bInduced : ∀ i j, i ≠ j → ¬ adj (near i) (near j))
    (onA : ∀ j ∈ cross, ∃ i k, A i k = near j) :
    ∃ coords : Finset (Fin r), ∃ bit : Fin r → Bool,
      coords.card = cross.card ∧
      (∀ i ∈ coords, ∃ j ∈ cross, A i (bit i) = near j) ∧
      (∀ j ∈ cross, ∃ i ∈ coords, A i (bit i) = near j) := by
  classical
  have pre (j : ↥cross) := onA j.val j.property
  choose idx side rep using pre
  have inj : Function.Injective idx := by
    intro i j eq
    by_contra neq
    have hn : i.val ≠ j.val := fun h => neq (Subtype.ext h)
    have hdiff : side i ≠ side j := by
      intro hs
      apply hn
      apply bDisjoint
      rw [← rep i,← rep j,eq,hs]
    have step : adj (A (idx i) (side i)) (A (idx j) (side j)) := by
      rw [eq]
      cases hi : side i <;> cases hj : side j
      · exact (hdiff (hi.trans hj.symm)).elim
      · exact aEdge _
      · exact symm (aEdge _)
      · exact (hdiff (hi.trans hj.symm)).elim
    rw [rep i,rep j] at step
    exact bInduced _ _ hn step
  let coords := Finset.univ.image idx
  let bit (i : Fin r) := if h : ∃ j, idx j = i then side h.choose else false
  have bitAt (j : ↥cross) : bit (idx j) = side j := by
    have ex : ∃ k, idx k = idx j := ⟨j,rfl⟩
    simp only [bit,dif_pos ex]
    exact congrArg side (inj ex.choose_spec)
  refine ⟨coords,bit,?_,?_,?_⟩
  · simpa [coords] using Finset.card_image_of_injective (s := (Finset.univ : Finset ↥cross)) inj
  · intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j.val,j.property,bitAt j ▸ rep j⟩
  · intro j hj
    let jj : ↥cross := ⟨j,hj⟩
    exact ⟨idx jj,Finset.mem_image_of_mem _ (Finset.mem_univ _),bitAt jj ▸ rep jj⟩

/-- Choose all crossing endpoints in the first batch and then one endpoint
of each remaining edge. This gives the claimed saving as an actual cover. -/
theorem crossing_cover {V : Type*} [DecidableEq V] {r s : ℕ}
    (A : Fin r → Bool → V) (B : Fin s → Bool → V) (cross : Finset (Fin s))
    (bit : Fin r → Bool) (sharedPoint : ∀ j ∈ cross, ∃ i, A i (bit i) = B j false) :
    ∃ S : Finset V, S.card ≤ r + (s-cross.card) ∧
      (∀ i, ∃ k, A i k ∈ S) ∧ ∀ j, ∃ k, B j k ∈ S := by
  classical
  let first := Finset.univ.image (fun i => A i (bit i))
  let other := Finset.univ \ cross
  let second := other.image (fun j => B j false)
  refine ⟨first ∪ second,?_,?_,?_⟩
  · have h := Finset.card_union_le first second
    have h1 : first.card ≤ r := by
      simpa [first] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := fun i => A i (bit i)))
    have h2 := Finset.card_image_le (s := other) (f := fun j => B j false)
    change second.card ≤ other.card at h2
    have h3 : other.card = s - cross.card := by
      simp [other, Finset.card_sdiff_of_subset (Finset.subset_univ cross)]
    omega
  · intro i
    exact ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  · intro j
    by_cases hj : j ∈ cross
    · obtain ⟨i,hi⟩ := sharedPoint j hj
      exact ⟨false,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)⟩
    · exact ⟨false,Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩))⟩

/-- A crossing endpoint outside the rich batch is isolated from every rich
endpoint within the center neighborhood. Adding it to every transversal
forces a different private rejecting occurrence for every row. -/
theorem outsider_private {n r : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (four : NoFourCycle G)
    (p z : Fin n) (pz : G.Adj p z) (A : Fin r → Bool → Fin n)
    (neigh : ∀ i k, G.Adj p (A i k)) (edges : ∀ i k, G.Adj (A i k) (A i (!k)))
    (outside : ∀ i k, A i k ≠ z)
    (indep : ∀ (t : Fin r → Bool) i j, ¬ G.Adj (A i (t i)) (A j (t j)))
    (clause : L → Finset (Fin n)) (shared : Finset L)
    (containsZ : ∀ l ∈ shared, z ∈ clause l)
    (hits : ∀ l i, A i false ∈ clause l ∨ A i true ∈ clause l)
    (clean : ∀ S : Finset (Fin n), (∀ l, ∃ v ∈ clause l, v ∈ S) →
      ∃ a ∈ S, ∃ b ∈ S, G.Adj a b) : 2^r ≤ Fintype.card L-shared.card := by
  classical
  let priv := Finset.univ \ shared
  have sep i k : ¬ G.Adj (A i k) z := fun h =>
    outside i (!k) (neighborhood_unique four (neigh i k) (neigh i (!k)) pz (edges i k) h)
  have pick (t : Fin r → Bool) : ∃ l : ↥priv, ∀ i, A i (t i) ∉ clause l := by
    let S := insert z (Finset.univ.image (fun i => A i (t i)))
    have no : ¬ ∀ l, ∃ v ∈ clause l, v ∈ S := by
      intro h
      obtain ⟨a,ha,b,hb,adj⟩ := clean S h
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact G.irrefl adj
        · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
          exact sep _ _ adj.symm
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact sep _ _ adj
        · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
          exact indep t i j adj
    push_neg at no
    obtain ⟨l,hl⟩ := no
    have hns : l ∉ shared := fun h => hl z (containsZ l h) (Finset.mem_insert_self _ _)
    refine ⟨⟨l,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hns⟩⟩,?_⟩
    intro i hi
    exact hl _ hi (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose f hf using pick
  have fi : Function.Injective f := by
    intro t u eq
    funext i
    have ht := hf t i
    have hu := hf u i
    rw [← eq] at hu
    have hit := hits (f t) i
    cases et : t i <;> cases eu : u i <;> simp_all
  have hh := Fintype.card_le_of_injective f fi
  simpa [priv,Finset.card_sdiff_of_subset (Finset.subset_univ shared)] using hh

/-- Apply the weighted pooling bound directly to graph edges in a common
neighborhood. Different batches use disjoint edges of the induced matching
on the neighborhood. Slot occurrences may belong to either or both roots. -/
theorem pool_neighborhood {n : ℕ} {L : Type*} [Fintype L]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (four : NoFourCycle G)
    (p : Fin n) (r : Bool → ℕ) (pos : ∀ b, Fin (r b) → Bool → Fin n)
    (nonempty : ∀ b, 0 < r b)
    (inner : ∀ b i k, G.Adj p (pos b i k))
    (edge : ∀ b i k, G.Adj (pos b i k) (pos b i (!k)))
    (apart : ∀ (t : ∀ b, Fin (r b) → Bool) b i c j,
      pos b i (!(t b i)) ≠ pos c j (t c j))
    (uses : L → Finset Bool) (clause : L → Finset (Fin n))
    (hits : ∀ l b, b ∈ uses l → ∀ i, pos b i false ∈ clause l ∨ pos b i true ∈ clause l)
    (clean : ∀ b (S : Finset (Fin n)), (∀ l, b ∈ uses l → ∃ v ∈ clause l, v ∈ S) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj x y) :
    2^(r false) + 2^(r true) ≤ Fintype.card L := by
  classical
  let X (b : Bool) := Fin (r b) → Bool
  let miss (l : L) (b : Bool) := Finset.univ.filter
    (fun t : X b => ∀ i, pos b i (t i) ∉ clause l)
  have unique (l : L) (b : Bool) (use : b ∈ uses l) : (miss l b).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    funext i
    have h1 := (Finset.mem_filter.mp ht).2 i
    have h2 := (Finset.mem_filter.mp hu).2 i
    have h3 := hits l b use i
    cases et : t i <;> cases eu : u i <;> simp_all
  have reject (t : ∀ b, X b) (b : Bool) :
      ∃ l, b ∈ uses l ∧ ∀ c ∈ uses l, t c ∈ miss l c := by
    let S := Finset.univ.filter (fun z : Fin n => ∃ c i, pos c i (t c i) = z)
    have no : ¬ ∀ l, b ∈ uses l → ∃ z ∈ clause l, z ∈ S := by
      intro active
      obtain ⟨u,hu,v,hv,adj⟩ := clean b S active
      obtain ⟨a,i,rfl⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨c,j,rfl⟩ := (Finset.mem_filter.mp hv).2
      exact apart t a i c j (neighborhood_unique four (inner _ _ _) (inner _ _ _)
        (inner _ _ _) (edge a i (t a i)) adj)
    push_neg at no
    obtain ⟨l,hl,empty⟩ := no
    refine ⟨l,hl,?_⟩
    intro c hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i hi
    exact empty _ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,i,rfl⟩)
  have positive (b : Bool) : 2 ≤ Fintype.card (X b) := by
    have h := nonempty b
    have hp : 2^1 ≤ 2^(r b) := Nat.pow_le_pow_right (by decide) h
    simpa [X] using hp
  have pooled := Q1Double.weighted_leaf_count X positive uses miss unique reject
  simpa [X,Fintype.sum_bool, Nat.add_comm] using pooled

/-- Orient the second batch at the rich neighborhood using any one common
slot. Every crossing edge's near endpoint belongs to every common slot. -/
theorem orient_second {n s : ℕ} {G : SimpleGraph (Fin n)} {L : Type*}
    (p : Fin n) (B : Fin s → Bool → Fin n) (shared : Finset L) (ex : shared.Nonempty)
    (clause : L → Finset (Fin n)) (inner : ∀ l ∈ shared, ∀ z ∈ clause l, G.Adj p z)
    (hit : ∀ l ∈ shared, ∀ j, B j false ∈ clause l ∨ B j true ∈ clause l) :
    ∃ b : Fin s → Bool, (∀ j, G.Adj p (B j (b j))) ∧
      ∀ j, ¬ G.Adj p (B j (!(b j))) → ∀ l ∈ shared, B j (b j) ∈ clause l := by
  classical
  obtain ⟨l₀,h₀⟩ := ex
  have pos (j : Fin s) : ∃ k, G.Adj p (B j k) := by
    rcases hit l₀ h₀ j with h | h
    · exact ⟨false,inner _ h₀ _ h⟩
    · exact ⟨true,inner _ h₀ _ h⟩
  choose b hb using pos
  refine ⟨b,hb,?_⟩
  intro j no l hl
  have h := hit l hl j
  cases eq : b j <;> simp [eq] at no ⊢ <;> rcases h with h | h
  · exact h
  · exact (no (inner _ hl _ h)).elim
  · exact (no (inner _ hl _ h)).elim
  · exact h

/-- Two rich centers coincide as soon as a common leaf meets two
vertex-disjoint first-batch edges. -/
theorem shared_centers {n r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (four : NoFourCycle G) (p q : Fin n) (S : Finset (Fin n)) (hr : 2 ≤ r)
    (A : Fin r → Bool → Fin n) (sep : ∀ i j, i ≠ j → ∀ k l, A i k ≠ A j l)
    (hit : ∀ i, ∃ k, A i k ∈ S)
    (one : ∀ z ∈ S, G.Adj p z) (two : ∀ z ∈ S, G.Adj q z) : p = q := by
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin r := ⟨1,by omega⟩
  have ne : i ≠ j := by intro h; have e := congrArg Fin.val h; change 0=1 at e; omega
  obtain ⟨k,hk⟩ := hit i
  obtain ⟨l,hl⟩ := hit j
  by_contra nq
  apply sep i j ne k l
  apply Finset.card_le_one.mp (four p q nq)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one _ hk,two _ hk⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one _ hl,two _ hl⟩

/-- Once the internal edges have been pooled, the crossing count selects
the corresponding explicit richPair alternative (including no crossings). -/
theorem rich_by_crossings {a b c r s e gain : ℕ}
    (little : s < 3) (ec : e ≤ s) (saving : e ≤ gain)
    (privateRows : 2^r-2^(r-e) ≤ a-c)
    (pooled : 2^r + (if e<s then 2^(s-e) else 0) ≤ a+b-c)
    (emptyPadding : s = 0 → 2^r+1 ≤ a+b-c) :
    richPair a b c r s gain := by
  by_cases he : e=0
  · subst e
    by_cases hs : s=0
    · subst s; exact Or.inl (by simpa using emptyPadding rfl)
    · exact Or.inl (by simpa [show 0<s by omega] using pooled)
  · have casesE : e=1 ∨ e=2 := by omega
    rcases casesE with rfl | rfl
    · exact Or.inr ⟨little,Or.inr (Or.inl ⟨ec,saving,privateRows,pooled⟩)⟩
    · exact Or.inr ⟨little,Or.inr (Or.inr ⟨ec,saving,privateRows,by
        simpa [show ¬ 2<s by omega] using pooled⟩)⟩

/-- A frequent shared block supplies a unique representative. Its omitted
endpoints give a real cover of both batches, bounding the minimum cover
cost and realizing the saving in singleForce. -/
theorem singleForce_of_geometry {n r s : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (A : Fin r → Bool → Fin n) (B : Fin s → Bool → Fin n)
    (aSeparates : ∀ (t : Fin r → Bool), Function.Injective (fun i => A i (t i)))
    (bSeparates : ∀ i j k l, B i k = B j l → i = j)
    (indep : ∀ (t : Fin r → Bool) i j, ¬ G.Adj (A i (t i)) (A j (t j)))
    (edge : ∀ i k, G.Adj (A i k) (A i (!k)))
    (res : ∀ i k, s(A i k,A i (!k)) ∈ Ustar G C)
    (clause : L → Finset (Fin n)) (shared : Finset L)
    (anchor : ∀ l p, p ∈ clause l → ∀ q ∈ clause l, p ≠ q →
      ∃ c, ∀ z ∈ clause l, G.Adj c z ∧ s(c,z) ∈ starEdges G C)
    (hits : ∀ l i, A i false ∈ clause l ∨ A i true ∈ clause l)
    (hitB : ∀ l ∈ shared, ∀ i, ∃ k, B i k ∈ clause l)
    (clean : ∀ S : Finset (Fin n), (∀ l, ∃ v ∈ clause l, v ∈ S) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj x y)
    (cost : ℕ) (minimum : ∀ S : Finset (Fin n), (∀ i, ∃ k, A i k ∈ S) →
      (∀ i, ∃ k, B i k ∈ S) → cost ≤ S.card) :
    singleForce (Fintype.card L) r shared.card s (r+s-cost) := by
  classical
  intro hr freq
  let rej (l : L) (t : Fin r → Bool) := ∀ i, A i (t i) ∉ clause l
  have rejects (t : Fin r → Bool) : ∃ l, rej l t := by
    by_contra! neg
    have active : ∀ l, ∃ v ∈ clause l, v ∈ Finset.univ.image (fun i => A i (t i)) := by
      intro l
      have h := neg l
      simp only [rej,not_forall,not_not] at h
      obtain ⟨i,hi⟩ := h
      exact ⟨_,hi,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    obtain ⟨u,hu,v,hv,h⟩ := clean _ active
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact indep t i j h
  have one l t u (ht : rej l t) (hu : rej l u) : t = u := by
    funext i
    have h := hits l i
    have h1 := ht i
    have h2 := hu i
    cases et : t i <;> cases eu : u i <;> simp only [et,eu] at h1 h2 ⊢ <;> first | rfl | exact ((h.elim h1 h2).elim) | exact ((h.elim h2 h1).elim)
  obtain ⟨bad,hcap,good⟩ := nonunique_slots rej rejects one
  have cap : bad.card ≤ 2*(Fintype.card L-2^r) := by simpa using hcap
  obtain ⟨l,hl,ok⟩ : ∃ l ∈ shared, l ∉ bad := by
    by_contra! nope
    have := Finset.card_le_card (show shared ⊆ bad from nope)
    omega
  obtain ⟨t,miss,unique⟩ := good l ok
  let mate i := A i (!(t i))
  have exactSlot : clause l = Finset.univ.image mate := by
    apply unique_slot_exact four hr (fun i => A i (t i)) mate (aSeparates _) (indep t)
      (fun i => edge i _) (fun i => res i _) clause l (anchor l)
    · intro i
      have hi := hits l i
      cases e : t i <;> simpa [mate,e,or_comm] using hi
    · exact miss
    · intro u ne
      by_contra! hu
      exact ne (unique u hu)
    · exact clean
  obtain ⟨le,S,card,ha,hb⟩ := common_exact_saving mate B bSeparates (fun i => by
    rw [← exactSlot]
    exact hitB l hl i)
  have hcost := minimum S (fun i => ⟨!(t i),ha i⟩) hb
  exact ⟨le,by omega⟩

/-- Two points meeting both disjoint edges of a two-edge batch are both
endpoints of that batch. This turns the shared-clause hit condition into
the endpoint-containment hypothesis of shared_exact_corner. -/
theorem shared_points_are_endpoints {V : Type*} [DecidableEq V] (S : Finset V)
    (B : Bool → Bool → V) (card : S.card ≤ 2)
    (hits : ∀ i, ∃ k, B i k ∈ S)
    (apart : ∀ k l, B false k ≠ B true l) :
    ∀ z ∈ S, ∃ e : Endpoint, z = B e.1 e.2 := by
  classical
  obtain ⟨k,hk⟩ := hits false
  obtain ⟨l,hl⟩ := hits true
  let T : Finset V := {B false k,B true l}
  have sub : T ⊆ S := by
    intro z hz
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hk
    · exact hl
  have tc : T.card = 2 := by simp [T,apart k l]
  have eq := Finset.eq_of_subset_of_card_le sub (show S.card ≤ T.card by omega)
  intro z hz
  rw [← eq] at hz
  simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with hz | hz
  · exact ⟨(false,k),hz⟩
  · exact ⟨(true,l),hz⟩

/-- With as many occurrences as rejecting rows, the row-to-slot
representative map is a bijection; distinct occurrences have distinct
rows, and each is the unique rejecting occurrence for its own row. -/
theorem exact_at_capacity {R L : Type*} [Fintype R] [Fintype L]
    (reject : L → R → Prop) (allRows : ∀ r, ∃ l, reject l r)
    (oneRow : ∀ l r s, reject l r → reject l s → r = s)
    (cap : Fintype.card L = Fintype.card R) :
    ∃ f : L → R, Function.Injective f ∧ ∀ l, reject l (f l) ∧
      ∀ z, reject z (f l) → z = l := by
  classical
  obtain ⟨bad,bound,good⟩ := nonunique_slots reject allRows oneRow
  have zero : bad.card = 0 := by omega
  have empty := Finset.card_eq_zero.mp zero
  have pick l := good l (by simp [empty])
  choose f hit only using pick
  refine ⟨f,?_,fun l => ⟨hit l,only l⟩⟩
  intro i j eq
  exact only j i (eq ▸ hit i)

/-- Tight corner from actual shared occurrence supports. Two four-slot
rows yield distinct omitted transversals. Each shared two-point support
hits both neighbor edges, so both points belong to the neighbor matching. -/
theorem tight_shared_card {V L : Type*} [DecidableEq V] [DecidableEq L]
    (G : SimpleGraph V) (A B : Endpoint → V) (support : L → Finset V)
    (block : Finset L) (row : L → Bool → Bool) (unique : Function.Injective row)
    (exactLeaf : ∀ l ∈ block, support l =
      Finset.univ.image (fun i => A (i,row l i)))
    (hits : ∀ l ∈ block, ∀ i, ∃ k, B (i,k) ∈ support l)
    (aEdge : ∀ i, G.Adj (A (i,false)) (A (i,true)))
    (bApart : ∀ k l, B (false,k) ≠ B (true,l))
    (bInduced : ∀ v w, G.Adj (B v) (B w) → v.1 = w.1)
    (disjoint : ∀ i j k l, A (i,false) = B (j,k) → A (i,true) ≠ B (j,l)) :
    block.card < 2 := by
  classical
  suffices block.card ≤ 1 by omega
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra neq
  let slot (h : Bool) := if h then b else a
  have mem (h : Bool) : slot h ∈ block := by cases h <;> simp [slot,ha,hb]
  apply shared_exact_corner G.Adj A B (fun h => row (slot h))
    (fun eq => neq (unique eq)) aEdge bInduced disjoint
  intro h i
  let l := slot h
  have cap : (support l).card ≤ 2 := by
    rw [exactLeaf _ (mem h)]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun i => A (i,row l i)))
  have inside : A (i,row l i) ∈ support l := by
    rw [exactLeaf _ (mem h)]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  exact shared_points_are_endpoints (support l) (fun j k => B (j,k)) cap (hits _ (mem h))
    bApart _ inside

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
