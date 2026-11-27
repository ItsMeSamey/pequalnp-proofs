import Q1DoubleTriangleGeometry
import Q1DoubleStarPool
import Q1DoubleStarBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

variable {n a b w r s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {A : Fin a → Clause n} {B : Fin b → Clause n} {W : Fin w → Clause n}

def restrictBatch (P : Batch G C A W r) {h : ℕ} (idx : Fin h ↪ Fin r) : Batch G C A W h where
  pt := fun i => P.pt (idx i)
  edges := fun i => P.edges (idx i)
  res := fun i => P.res (idx i)
  sep := fun i j ne => P.sep _ _ (fun eq => ne (idx.injective eq))
  induced := fun i j ne => P.induced _ _ (fun eq => ne (idx.injective eq))
  hits := fun c i => P.hits c (idx i)
  clean := P.clean
  anchor := P.anchor

theorem pair_pool (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (hr : 0<r) (hs : 0<s) (v : Fin n)
    (inP : ∀ i k, G.Adj v (P.pt i k)) (inQ : ∀ i k, G.Adj v (Q.pt i k))
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l))) :
    2^r+2^s ≤ a+b+w := by
  classical
  let nA : Bool → ℕ | false => a | true => b
  let num : Bool → ℕ | false => r | true => s
  let left : ∀ i : Bool, Fin (nA i) → Clause n | false => A | true => B
  let bt : ∀ i : Bool, Batch G C (left i) W (num i) | false => P | true => Q
  let L := (Fin a ⊕ Fin b) ⊕ Fin w
  let phys : ∀ i : Bool, (Fin (nA i) ⊕ Fin w) → L
    | false,.inl j => .inl (.inl j)
    | true,.inl j => .inl (.inr j)
    | _,.inr j => .inr j
  let support : L → Clause n := Sum.elim (Sum.elim A B) W
  have h := Q1Double.weighted_batch_pool (L := L) four nA (fun _ => w) num left
    (fun _ => W) bt (by intro i; cases i <;> assumption) phys support (by
      intro i c
      cases i <;> cases c <;> rfl) v (by intro i; cases i <;> assumption) (by
      intro i j ne
      cases i <;> cases j
      · exact (ne rfl).elim
      · exact ex
      · exact fun i j k l => Ne.symm (ex j i l k)
      · exact (ne rfl).elim)
  simpa [L,num,Fintype.sum_bool,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem internal_pool (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (hr : 0<r) (v : Fin n) (inP : ∀ i k, G.Adj v (P.pt i k))
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (cross : Finset (Fin s)) (inside : ∀ j, j ∉ cross → ∀ k, G.Adj v (Q.pt j k)) :
    2^r + (if cross.card<s then 2^(s-cross.card) else 0) ≤ a+b+w := by
  classical
  let rest := Finset.univ \ cross
  have card : rest.card = s-cross.card := by
    simp [rest,Finset.card_sdiff_of_subset (Finset.subset_univ cross)]
  by_cases h : cross.card<s
  · let ix : Fin rest.card ↪ Fin s := rest.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
    have bound := pair_pool four P (restrictBatch Q ix) hr (by omega) v inP
      (fun i k => inside (ix i) (Finset.mem_sdiff.mp (rest.equivFin.symm i).property).2 k)
      (fun i j k l => ex i (ix j) k l)
    simpa [h,card] using bound
  · have h₀ := P.power
    simp [h]
    omega

theorem rich_pair_of_batches (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (rich : 3 ≤ r) (hw : 0<w) (padding : 0<b)
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (cost : ℕ) (minCost : ∀ S : Finset (Fin n), (∀ i, ∃ k, P.pt i k ∈ S) →
      (∀ j, ∃ k, Q.pt j k ∈ S) → cost ≤ S.card) :
    richPair (a+w) (b+w) w r s (r+s-cost) := by
  classical
  obtain ⟨v,inP,around⟩ := Q1Double.rich_batch_anchor P rich four
  let L := Fin a ⊕ Fin w
  let common : Finset L := Finset.univ.image (Sum.inr : Fin w → L)
  have commonCard : common.card = w := by
    simpa [common] using Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin w)))
      (Sum.inr_injective (α := Fin a) (β := Fin w))
  have nz : common.Nonempty := ⟨.inr ⟨0,hw⟩,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have commonHits (l : L) (hl : l ∈ common) (j : Fin s) :
      Q.pt j false ∈ literals A W l ∨ Q.pt j true ∈ literals A W l := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact Q.hits (.inr i) j
  have cnt : (a+w)+(b+w)-w = a+b+w := by omega
  by_cases big : 3≤s
  · have inQ := Q1Double.rich_shared_neighborhood Q big four (.inr ⟨0,hw⟩) v
        (fun z hz => (around (.inr ⟨0,hw⟩) z hz).1)
    exact Or.inl (by rw [cnt]; exact pair_pool four P Q (by omega) (by omega) v inP inQ ex)
  obtain ⟨side,near,all⟩ := orient_second v Q.pt common nz (literals A W)
    (fun l _ z hz => (around l z hz).1) commonHits
  let cross := Finset.univ.filter (fun j : Fin s => ¬ G.Adj v (Q.pt j (!(side j))))
  have full (j : Fin s) (hj : j ∈ cross) := all j ((Finset.mem_filter.mp hj).2)
  have clean (S : Finset (Fin n)) (hs : ∀ l : L, ∃ z ∈ literals A W l, z ∈ S) :=
    P.clean S (fun l => by obtain ⟨z,hz,hm⟩ := hs l; exact ⟨z,hm,hz⟩)
  have selected (t : Fin r → Bool) (i j : Fin r) : ¬ G.Adj (P.pt i (t i)) (P.pt j (t j)) := by
    by_cases eq : i=j
    · subst j; exact G.loopless.irrefl _
    · exact P.induced _ _ eq _ _
  by_cases onA : ∀ j ∈ cross, ∃ i k, P.pt i k = Q.pt j (side j)
  · obtain ⟨coords,bit,card,coordsIn,onCoords⟩ := crossing_coordinates G.Adj P.pt
        (fun j => Q.pt j (side j)) cross (fun i => P.edges i false)
        (fun h => h.symm) (fun {i j} eq => by
          by_contra ne; exact Q.sep i j ne _ _ eq)
        (fun i j ne => Q.induced i j ne _ _) onA
    let bad (l : L) (t : Fin r → Bool) := ∀ i, P.pt i (t i) ∉ literals A W l
    have one (l : L) (t u : Fin r → Bool) (ht : bad l t) (hu : bad l u) : t=u := by
      funext i
      have h1 := ht i
      have h2 := hu i
      have hit := P.hits l i
      cases et : t i <;> cases eu : u i <;> simp_all
    have pr := crossing_private_rows coords bit common bad P.reject one (by
      intro l hl t force miss
      obtain ⟨i,hi,eq⟩ := force
      obtain ⟨j,hj,hpoint⟩ := coordsIn i hi
      apply miss i
      rw [eq,hpoint]
      exact full j hj l hl)
    have pr' : 2^r-2^(r-cross.card) ≤ (a+w)-w := by simpa [L,card,commonCard] using pr
    let ptsB (j : Fin s) (k : Bool) := Q.pt j (if k then !(side j) else side j)
    obtain ⟨S,size,ha,hb⟩ := crossing_cover P.pt ptsB cross bit (fun j hj => by
      obtain ⟨i,_,hi⟩ := onCoords j hj
      exact ⟨i,hi⟩)
    have mc := minCost S ha (fun j => by
      obtain ⟨k,hk⟩ := hb j
      exact ⟨_,hk⟩)
    have le : cross.card ≤ s := by simpa using Finset.card_le_univ cross
    have pool := internal_pool four P Q (by omega) v inP ex cross (by
      intro j hj k
      have far : G.Adj v (Q.pt j (!(side j))) := by
        by_contra no; exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩)
      cases h : side j <;> cases k <;> first | exact h ▸ near j | simpa [h] using far)
    apply rich_by_crossings (e := cross.card) (by omega) le (by omega) pr'
    · rwa [cnt]
    · intro hs
      have h := P.power
      omega
  · push_neg at onA
    obtain ⟨j,hj,hout⟩ := onA
    have pr := outsider_private four v (Q.pt j (side j)) (near j) P.pt inP P.edges
      hout selected (literals A W) common (full j hj) P.hits clean
    apply Or.inr
    refine ⟨by omega,Or.inl ?_⟩
    simpa [L,commonCard] using pr

theorem single_of_batches (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (cost : ℕ) (minCost : ∀ S : Finset (Fin n), (∀ i, ∃ k, P.pt i k ∈ S) →
      (∀ j, ∃ k, Q.pt j k ∈ S) → cost ≤ S.card) : singleForce (a+w) r w s (r+s-cost) := by
  classical
  let shared := Finset.univ.image (Sum.inr : Fin w → Fin a ⊕ Fin w)
  have card : shared.card = w := by
    simpa [shared] using Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin w)))
      (Sum.inr_injective (α := Fin a) (β := Fin w))
  have h := singleForce_of_geometry four P.pt Q.pt
    (fun t i j eq => by by_contra ne; exact P.sep i j ne _ _ eq)
    (fun i j k l eq => by by_contra ne; exact Q.sep i j ne _ _ eq)
    (fun t i j => by
      by_cases eq : i=j
      · subst j; exact G.loopless.irrefl _
      · exact P.induced i j eq _ _)
    P.edges P.res (literals A W) shared P.anchor P.hits (by
      intro l hl i
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
      rcases Q.hits (.inr j) i with h | h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩) (fun S hs => P.clean S (fun l => by
        obtain ⟨z,hz,hm⟩ := hs l
        exact ⟨z,hm,hz⟩)) cost minCost
  simpa [card] using h

theorem pair_rule_of_batches (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (hw : 0<w) (ha : 0<a) (hb : 0<b)
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (cost : ℕ) (minCost : ∀ S : Finset (Fin n), (∀ i, ∃ k, P.pt i k ∈ S) →
      (∀ j, ∃ k, Q.pt j k ∈ S) → cost ≤ S.card) :
    pairRule (a+w) (b+w) w r s (r+s-cost) := by
  have rev (S : Finset (Fin n)) (hb : ∀ i, ∃ k, Q.pt i k ∈ S)
      (ha : ∀ j, ∃ k, P.pt j k ∈ S) := minCost S ha hb
  refine ⟨single_of_batches four P Q cost minCost,?_,?_⟩
  · simpa [Nat.add_comm] using single_of_batches four Q P cost rev
  · intro large
    split
    next h => exact rich_pair_of_batches four P Q (by omega) hw hb ex cost minCost
    next h =>
      simpa [Nat.add_comm] using rich_pair_of_batches four Q P (by omega) hw ha
        (fun i j k l => Ne.symm (ex j i l k)) cost rev

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
