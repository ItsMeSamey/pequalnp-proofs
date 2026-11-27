import Q1PrivateCounts
import Q1PrivateRich
import Q1PrivateTight
import Q1PrivateCover

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Clause (n : ℕ) := Finset (Fin n)
def literals {a w n : ℕ} (A : Fin a → Clause n) (W : Fin w → Clause n) :
    Fin a ⊕ Fin w → Clause n := Sum.elim A W

/-- A projected clean conjunction, retaining literal occurrences with multiplicity. -/
structure Batch (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) {a w : ℕ}
    (A : Fin a → Clause n) (W : Fin w → Clause n) (r : ℕ) where
  pt : Fin r → Bool → Fin n
  edges : ∀ i k, G.Adj (pt i k) (pt i (!k))
  res : ∀ i k, s(pt i k, pt i (!k)) ∈ Ustar G C
  sep : ∀ i j, i ≠ j → ∀ x y, pt i x ≠ pt j y
  induced : ∀ i j, i ≠ j → ∀ x y, ¬ G.Adj (pt i x) (pt j y)
  hits : ∀ c i, pt i false ∈ literals A W c ∨ pt i true ∈ literals A W c
  clean : ∀ S : Finset (Fin n), (∀ c, ∃ v ∈ S, v ∈ literals A W c) →
    ∃ x ∈ S, ∃ y ∈ S, G.Adj x y
  anchor : ∀ c, ∀ x ∈ literals A W c, ∀ y ∈ literals A W c, x ≠ y →
    ∃ d, ∀ z ∈ literals A W c, G.Adj d z ∧ s(d,z) ∈ starEdges G C

namespace Batch

variable {a w r : ℕ} {A : Fin a → Clause n} {W : Fin w → Clause n}

theorem reject (P : Batch G C A W r) (t : Fin r → Bool) :
    ∃ c, ∀ i, P.pt i (t i) ∉ literals A W c := by
  classical
  by_contra! yes
  let S := Finset.univ.image (fun i => P.pt i (t i))
  obtain ⟨x,hx,y,hy,adj⟩ := P.clean S (by
    intro c
    obtain ⟨i,hi⟩ := yes c
    exact ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ i),hi⟩)
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  by_cases e : i=j
  · subst j; exact G.irrefl adj
  · exact P.induced i j e _ _ adj

theorem power (P : Batch G C A W r) : 2^r ≤ a+w := by
  simpa using Q0Transversal.pow_le_card P.pt (fun c v => v ∈ literals A W c) P.hits P.reject

theorem global_center (P : Batch G C A W 3) (four : NoFourCycle G) :
    ∃ d, ∀ i b, G.Adj d (P.pt i b) := by
  apply rich_center four P.pt (literals A W) P.sep P.hits P.reject
  intro c x hx y hy ne
  obtain ⟨d,hd⟩ := P.anchor c x hx y hy ne
  exact ⟨d,fun z hz => (hd _ hz).1⟩

theorem small_guard (P : Batch G C A W 2) (four : NoFourCycle G) (k : a+w=4) (c : Fin w) :
    ∃ u v, W c={u,v} := by
  classical
  let en : Fin 4 ≃ Fin a ⊕ Fin w := Fintype.equivOfCardEq (by simpa using k.symm)
  let ix : Bool → Fin 2 := fun b => if b then 1 else 0
  let p := fun i b => P.pt (ix i) b
  let L := fun d => literals A W (en d)
  have neq : ix false ≠ ix true := by decide
  have result := tight_clause four p L
    (fun d i => P.hits (en d) (ix i))
    (fun S h => P.clean S (fun d => by simpa [L] using h (en.symm d)))
    (fun x y => P.induced _ _ neq x y) (fun x y => P.sep _ _ neq x y)
    (fun i b => P.edges _ b) (fun i b => P.res _ b)
    (fun d => P.anchor (en d)) (en.symm (.inr c))
  simpa [L,literals] using result

end Batch
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
