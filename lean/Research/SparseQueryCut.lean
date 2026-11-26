import Research.LocalGateCut
import Research.SparseBoundary
import Research.UniqueStarCost

namespace SparseQueryCut
open CircuitRewire
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def profile (X : ℕ → Set (Finset V)) (j : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun l => ({l} : Finset V) ∈ X j)

omit [DecidableEq V] in
theorem mem_profile (X : ℕ → Set (Finset V)) (j : ℕ) (l : V) :
    l ∈ profile X j ↔ ({l} : Finset V) ∈ X j := by
  classical
  simp [profile]

noncomputable def slots (m s : ℕ) (X : ℕ → Set (Finset V)) (A : Finset V) :=
  (Finset.range s).filter (fun g => 2 ≤ (profile X (m+g)).card ∧ profile X (m+g) ⊆ A)

theorem per_query (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set (Finset V))
    (ho : o < m+s) (ordered : ∀ k<s, (raw k).left < m+k ∧ (raw k).right < m+k)
    (sem : ∀ k<s, X (m+k) = (raw k).eval X) (A H : Finset V) (r : ℕ)
    (card : H.card = r+1)
    (input : ∀ j<m, (profile X j).card ≤ 1 ∨ ¬ profile X j ⊆ A)
    (up : ∀ j<m+s, ∀ l : V, ∀ T : Finset V, l ∈ T → {l} ∈ X j → T ∈ X j)
    (pos : ∀ l ∈ H, ({l} : Finset V) ∈ X o)
    (neg : ∀ T : Finset V, T.card ≤ r → Disjoint T A → T ∉ X o) :
    r ≤ (slots m s X A).card := by
  classical
  by_contra! cheap
  let L := slots m s X A
  obtain ⟨S,cost,bound,cut⟩ := LocalGateCut.cut_ordered m s o raw X ho ordered sem L
  have boundary (j : ℕ) (hj : j ∈ S) : (profile X j).card ≤ 1 ∨ ¬ profile X j ⊆ A := by
    obtain ⟨lim,h⟩ := bound j hj
    by_cases before : j<m
    · exact input j before
    · have outside := h.resolve_left before
      by_contra! hc
      apply outside
      change j-m ∈ (Finset.range s).filter _
      apply Finset.mem_filter.mpr
      have e : m+(j-m)=j := by omega
      exact ⟨Finset.mem_range.mpr (by omega),by simpa [e] using (show 2 ≤ (profile X j).card ∧
        profile X j ⊆ A from ⟨by omega,hc.2⟩)⟩
  have width : S.card ≤ r := by change S.card ≤ (slots m s X A).card+1 at cost; omega
  obtain ⟨l,hl,T,small,dis,meet⟩ := SparseBoundary.dominate_subset r A H S (profile X) card width boundary
  apply neg T small dis (cut {l} T ?_ (pos l hl))
  intro j hj hit
  obtain ⟨w,hw,wire⟩ := meet j hj ((mem_profile X j l).mpr hit)
  exact up j (bound j hj).1 w T hw ((mem_profile X j w).mp wire)

theorem simultaneous {P : Type*} [Fintype P] (m s : ℕ) (out : P → ℕ) (raw : ℕ → Gate)
    (X : ℕ → Set (Finset V)) (ord : ∀ k<s, (raw k).left < m+k ∧ (raw k).right < m+k)
    (sem : ∀ k<s, X (m+k) = (raw k).eval X) (A : P → Finset V) (q : ℕ)
    (size : ∀ p, (A p).card=q+1) (over : ∀ p r, p≠r → (A p ∩ A r).card ≤ 1)
    (lim : ∀ p, out p < m+s) (input : ∀ p j, j<m → (profile X j).card ≤ 1 ∨ ¬ profile X j ⊆ A p)
    (up : ∀ j<m+s, ∀ l : V, ∀ T : Finset V, l ∈ T → {l} ∈ X j → T ∈ X j)
    (pos : ∀ p, ∀ l ∈ A p, ({l} : Finset V) ∈ X (out p))
    (neg : ∀ p, ∀ T : Finset V, T.card ≤ q → Disjoint T (A p) → T ∉ X (out p)) :
    Fintype.card P*q ≤ s := by
  apply UniqueStarCost.global_count A (fun g => profile X (m+g)) s q over
  intro p
  exact per_query m s (out p) raw X (lim p) ord sem (A p) (A p) q (size p) (input p) up (pos p) (neg p)

end SparseQueryCut
