import Research.CircuitRewire
import Research.FirstGate

namespace CircuitRewire

def fanout (s : ℕ) (raw : ℕ → Gate) (i : ℕ) :=
  ((Finset.range s).filter (uses raw i)).card

private theorem occurs (s : ℕ) (raw : ℕ → Gate) (i : ℕ) (hs : 0 < s)
    (hit : uses raw i 0) : 1 ≤ fanout s raw i :=
  Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs,hit⟩⟩

private theorem unique_use (s : ℕ) (raw : ℕ → Gate) (i : ℕ) (hs : 0 < s)
    (hit : uses raw i 0) (small : fanout s raw i ≤ 1)
    (k : ℕ) (hk : k < s) (later : k ≠ 0) : ¬ uses raw i k := by
  intro h
  exact later (Finset.card_le_one.mp small k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,h⟩)
    0 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs,hit⟩))

private theorem transfer {Z : Type*} {u v : Z} (op : Op) (A B : Set Z)
    (pa : u ∈ A → v ∈ A) (pb : u ∈ B → v ∈ B) :
    u ∈ op.eval A B → v ∈ op.eval A B := by
  cases op with
  | join => exact Or.imp pa pb
  | meet => exact fun h => ⟨pa h.1,pb h.2⟩
  | copy => exact pa
  | zero => exact id

theorem double_fanout {Z : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (internal : m ≤ o) (ho : o < m+s)
    (norm : ∀ k < s, Normal (raw k) (m+k))
    (sem : ∀ k < s, X (m+k) = (raw k).eval X)
    (dist : FirstGate.Distinguishes m X o (raw 0).left (raw 0).right) :
    2 ≤ fanout s raw (raw 0).left ∨ 2 ≤ fanout s raw (raw 0).right := by
  by_contra! low
  have hs : 0 < s := by omega
  have a0 : uses raw (raw 0).left 0 := Or.inl rfl
  have b0 : uses raw (raw 0).right 0 := Or.inr rfl
  obtain ⟨u,hu,v,hv,ab,ba,other⟩ := dist
  have all (w : ℕ) (lim : w < m+s) (wa : w ≠ (raw 0).left) (wb : w ≠ (raw 0).right) :
      u ∈ X w → v ∈ X w := by
    induction w using Nat.strong_induction_on with
    | ind w prev =>
      by_cases inp : w < m
      · exact other w inp wa wb
      let k := w-m
      have eq : w=m+k := by dsimp [k]; omega
      have hk : k<s := by omega
      have hnorm := norm k hk
      rw [eq,sem k hk]
      by_cases first : k=0
      · rw [first]
        change u ∈ (raw 0).op.eval _ _ → v ∈ (raw 0).op.eval _ _
        rcases (norm 0 hs).2.2.2 with join|meet
        · rw [join]; exact fun h => h.elim (fun a => Or.inr (ab a)) (fun b => Or.inl (ba b))
        · rw [meet]; exact fun h => ⟨ba h.2,ab h.1⟩
      · have la := unique_use s raw _ hs a0 (by omega) k hk first
        have lb := unique_use s raw _ hs b0 (by omega) k hk first
        have l : (raw k).left < w := eq ▸ hnorm.1
        have r : (raw k).right < w := eq ▸ hnorm.2.1
        apply transfer
        · exact prev _ l (by omega) (fun e => la (Or.inl e)) (fun e => lb (Or.inl e))
        · exact prev _ r (by omega) (fun e => la (Or.inr e)) (fun e => lb (Or.inr e))
  have normal := norm 0 hs
  have la : (raw 0).left < m := by simpa using normal.1
  have lb : (raw 0).right < m := by simpa using normal.2.1
  exact hv (all o ho (by omega) (by omega) hu)

theorem select_parent {Z : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (internal : m ≤ o) (ho : o < m+s) (norm : ∀ k < s, Normal (raw k) (m+k))
    (sem : ∀ k < s, X (m+k) = (raw k).eval X) :
    ∃ i ∈ ({(raw 0).left,(raw 0).right} : Finset ℕ), i < m ∧ 1 ≤ fanout s raw i ∧
      (FirstGate.Distinguishes m X o (raw 0).left (raw 0).right → 2 ≤ fanout s raw i) := by
  have hs : 0<s := by omega
  have n := norm 0 hs
  by_cases high : 2 ≤ fanout s raw (raw 0).left
  · exact ⟨_,Finset.mem_insert_self _ _,by simpa using n.1,by omega,fun _ => high⟩
  · refine ⟨(raw 0).right,by simp,by simpa using n.2.1,occurs s raw _ hs (Or.inr rfl),?_⟩
    exact fun h => (double_fanout m s o raw X internal ho norm sem h).resolve_left high

theorem eliminate_parent {Z W : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (internal : m ≤ o) (ho : o < m+s) (norm : ∀ k < s, Normal (raw k) (m+k))
    (sem : ∀ k < s, X (m+k) = (raw k).eval X) (D : Finset ℕ)
    (parents_alive : (raw 0).left ∉ D ∧ (raw 0).right ∉ D)
    (rows : ℕ → W → Z)
    (fixed : ∀ i ∈ ({(raw 0).left,(raw 0).right} : Finset ℕ), ∀ j ∈ insert i D, j < m →
      rows i ⁻¹' X j = ∅)
    (live : ∀ i ∈ ({(raw 0).left,(raw 0).right} : Finset ℕ), (rows i ⁻¹' X o).Nonempty) :
    ∃ i ∈ ({(raw 0).left,(raw 0).right} : Finset ℕ), i < m ∧ i ∉ D ∧
      ∃ (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set W), t+1 ≤ s ∧
      (FirstGate.Distinguishes m X o (raw 0).left (raw 0).right → t+2 ≤ s) ∧
      out < m+t ∧ rows i ⁻¹' X o = Y out ∧ (∀ j < m, Y j = rows i ⁻¹' X j) ∧
      ∀ g < t, Normal (code g) (m+g) ∧ Y (m+g) = (code g).eval Y ∧
        ∀ j ∈ insert i D, j < m → (code g).left ≠ j ∧ (code g).right ≠ j := by
  obtain ⟨i,mem,hi,one,two⟩ := select_parent m s o raw X internal ho norm sem
  have alive : i ∉ D := by
    rcases Finset.mem_insert.mp mem with rfl|e
    · exact parents_alive.1
    · rw [Finset.mem_singleton.mp e]; exact parents_alive.2
  obtain ⟨t,out,code,Y,_,credit,limit,eq,input,gates⟩ := restrict_mask m s o raw
    (fun j => rows i ⁻¹' X j) (insert i D) ho (fixed i mem) (live i mem)
    (fun g hg => ⟨(norm g hg).1,(norm g hg).2.1⟩)
    (by intro g hg; rw [sem g hg,preimage_gate])
  have cost : t + fanout s raw i ≤ s := credit i (by simp) hi
  refine ⟨i,mem,hi,alive,t,out,code,Y,by omega,?_,limit,eq,input,gates⟩
  intro h
  have := two h
  omega

end CircuitRewire
