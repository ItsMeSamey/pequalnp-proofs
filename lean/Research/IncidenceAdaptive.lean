import Research.IncidenceIterate
import Research.AdaptiveTerminal

namespace IncidenceAdaptive
open FirstGate CircuitRewire IncidenceIterate

structure Geometry (m d : ℕ) (E : ℕ → ℕ → Prop) (B : Finset ℕ → Finset ℕ) : Prop where
  enough : ∀ D : Finset ℕ, D ⊆ Finset.range m → D.card ≤ d → D.card+(B D).card+2 ≤ m
  irrefl : ∀ a < m, ¬ E a a
  grows : ∀ D D' : Finset ℕ, D ⊆ D' → B D ⊆ B D'
  neighbor : ∀ D : Finset ℕ, D ⊆ Finset.range m → D.card ≤ d → ∀ a < m, a ∉ D → a ∉ B D →
    ∃ c < m, c ∉ D ∧ E a c
  transpose : ∀ D : Finset ℕ, D ⊆ Finset.range m → D.card ≤ d →
    ∀ a < m, a ∉ D → ∀ b < m, b ∉ D → a ≠ b → (a ∉ B D ∨ b ∉ B D) →
    ∃ c < m, c ∉ D ∧ c ≠ a ∧ c ≠ b ∧ ((E a c ∧ ¬ E b c) ∨ (E b c ∧ ¬ E a c))

variable {m d : ℕ} {E : ℕ → ℕ → Prop} {B : Finset ℕ → Finset ℕ} {D : Finset ℕ} {s o : ℕ}
variable {raw : ℕ → Gate} {X : ℕ → Set (Finset ℕ)}
theorem essential (G : Geometry m d E B) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card ≤ d) (a : ℕ) (ha : a < m) (alive : a ∉ D) (good : a ∉ B D) :
    Essential m X o a := by
  obtain ⟨c,hc,hD,edge⟩ := G.neighbor D sub small a ha alive good
  refine ⟨{a,c},(R.pairs a ha alive c hc hD).mpr edge,{c},?_,?_⟩
  · simpa using (fun h => G.irrefl c hc ((R.pairs c hc hD c hc hD).mp h))
  · intro t ht ne
    rw [R.inputs t ht,R.inputs t ht]
    simp [ne]

private theorem oriented (R : Realizes m E D s o raw X)
    {a b c : ℕ} (ha : a<m) (hb : b<m) (hc : c<m) (aD : a ∉ D) (bD : b ∉ D) (cD : c ∉ D)
    (ab : a ≠ b) (cb : c ≠ b) (edge : E a c) (non : ¬ E b c) : Distinguishes m X o a b := by
  refine ⟨{a,c},(R.pairs a ha aD c hc cD).mpr edge,{b,c},fun h => non ((R.pairs b hb bD c hc cD).mp h),?_,?_,?_⟩
  · intro _; exact (R.inputs b hb _).mpr ⟨by simp,bD⟩
  · intro h
    have inc := ((R.inputs b hb _).mp h).1
    simp [Ne.symm ab,Ne.symm cb] at inc
  · intro t ht na nb
    rw [R.inputs t ht,R.inputs t ht]
    simp [na,nb]

theorem distinguish (G : Geometry m d E B) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card ≤ d)
    (a b : ℕ) (ha : a<m) (hb : b<m) (aD : a ∉ D) (bD : b ∉ D) (ab : a ≠ b) (good : a ∉ B D ∨ b ∉ B D) :
    Distinguishes m X o a b := by
  obtain ⟨c,hc,cD,ca,cb,law⟩ := G.transpose D sub small a ha aD b hb bD ab good
  rcases law with yes|no
  · exact oriented R ha hb hc aD bD cD ab cb yes.1 yes.2
  · obtain ⟨u,hu,v,hv,ba,ab',other⟩ := oriented R hb ha hc bD aD cD ab.symm ca no.1 no.2
    exact ⟨u,hu,v,hv,ab',ba,fun t ht na nb => other t ht nb na⟩

theorem advance (G : Geometry m d E B) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card < d) :
    ∃ i < m, i ∉ D ∧ ∃ t out code Y,
      t+2+(D ∩ B D).card ≤ s+((insert i D) ∩ B (insert i D)).card ∧ Realizes m E (insert i D) t out code Y := by
  have big := G.enough D sub (by omega)
  have inner := AdaptiveTerminal.internal m o X D (B D) (by omega) (essential G R sub (by omega))
  have hs : 0<s := by have := R.bounded; omega
  have norm := R.normal 0 hs
  let a := (raw 0).left
  let b := (raw 0).right
  have ha : a<m := by simpa [a] using norm.1
  have hb : b<m := by simpa [b] using norm.2.1
  have aD : a ∉ D := fun h => (R.avoids 0 hs a h ha).1 rfl
  have bD : b ∉ D := fun h => (R.avoids 0 hs b h hb).2 rfl
  let rows := fun (i : ℕ) (T : Finset ℕ) => T.erase i
  have live (i : ℕ) (mem : i ∈ ({a,b} : Finset ℕ)) : (rows i ⁻¹' X o).Nonempty := by
    have hi : i<m := by rcases Finset.mem_insert.mp mem with rfl|h <;> simp_all
    have sub' : insert i D ⊆ Finset.range m := Finset.insert_subset (Finset.mem_range.mpr hi) sub
    have small' : (insert i D).card ≤ d := by have := Finset.card_insert_le i D; omega
    have room := G.enough (insert i D) sub' small'
    obtain ⟨p,hp,pD,l,hl,lD,h⟩ := AdaptiveTerminal.exists_edge m E (insert i D) (B (insert i D))
      (by omega) (G.neighbor _ sub' small')
    have old (z : ℕ) (h : z ∉ insert i D) : z ∉ D := fun hz => h (Finset.mem_insert_of_mem hz)
    refine ⟨{p,l},?_⟩
    change ({p,l} : Finset ℕ).erase i ∈ X o
    rw [Finset.erase_eq_of_notMem (by simp_all [eq_comm])]
    exact (R.pairs p hp (old p pD) l hl (old l lD)).mpr h
  obtain ⟨i,mem,hi,fresh,t,out,code,Y,one,save,lim,eq,inp,gates⟩ :=
    eliminate_parent m s o raw X inner R.bounded R.normal R.gate D ⟨aD,bD⟩ rows (by
      intro i _ j hj bound
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T h
      obtain ⟨hT,hD⟩ := (R.inputs j bound _).mp h
      rcases Finset.mem_insert.mp hj with rfl|h'
      · exact Finset.notMem_erase _ _ hT
      · exact hD h') live
  have grow := G.grows D (insert i D) (Finset.subset_insert _ _)
  have old : D ∩ B D ⊆ insert i D ∩ B (insert i D) :=
    Finset.inter_subset_inter (Finset.subset_insert _ _) grow
  have amort : t+2+(D ∩ B D).card ≤ s+(insert i D ∩ B (insert i D)).card := by
    by_cases hit : i ∈ B D
    · have inc : insert i (D ∩ B D) ⊆ insert i D ∩ B (insert i D) :=
        Finset.insert_subset (Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,grow hit⟩) old
      have count := Finset.card_le_card inc
      have ne : i ∉ D ∩ B D := fun h => fresh (Finset.mem_inter.mp h).1
      rw [Finset.card_insert_of_notMem ne] at count
      omega
    · have good : a ∉ B D ∨ b ∉ B D := by
        rcases Finset.mem_insert.mp mem with e|e
        · exact Or.inl (fun h => hit (e.symm ▸ (show (raw 0).left ∈ B D from h)))
        · exact Or.inr (fun h => hit ((Finset.mem_singleton.mp e).symm ▸ (show (raw 0).right ∈ B D from h)))
      have cost := save (distinguish G R sub (by omega) a b ha hb aD bD norm.2.2.1 good)
      have := Finset.card_le_card old
      omega
  refine ⟨i,hi,fresh,t,out,code,Y,amort,
    lim,fun g hg => (gates g hg).1,fun g hg => (gates g hg).2.1,fun g hg => (gates g hg).2.2,?_,?_⟩
  · intro j hj T
    rw [inp j hj]
    change T.erase i ∈ X j ↔ _
    rw [R.inputs j hj]
    simp only [Finset.mem_erase,Finset.mem_insert,not_or]
    tauto
  · intro p hp pD c hc cD
    rw [← eq]
    change ({p,c} : Finset ℕ).erase i ∈ X o ↔ _
    rw [Finset.erase_eq_of_notMem (by simp_all [eq_comm])]
    apply R.pairs p hp _ c hc _
    · exact fun h => pD (Finset.mem_insert_of_mem h)
    · exact fun h => cD (Finset.mem_insert_of_mem h)

theorem iterate (G : Geometry m d E B) {s₀ o₀ : ℕ} {raw₀ X₀}
    (start : Realizes m E ∅ s₀ o₀ raw₀ X₀) (k : ℕ) (hk : k ≤ d) :
    ∃ (D : Finset ℕ) (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set (Finset ℕ)),
      D ⊆ Finset.range m ∧ D.card=k ∧ t+2*k ≤ s₀+(D ∩ B D).card ∧ Realizes m E D t out code Y := by
  induction k with
  | zero => exact ⟨∅,s₀,o₀,raw₀,X₀,by simp,by simp,by simp,start⟩
  | succ k ih =>
    obtain ⟨D,t,out,code,Y,sub,card,cost,R⟩ := ih (by omega)
    obtain ⟨i,hi,fresh,t',out',code',Y',save,R'⟩ := advance G R sub (by omega)
    refine ⟨insert i D,t',out',code',Y',Finset.insert_subset (Finset.mem_range.mpr hi) sub,?_,by omega,R'⟩
    simp [Finset.card_insert_of_notMem fresh,card]

theorem lower (G : Geometry m d E B) (start : Realizes m E ∅ s o raw X) :
    ∃ D ⊆ Finset.range m, D.card=d ∧ m+d ≤ s+1+(B D).card := by
  obtain ⟨D,t,out,code,Y,sub,card,cost,R⟩ := iterate G start d le_rfl
  have bound := AdaptiveTerminal.lower R (B D) (essential G R sub (by omega))
  have split := Finset.card_sdiff_add_card_inter (B D) D
  rw [Finset.inter_comm] at split
  exact ⟨D,sub,card,by omega⟩

end IncidenceAdaptive
