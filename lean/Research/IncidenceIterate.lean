import Research.FirstFanout
import Research.ResidualFanIn
import Research.IncidenceInitial
namespace IncidenceIterate
open CircuitRewire FirstGate
structure Geometry (m q : ℕ) (E : ℕ → ℕ → Prop) : Prop where
  enough : q+2 ≤ m
  irrefl : ∀ a < m, ¬ E a a
  neighbor : ∀ D : Finset ℕ, D ⊆ Finset.range m → D.card ≤ q → ∀ a < m, a ∉ D →
    ∃ c < m, c ∉ D ∧ E a c
  transpose : ∀ D : Finset ℕ, D ⊆ Finset.range m → D.card ≤ q →
    ∀ a < m, a ∉ D → ∀ b < m, b ∉ D → a ≠ b →
    ∃ c < m, c ∉ D ∧ c ≠ a ∧ c ≠ b ∧ ((E a c ∧ ¬ E b c) ∨ (E b c ∧ ¬ E a c))

structure Realizes (m : ℕ) (E : ℕ → ℕ → Prop) (D : Finset ℕ) (s o : ℕ)
    (raw : ℕ → Gate) (X : ℕ → Set (Finset ℕ)) : Prop where
  bounded : o < m+s
  normal : ∀ k < s, Normal (raw k) (m+k)
  gate : ∀ k < s, X (m+k) = (raw k).eval X
  avoids : ∀ k < s, ∀ i ∈ D, i < m → (raw k).left ≠ i ∧ (raw k).right ≠ i
  inputs : ∀ i < m, ∀ T, T ∈ X i ↔ i ∈ T ∧ i ∉ D
  pairs : ∀ a < m, a ∉ D → ∀ c < m, c ∉ D → (({a,c} : Finset ℕ) ∈ X o ↔ E a c)

variable {m q : ℕ} {E : ℕ → ℕ → Prop} {D : Finset ℕ} {s o : ℕ}
variable {raw : ℕ → Gate} {X : ℕ → Set (Finset ℕ)}

private theorem available (G : Geometry m q E) (small : D.card ≤ q) :
    ∃ a < m, a ∉ D := by
  by_contra! h
  have inc : Finset.range m ⊆ D := fun a ha => h a (Finset.mem_range.mp ha)
  have := Finset.card_le_card inc
  rw [Finset.card_range] at this
  have := G.enough
  omega

theorem essential (G : Geometry m q E) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card ≤ q) (a : ℕ) (ha : a < m) (alive : a ∉ D) :
    Essential m X o a := by
  obtain ⟨c,hc,hD,edge⟩ := G.neighbor D sub small a ha alive
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

theorem distinguish (G : Geometry m q E) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card ≤ q)
    (a b : ℕ) (ha : a<m) (hb : b<m) (aD : a ∉ D) (bD : b ∉ D) (ab : a ≠ b) :
    Distinguishes m X o a b := by
  obtain ⟨c,hc,cD,ca,cb,law⟩ := G.transpose D sub small a ha aD b hb bD ab
  rcases law with yes|no
  · exact oriented R ha hb hc aD bD cD ab cb yes.1 yes.2
  · obtain ⟨u,hu,v,hv,ba,ab',other⟩ := oriented R hb ha hc bD aD cD ab.symm ca no.1 no.2
    exact ⟨u,hu,v,hv,ab',ba,fun t ht na nb => other t ht nb na⟩

theorem advance (G : Geometry m q E) (R : Realizes m E D s o raw X)
    (sub : D ⊆ Finset.range m) (small : D.card < q) :
    ∃ i < m, i ∉ D ∧ ∃ t out code Y,
      t+2 ≤ s ∧ Realizes m E (insert i D) t out code Y := by
  have big := G.enough
  have inner := ResidualFanIn.internal m o X D sub (by omega) (essential G R sub (by omega))
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
    have small' : (insert i D).card ≤ q := by have := Finset.card_insert_le i D; omega
    obtain ⟨p,hp,pD⟩ := available G small'
    obtain ⟨l,hl,lD,h⟩ := G.neighbor (insert i D) sub' small' p hp pD
    have old (z : ℕ) (h : z ∉ insert i D) : z ∉ D := fun hz => h (Finset.mem_insert_of_mem hz)
    refine ⟨{p,l},?_⟩
    change ({p,l} : Finset ℕ).erase i ∈ X o
    rw [Finset.erase_eq_of_notMem (by simp_all [eq_comm])]
    exact (R.pairs p hp (old p pD) l hl (old l lD)).mpr h
  obtain ⟨i,mem,hi,fresh,t,out,code,Y,_,save,lim,eq,inp,gates⟩ :=
    eliminate_parent m s o raw X inner R.bounded R.normal R.gate D ⟨aD,bD⟩ rows (by
      intro i _ j hj bound
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T h
      obtain ⟨hT,hD⟩ := (R.inputs j bound _).mp h
      rcases Finset.mem_insert.mp hj with rfl|h'
      · exact Finset.notMem_erase _ _ hT
      · exact hD h') live
  refine ⟨i,hi,fresh,t,out,code,Y,save (distinguish G R sub (by omega) a b ha hb aD bD norm.2.2.1),
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

theorem iterate (G : Geometry m q E) {s₀ o₀ : ℕ} {raw₀ X₀}
    (start : Realizes m E ∅ s₀ o₀ raw₀ X₀) (k : ℕ) (hk : k ≤ q) :
    ∃ (D : Finset ℕ) (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set (Finset ℕ)), D ⊆ Finset.range m ∧ D.card=k ∧
      t+2*k ≤ s₀ ∧ Realizes m E D t out code Y := by
  induction k with
  | zero => exact ⟨∅,s₀,o₀,raw₀,X₀,by simp,by simp,by omega,start⟩
  | succ k ih =>
    obtain ⟨D,t,out,code,Y,sub,card,cost,R⟩ := ih (by omega)
    obtain ⟨i,hi,fresh,t',out',code',Y',save,R'⟩ := advance G R sub (by omega)
    refine ⟨insert i D,t',out',code',Y',Finset.insert_subset (Finset.mem_range.mpr hi) sub,?_,by omega,R'⟩
    simp [Finset.card_insert_of_notMem fresh,card]

theorem lower (G : Geometry m q E) (start : Realizes m E ∅ s o raw X) : m+q ≤ s := by
  obtain ⟨D,t,out,code,Y,sub,card,cost,R⟩ := iterate G start q le_rfl
  have := G.enough
  have bound := ResidualFanIn.normalized m t out code Y R.bounded R.normal R.gate D sub (by omega)
    (essential G R sub (by omega)) (fun a ha aD b hb bD ne => distinguish G R sub (by omega) a b ha hb aD bD ne)
  omega

end IncidenceIterate
