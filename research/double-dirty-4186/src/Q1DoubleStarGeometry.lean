import Q1DoubleOneLeak
import Q1DoubleStarCubes

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

/-- The two shared tight supports force a common endpoint for every fresh
edge, and a matching can use that endpoint only once. -/
theorem tight_central_bound {V : Type*} {r : ℕ} (edge : Fin r → Bool → V)
    (separated : ∀ i j, i ≠ j → ∀ b c, edge i b ≠ edge j c)
    (label : OneLeak.Pos → V) (inj : Function.Injective label)
    (T : Finset OneLeak.Pattern)
    (exclusive : ∀ p q, ¬ ∃ i, edge i false = label p ∧ edge i true = label q)
    (hits : ∀ i, ∀ t ∈ T, OneLeak.inSlot label t (edge i false) ∨
      OneLeak.inSlot label t (edge i true))
    {t u : OneLeak.Pattern} (ht : t ∈ T) (hu : u ∈ T) (neq : t ≠ u) : r ≤ 1 := by
  classical
  by_contra! h
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin r := ⟨1,by omega⟩
  let fresh (a b : V) : Prop := ∃ k, edge k false=a ∧ edge k true=b
  have meet : ∀ a b, fresh a b → ∀ v ∈ T,
      OneLeak.inSlot label v a ∨ OneLeak.inSlot label v b := by
    rintro a b ⟨k,rfl,rfl⟩; exact hits k
  obtain ⟨p,hub⟩ := OneLeak.two_shared_hub (fresh := fresh) inj exclusive meet ht hu neq
    ⟨_,_,i,rfl,rfl⟩
  have sep := separated i j (by intro e; have := congrArg Fin.val e; simp [i,j] at this)
  rcases hub _ _ ⟨i,rfl,rfl⟩ with a|a <;> rcases hub _ _ ⟨j,rfl,rfl⟩ with b|b <;>
    exact sep _ _ (a.symm.trans b)

/-- Any one vertex occurs in at most one edge of the indexed matching.
Removing one edge leaves r complete edges avoiding that vertex. -/
theorem omit_vertex {V : Type*} {r : ℕ} (pt : Fin (r+1) → Bool → V)
    (separated : ∀ i j, i ≠ j → ∀ b c, pt i b ≠ pt j c) (x : V) :
    ∃ j : Fin (r+1), ∀ i b, pt (j.succAbove i) b ≠ x := by
  classical
  by_cases h : ∃ j b, pt j b = x
  · obtain ⟨j,b,rfl⟩ := h
    exact ⟨j,fun i c => separated _ _ (Fin.succAbove_ne j i) c b⟩
  · exact ⟨0,fun i b he => h ⟨_,b,he⟩⟩

/-- The induced edges in N(v) have no other edges among their endpoints.
The codegree condition bounds the degree of the graph induced on N(v) by one. -/
theorem neighborhood_induced {V I : Type*} (G : SimpleGraph V) (v : V)
    (noFour : ∀ {a b c d}, c ≠ d → G.Adj a c → G.Adj a d →
      G.Adj b c → G.Adj b d → a=b)
    (pt : I → Bool → V) (adj : ∀ i, G.Adj (pt i false) (pt i true))
    (inside : ∀ i b, G.Adj v (pt i b))
    (disjoint : ∀ i j, i ≠ j → ∀ b c, pt i b ≠ pt j c)
    (i j : I) (ne : i ≠ j) (b c : Bool) : ¬ G.Adj (pt i b) (pt j c) := by
  intro cross
  have mate : G.Adj (pt i b) (pt i (!b)) := by cases b <;> simp [adj,(adj i).symm]
  have eq := noFour (disjoint i j ne (!b) c) (inside i (!b)) (inside j c) mate cross
  exact G.loopless.irrefl _ (eq ▸ inside i b)

/-- Two boundary edges with distinct inside endpoints force at least three
private slots. Each of three independent transversals contains an inside
endpoint, and consequently already hits every shared slot. -/
theorem crossing_double_three {V P : Type*} [Fintype P] (a b : Bool → V)
    (privateSlot : P → V → Prop)
    (hitA : ∀ p, privateSlot p (a false) ∨ privateSlot p (a true))
    (hitB : ∀ p, privateSlot p (b false) ∨ privateSlot p (b true))
    (reject : ∀ i j : Bool, i = true ∨ j = true →
      ∃ p, ¬ privateSlot p (a i) ∧ ¬ privateSlot p (b j)) : 3 ≤ Fintype.card P := by
  classical
  obtain ⟨x,xa,xb⟩ := reject true false (Or.inl rfl)
  obtain ⟨y,ya,yb⟩ := reject false true (Or.inr rfl)
  obtain ⟨z,za,zb⟩ := reject true true (Or.inl rfl)
  have xy : x ≠ y := by rintro rfl; exact (hitA x).elim ya xa
  have xz : x ≠ z := by rintro rfl; exact (hitB x).elim xb zb
  have yz : y ≠ z := by rintro rfl; exact (hitA y).elim ya za
  have h := Finset.card_le_univ ({x,y,z} : Finset P)
  simpa [xy,xz,yz] using h

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
