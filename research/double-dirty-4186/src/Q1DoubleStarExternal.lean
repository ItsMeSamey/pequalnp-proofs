import Q1DoubleStarMixed
import Q1DoubleStarBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private

variable {n r k p : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {shared : Fin k → Clause n} {other : Fin p → Clause n}

/-- Extend the central neighborhood matching by the distinct interior edge
of an external mixed batch, so a subsequent deletion still leaves r edges. -/
theorem mixed_extended_power (P : Batch G C shared other 2) (four : NoFourCycle G)
    (v : Fin n) (hk : 0 < k) (anchor : ∀ c y, y ∈ shared c → G.Adj v y ∧ s(v,y) ∈ starEdges G C)
    (x : Bool) (out : ¬ G.Adj v (P.pt 0 (!x))) (inner : ∀ b, G.Adj v (P.pt 1 b))
    (small : p < 3) (central : Fin r → Bool → Fin n)
    (adj : ∀ i b, G.Adj (central i b) (central i (!b)))
    (inside : ∀ i b, G.Adj v (central i b))
    (distinct : ∀ i j, i ≠ j → ∀ b c, central i b ≠ central j c)
    (fresh : ∀ i b c, s(central i b,central i (!b)) ≠ s(P.pt 1 c,P.pt 1 (!c)))
    (hits : ∀ c i, central i false ∈ shared c ∨ central i true ∈ shared c) :
    p=2 ∧ 2^r ≤ k := by
  classical
  obtain ⟨allX,zv⟩ := crossing_endpoint P hk v anchor 0 x out
  obtain ⟨p2,priv⟩ := mixed_private P x allX small
  have disjoint (i : Fin r) (b c : Bool) : central i b ≠ P.pt 1 c := by
    intro eq
    have same := nbhd_matching four (inside i b) (inside i (!b)) (inner (!c))
      (adj i b) (by simpa only [eq] using P.edges 1 c)
    exact fresh i b c (by rw [eq,same])
  let lab (i : Option (Fin r)) (b : Bool) := i.elim (P.pt 1 b) (fun j => central j b)
  let en : Fin (r+1) ≃ Option (Fin r) := Fintype.equivOfCardEq (by simp)
  have sep {i j} (ne : i≠j) (b c : Bool) : lab i b ≠ lab j c := by
    cases i with
    | none =>
      cases j with
      | none => exact (ne rfl).elim
      | some j => exact (disjoint j c b).symm
    | some i =>
      cases j with
      | none => exact disjoint i b c
      | some j => exact distinct i j (fun e => ne (congrArg some e)) b c
  have ed (i) : G.Adj (lab i false) (lab i true) := by
    cases i with
    | none => exact P.edges 1 false
    | some i => exact adj i false
  have near (i b) : G.Adj v (lab i b) := by cases i <;> first | apply inner | apply inside
  have hit (c i) : lab i false ∈ shared c ∨ lab i true ∈ shared c := by
    cases i with
    | none => exact P.hits (.inl c) 1
    | some i => exact hits c i
  have vx := (anchor ⟨0,hk⟩ _ (allX ⟨0,hk⟩)).1
  exact ⟨p2,mixed_power P four _ _ _ zv (P.edges 0 x).symm vx priv
    (fun i b => lab (en i) b) (fun i j ij => sep (fun e => ij (en.injective e)))
    (fun i => ed (en i)) (fun i => near (en i)) (fun c i => hit c (en i))⟩

/-- From actual clean projected slots, two crossing edges pay the full local
charge without taking any of the leaking block from A. -/
theorem both_cross_pay (P : Batch G C shared other 2) (hk : 0 < k)
    (v : Fin n) (anchor : ∀ c y, y ∈ shared c → G.Adj v y ∧ s(v,y) ∈ starEdges G C)
    (s t : Bool) (out0 : ¬ G.Adj v (P.pt 0 (!s))) (out1 : ¬ G.Adj v (P.pt 1 (!t))) :
    3 ≤ p := by
  have hs := (crossing_endpoint P hk v anchor 0 s out0).1
  have ht := (crossing_endpoint P hk v anchor 1 t out1).1
  let f (i : Fin 2) (d b : Bool) := P.pt i (if b then d else !d)
  have both (j : Fin p) (i : Fin 2) (d : Bool) :
      f i d false ∈ other j ∨ f i d true ∈ other j := by
    have h : P.pt i false ∈ other j ∨ P.pt i true ∈ other j := P.hits (.inr j) i
    cases d <;> simp_all [f,or_comm]
  have h := crossing_double_three (f 0 s) (f 1 t) (fun j y => y ∈ other j)
    (fun j => both j 0 s) (fun j => both j 1 t) (fun b c selected => by
      let o : Fin 2 → Bool := fun i => if i=0 then (if b then s else !s) else (if c then t else !t)
      obtain ⟨slot,miss⟩ := P.reject o
      cases slot with
      | inl j =>
        rcases selected with rfl|rfl
        · exact ((miss 0) (by simpa [o,literals] using hs j)).elim
        · exact ((miss 1) (by simpa [o,literals] using ht j)).elim
      | inr j => exact ⟨j,by simpa [f,o,literals] using miss 0,by simpa [f,o,literals] using miss 1⟩)
  simpa using h

private def permuteBatch {h : ℕ} (P : Batch G C shared other h) (e : Fin h ≃ Fin h) :
    Batch G C shared other h where
  pt i := P.pt (e i)
  edges i := P.edges (e i)
  res i := P.res (e i)
  sep i j ne := P.sep (e i) (e j) (fun h => ne (e.injective h))
  induced i j ne := P.induced (e i) (e j) (fun h => ne (e.injective h))
  hits c i := P.hits c (e i)
  clean := P.clean
  anchor := P.anchor

/-- Every external batch is either paid by its private allowance, belongs
entirely to the common neighborhood and can be pooled, or forces enough
extra shared slots to pay the entire central batch. -/
theorem classify_external {h : ℕ} (P : Batch G C shared other h) (four : NoFourCycle G)
    (v : Fin n) (hk : 0 < k) (hp : 0 < p)
    (anchor : ∀ c y, y ∈ shared c → G.Adj v y ∧ s(v,y) ∈ starEdges G C)
    (central : Fin r → Bool → Fin n)
    (adj : ∀ i b, G.Adj (central i b) (central i (!b)))
    (inside : ∀ i b, G.Adj v (central i b))
    (distinct : ∀ i j, i ≠ j → ∀ b c, central i b ≠ central j c)
    (fresh : ∀ i j b c, s(central i b,central i (!b)) ≠ s(P.pt j c,P.pt j (!c)))
    (hits : ∀ c i, central i false ∈ shared c ∨ central i true ∈ shared c) :
    2*h ≤ p+1 ∨ (0<h ∧ ∀ i b, G.Adj v (P.pt i b)) ∨ (h=2 ∧ p=2 ∧ 2^r ≤ k) := by
  classical
  by_cases ok : 2*h ≤ p+1
  · exact Or.inl ok
  right
  have pos : 0<h := by omega
  by_cases h3 : 3≤h
  · exact Or.inl ⟨pos,rich_shared_neighborhood P h3 four (.inl ⟨0,hk⟩) v
      (fun y hy => (anchor _ y hy).1)⟩
  have eq : h=2 := by omega
  subst h
  by_cases internal : ∀ i b, G.Adj v (P.pt i b)
  · exact Or.inl ⟨by decide,internal⟩
  push_neg at internal
  obtain ⟨j,b,bad⟩ := internal
  let e := Equiv.swap (0 : Fin 2) j
  let T := permuteBatch P e
  have out : ¬ G.Adj v (T.pt 0 (!(!b))) := by simpa [T,permuteBatch,e] using bad
  by_cases inn : ∀ c, G.Adj v (T.pt 1 c)
  · obtain ⟨privateTwo,power⟩ := mixed_extended_power T four v hk anchor (!b) out inn
      (by omega) central adj inside distinct (fun i x y => fresh i (e 1) x y) hits
    exact Or.inr ⟨rfl,privateTwo,power⟩
  · push_neg at inn
    obtain ⟨c,bad'⟩ := inn
    have paid := both_cross_pay T hk v anchor (!b) (!c) out (by simpa using bad')
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
