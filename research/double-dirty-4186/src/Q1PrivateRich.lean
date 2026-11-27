import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem common_center (four : NoFourCycle G) {c d a b : Fin n} (ab : a ≠ b)
    (ca : G.Adj c a) (cb : G.Adj c b) (da : G.Adj d a) (db : G.Adj d b) : c=d := by
  by_contra ne
  exact ab (Finset.card_le_one.mp (four c d ne) a
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ca,da⟩) b
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,cb,db⟩))

/-- The all-false orientation and its three single flips already determine one center. -/
theorem rich_center {K : Type*} (four : NoFourCycle G) (p : Fin 3 → Bool → Fin n)
    (cl : K → Finset (Fin n))
    (sep : ∀ i j, i ≠ j → ∀ x y, p i x ≠ p j y)
    (hits : ∀ k i, p i false ∈ cl k ∨ p i true ∈ cl k)
    (reject : ∀ t : Fin 3 → Bool, ∃ k, ∀ i, p i (t i) ∉ cl k)
    (anchor : ∀ k, ∀ x ∈ cl k, ∀ y ∈ cl k, x ≠ y → ∃ w, ∀ z ∈ cl k, G.Adj w z) :
    ∃ w, ∀ i b, G.Adj w (p i b) := by
  classical
  have anchored (t : Fin 3 → Bool) : ∃ w, ∀ i, G.Adj w (p i (t i)) := by
    obtain ⟨k,miss⟩ := reject (fun i => !(t i))
    have mem (i) : p i (t i) ∈ cl k := by
      have h := hits k i
      have m := miss i
      cases eq : t i with
      | false => exact h.resolve_right (by simpa [eq] using m)
      | true => exact h.resolve_left (by simpa [eq] using m)
    obtain ⟨w,hw⟩ := anchor k _ (mem 0) _ (mem 1) (sep 0 1 (by decide) _ _)
    exact ⟨w, fun i => hw _ (mem i)⟩
  obtain ⟨w,hw⟩ := anchored (fun _ => false)
  refine ⟨w, fun j b => ?_⟩
  cases b with
  | false => exact hw j
  | true =>
    let t := fun i : Fin 3 => decide (i=j)
    obtain ⟨v,hv⟩ := anchored t
    have witnesses : ∀ j : Fin 3, ∃ a b : Fin 3, a ≠ b ∧ a ≠ j ∧ b ≠ j := by decide
    obtain ⟨a,b,ab,aj,bj⟩ := witnesses j
    have va : G.Adj v (p a false) := by simpa [t,aj] using hv a
    have vb : G.Adj v (p b false) := by simpa [t,bj] using hv b
    have eq := common_center four (sep a b ab false false) va vb (hw a) (hw b)
    simpa [eq,t] using hv j

/-- A shared guard hitting a three-edge matching has the same center as that batch. -/
theorem guard_center (four : NoFourCycle G) (p : Fin 3 → Bool → Fin n) (L : Finset (Fin n))
    (c d : Fin n) (hc : ∀ i b, G.Adj c (p i b)) (hd : ∀ z ∈ L, G.Adj d z)
    (sep : ∀ i j, i ≠ j → ∀ x y, p i x ≠ p j y)
    (hits : ∀ i, ∃ b, p i b ∈ L) : c = d := by
  obtain ⟨x,hx⟩ := hits 0
  obtain ⟨y,hy⟩ := hits 1
  exact common_center four (sep 0 1 (by decide) x y) (hc 0 x) (hc 1 y) (hd _ hx) (hd _ hy)

/-- Two different neighbors of a vertex in a single common neighborhood coincide. -/
theorem nbhd_matching (four : NoFourCycle G) {c z x y : Fin n}
    (cz : G.Adj c z) (cx : G.Adj c x) (cy : G.Adj c y)
    (zx : G.Adj z x) (zy : G.Adj z y) : x = y := by
  by_contra xy
  exact G.irrefl ((common_center four xy cx cy zx zy) ▸ cz)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
