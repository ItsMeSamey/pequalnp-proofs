import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem cube_center_constant {I V : Type*} [Fintype I] (label : (I → Bool) → V)
    (step : ∀ (i : I) (x y : I → Bool), (∀ k, k ≠ i → x k = y k) → label x = label y)
    (x y : I → Bool) : label x = label y := by
  classical
  let patch (s : Finset I) (k : I) := if k ∈ s then y k else x k
  have h (s : Finset I) : label x = label (patch s) := by
    induction s using Finset.induction_on with
    | empty => simp [patch]
    | @insert i s hi ih =>
      apply ih.trans (step i _ _ ?_)
      intro k hk
      simp [patch, hk]
  simpa [patch] using h Finset.univ

theorem rejecting_centers_equal {I V : Type*} [Fintype I]
    (point : I → Bool → V) (p : (I → Bool) → V) (adj : V → V → Prop)
    (twoOthers : ∀ i : I, ∃ j k : I, j ≠ i ∧ k ≠ i ∧ j ≠ k)
    (separate : ∀ {i j : I}, i ≠ j → ∀ b c, point i b ≠ point j c)
    (anchored : ∀ t i, adj (p t) (point i (t i)))
    (codegree : ∀ {a b u v}, u ≠ v → adj a u → adj a v → adj b u → adj b v → a = b)
    (s t : I → Bool) : p s = p t := by
  apply cube_center_constant p _ s t
  intro i x y agree
  obtain ⟨j,k,hj,hk,hjk⟩ := twoOthers i
  apply codegree (separate hjk (x j) (x k)) (anchored x j) (anchored x k)
  · simpa only [agree j hj] using anchored y j
  · simpa only [agree k hk] using anchored y k

theorem rich_common_center {I V K : Type*} [Fintype I] [Nonempty I]
    (point : I → Bool → V) (center : K → V) (contains : K → V → Prop) (adj : V → V → Prop)
    (twoOthers : ∀ i : I, ∃ j k : I, j ≠ i ∧ k ≠ i ∧ j ≠ k)
    (separate : ∀ {i j : I}, i ≠ j → ∀ b c, point i b ≠ point j c)
    (reject : ∀ t : I → Bool, ∃ k : K, ∀ i, contains k (point i (t i)))
    (hits : ∀ k i, ∃ b, contains k (point i b))
    (anchor : ∀ k v, contains k v → adj (center k) v)
    (codegree : ∀ {a b u v}, u ≠ v → adj a u → adj a v → adj b u → adj b v → a = b) :
    ∃ common, (∀ i b, adj common (point i b)) ∧ ∀ k, center k = common := by
  classical
  choose rejected hreject using reject
  let fixed : I → Bool := fun _ => false
  let common := center (rejected fixed)
  have eq (t : I → Bool) : common = center (rejected t) :=
    rejecting_centers_equal point (fun v => center (rejected v)) adj twoOthers separate
      (fun v i => anchor _ _ (hreject v i)) codegree fixed t
  have neigh (i : I) (b : Bool) : adj common (point i b) := by
    rw [eq (fun _ => b)]
    exact anchor _ _ (hreject (fun _ => b) i)
  refine ⟨common, neigh, ?_⟩
  intro k
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨j,l,_,_,hjl⟩ := twoOthers i
  obtain ⟨b,hb⟩ := hits k j
  obtain ⟨c,hc⟩ := hits k l
  exact codegree (separate hjl b c) (anchor _ _ hb) (anchor _ _ hc) (neigh j b) (neigh l c)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
