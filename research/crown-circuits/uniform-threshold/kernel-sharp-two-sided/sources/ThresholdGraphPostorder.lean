import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra

namespace ThresholdGraphPostorder
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- At a reverse-growth step x is deleted, while its two-edge witness x-w-z survives. -/
inductive Peel (base : Finset V) : Finset V → List V → Prop where
  | done : Peel base base []
  | step {s : Finset V} {x w z : V} {xs : List V}
      (fresh : x ∉ s) (hw : w ∈ s) (hz : z ∈ s)
      (e : G.Adj x w) (e' : G.Adj w z) (tail : Peel base s xs) :
      Peel base (insert x s) (x :: xs)

private theorem no_boundary {s : Finset V}
    (closed : ∀ a ∈ s, ∀ b, G.Adj a b → b ∈ s)
    {a b : V} (reach : G.Reachable a b) (ha : a ∈ s) : b ∈ s := by
  obtain ⟨walk⟩ := reach
  revert ha
  induction walk with
  | nil => exact id
  | cons e _ ih => exact fun ha => ih (closed _ ha _ e)

/-- Reverse a growth forest rooted at the specified protected sets. The
    construction only needs one seeded edge per component, and it preserves
    an arbitrarily larger seed, in particular the entire central star. -/
theorem exists_interior_order (base : Finset V)
    (covers : ∀ v, ∃ a ∈ base, G.Reachable a v)
    (paired : ∀ a ∈ base, ∃ z ∈ base, G.Adj a z) :
    ∃ xs : List V, Peel G base Finset.univ xs ∧ xs.length + base.card = Fintype.card V := by
  classical
  let grow := fun (s : Finset V) => ∃ xs : List V, Peel G base s xs ∧
    xs.length + base.card = s.card
  let rec extend (s : Finset V) (hbs : base ⊆ s)
      (partners : ∀ a ∈ s, ∃ z ∈ s, G.Adj a z) (hs : grow s) :
      grow Finset.univ := by
    by_cases full : s = Finset.univ
    · simpa [full] using hs
    · have seed : ∃ w ∈ s, ∃ x ∉ s, G.Adj w x := by
        by_contra! h
        apply full
        apply Finset.eq_univ_of_forall
        intro v
        obtain ⟨a,ha,r⟩ := covers v
        apply no_boundary G (fun w hw x wx => by
          by_contra hx
          exact h w hw x hx wx) r (hbs ha)
      obtain ⟨w,hw,x,hx,e⟩ := seed
      obtain ⟨z,hz,wz⟩ := partners w hw
      obtain ⟨xs,order,len⟩ := hs
      have ins : s ⊆ insert x s := Finset.subset_insert _ _
      apply extend (insert x s) (hbs.trans ins)
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨w,ins hw,e.symm⟩
        · obtain ⟨t,ht,et⟩ := partners v hv
          exact ⟨t,ins ht,et⟩
      · refine ⟨x :: xs,.step hx hw hz e.symm wz order,?_⟩
        simp [Finset.card_insert_of_notMem hx, len, Nat.succ_add]
  termination_by Fintype.card V - s.card
  decreasing_by
      have lt : s.card < Fintype.card V := (Finset.card_lt_iff_ne_univ s).2 full
      rw [Finset.card_insert_of_notMem hx]
      omega
  simpa [grow] using extend base (fun _ h => h) paired ⟨[],.done,by simp⟩

/-- Choosing a remote seed edge requires only that the graph has no isolated vertices. -/
theorem anchor_edge (noIso : ∀ a, ∃ b, G.Adj a b) (c : G.ConnectedComponent) :
    ∃ a b, G.connectedComponentMk a = c ∧ G.connectedComponentMk b = c ∧ G.Adj a b := by
  refine SimpleGraph.ConnectedComponent.ind (fun a => ?_) c
  obtain ⟨b,e⟩ := noIso a
  exact ⟨a,b,rfl,(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj e).symm,e⟩

/-- Assemble arbitrary nonempty edge-supported seeds from different components.
    The card equality counts physical vertices even if the seeds have unequal sizes. -/
theorem component_seeds [Fintype G.ConnectedComponent] [DecidableEq G.ConnectedComponent]
    (S : G.ConnectedComponent → Finset V)
    (loc : ∀ c a, a ∈ S c → G.connectedComponentMk a = c)
    (nonempty : ∀ c, (S c).Nonempty)
    (edge : ∀ c a, a ∈ S c → ∃ b ∈ S c, G.Adj a b) :
    ∃ xs, Peel G (Finset.univ.biUnion S) Finset.univ xs ∧
      xs.length + ∑ c, (S c).card = Fintype.card V := by
  classical
  have disj : (↑(Finset.univ : Finset G.ConnectedComponent) : Set _).PairwiseDisjoint S := by
    intro i _ j _ ne
    exact Finset.disjoint_left.mpr fun a hi hj => ne ((loc i a hi).symm.trans (loc j a hj))
  obtain ⟨xs,hx,hc⟩ := exists_interior_order G (Finset.univ.biUnion S) (by
    intro v
    obtain ⟨a,ha⟩ := nonempty (G.connectedComponentMk v)
    exact ⟨a,Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,ha⟩,
      SimpleGraph.ConnectedComponent.exact (loc _ a ha)⟩) (by
    intro a ha
    obtain ⟨c,_,ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b,hb,ab⟩ := edge c a ha
    exact ⟨b,Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,hb⟩,ab⟩)
  exact ⟨xs,hx,by simpa only [Finset.card_biUnion disj] using hc⟩

/-- Preserve the full central star, and exactly one physical edge per remote component. -/
theorem star_seeds [DecidableRel G.Adj] (u : V) (noIso : ∀ a, ∃ b, G.Adj a b) :
    ∃ S : G.ConnectedComponent → Finset V,
      S (G.connectedComponentMk u) = insert u (G.neighborFinset u) ∧
      (∀ c, c ≠ G.connectedComponentMk u → ∃ a b, G.Adj a b ∧ S c = {a,b}) ∧
      (∀ c a, a ∈ S c → G.connectedComponentMk a = c) ∧
      (∀ c, (S c).Nonempty) ∧ (∀ c a, a ∈ S c → ∃ b ∈ S c, G.Adj a b) := by
  classical
  choose A B hA hB hAB using anchor_edge G noIso
  let S := fun c : G.ConnectedComponent =>
    if c = G.connectedComponentMk u then insert u (G.neighborFinset u) else {A c,B c}
  refine ⟨S,by simp [S],?_,?_,?_,?_⟩
  · intro c hc
    exact ⟨A c,B c,hAB c,by simp [S,hc]⟩
  · intro c a ha
    by_cases hc : c = G.connectedComponentMk u
    · subst c
      have sides : a = u ∨ G.Adj u a := by simpa [S] using ha
      rcases sides with rfl | hadj
      · rfl
      · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).symm
    · simp only [S,if_neg hc,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hA c
      · exact hB c
  · intro c
    by_cases hc : c = G.connectedComponentMk u <;> simp [S,hc]
  · intro c a ha
    by_cases hc : c = G.connectedComponentMk u
    · simp only [S,if_pos hc,Finset.mem_insert] at ha ⊢
      rcases ha with rfl | hadj
      · obtain ⟨b,hb⟩ := noIso a
        exact ⟨b,Or.inr ((G.mem_neighborFinset a b).mpr hb),hb⟩
      · exact ⟨u,Or.inl rfl,((G.mem_neighborFinset u a).mp hadj).symm⟩
    · simp only [S,if_neg hc,Finset.mem_insert,Finset.mem_singleton] at ha ⊢
      rcases ha with rfl | rfl
      · exact ⟨B c,Or.inr rfl,hAB c⟩
      · exact ⟨A c,Or.inl rfl,(hAB c).symm⟩

/-- Count protected vertices using one central term and a constant remote term. -/
theorem star_seed_card [Fintype G.ConnectedComponent] [DecidableRel G.Adj]
    (u : V) (S : G.ConnectedComponent → Finset V)
    (center : S (G.connectedComponentMk u) = insert u (G.neighborFinset u))
    (remote : ∀ c, c ≠ G.connectedComponentMk u → ∃ a b, G.Adj a b ∧ S c = {a,b}) :
    (∑ c, (S c).card) = G.degree u + 1 + 2*(Fintype.card G.ConnectedComponent - 1) := by
  classical
  let c := G.connectedComponentMk u
  have two : ∀ i ∈ Finset.univ.erase c, (S i).card = 2 := by
    intro i hi
    obtain ⟨a,b,ab,e⟩ := remote i (Finset.mem_erase.mp hi).1
    simp [e,ab.ne]
  have main : (S c).card = G.degree u+1 := by
    change (S (G.connectedComponentMk u)).card = _
    rw [center, Finset.card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree]
  have separate := Finset.sum_erase_add (Finset.univ : Finset G.ConnectedComponent)
    (fun i => (S i).card) (Finset.mem_univ c)
  rw [Finset.sum_congr rfl two,main] at separate
  simpa [Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using separate.symm

/-- Every remote anchor is charged once after its interior. -/
theorem charge_count {v k c base interior : Nat}
    (hc : 1 ≤ c) (seed : base = k+1+2*(c-1)) (h : interior+base=v) :
    interior+(c-1)=v-c-k := by omega

end ThresholdGraphPostorder
