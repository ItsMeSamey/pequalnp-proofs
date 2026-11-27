import DDLaminarQuota
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98

/-- A redundant cut may erase every use of a common AND reader. Its sources
are earlier and both influence every strict descendant of this extra cut. -/
structure JointSource {n : ℕ} (C : Circuit) (a b s : ℕ) : Prop where
  first : strictInfluence n C a (n+s)
  second : strictInfluence n C b (n+s)
  on : ∀ x, gateVal n C a x = true → gateVal n C b x = true → gateVal n C s x = true

theorem joint_source {n : ℕ} (C : Circuit) (ao : IsAO2 n C) {s a b : ℕ}
    (len : s<C.size) (hop : (gateAt C s).op = .and)
    (pins : (gateAt C s).inputs = [n+a,n+b]) : JointSource (n := n) C a b s := by
  have left : n+a ∈ (gateAt C s).inputs := by simp [pins]
  have right : n+b ∈ (gateAt C s).inputs := by simp [pins]
  refine ⟨⟨s,len,rfl,n+a,left,.source⟩,⟨s,len,rfl,n+b,right,.source⟩,?_⟩
  intro x hx hy
  change W n C x (n+s) = true
  rw [W_and n C x s len hop _ _ pins (ao.2.1 s len _ left) (ao.2.1 s len _ right)]
  change W n C x (n+a) = true at hx
  change W n C x (n+b) = true at hy
  simp [hx,hy]

theorem joint_wire {n a b t : ℕ} (C : Circuit) (ao : IsAO2 n C) (S : Finset ℕ)
    (aS : a ∈ S) (bS : b ∈ S) (valid : ∀ i ∈ S, i < C.size) (ht : t<C.size)
    (extra : ∀ i ∈ S, i ≠ a → i ≠ b → JointSource (n := n) C a b i)
    (dom : ∀ s, s=a ∨ s=b → strictInfluence n C s (n+t) →
      ∀ x, gateVal n C t x = true → gateVal n C s x = true) (x : Fin n → Bool) :
    gateVal n C t x = true ↔
      ((strictInfluence n C a (n+t) → denotation (physicalSlot n C (multiCuts n C S) C.size (n+a)) x = true) ∧
       (strictInfluence n C b (n+t) → denotation (physicalSlot n C (multiCuts n C S) C.size (n+b)) x = true)) ∧
      denotation (physicalSlot n C (multiCuts n C S) C.size (n+t)) x = true := by
  let rel := fun i => strictInfluence n C i (n+t)
  let v := fun i => denotation (physicalSlot n C (multiCuts n C S) C.size (n+i)) x
  have allDom (act : gateVal n C t x = true) (i) (hi : i ∈ S) (path : rel i) :
      gateVal n C i x = true := by
    by_cases ia : i=a
    · exact dom i (.inl ia) path x act
    by_cases ib : i=b
    · exact dom i (.inr ib) path x act
    have j := extra i hi ia ib
    exact j.on x (dom a (.inl rfl) (strict_trans j.first path) x act)
      (dom b (.inr rfl) (strict_trans j.second path) x act)
  have base := multi_restore C ao S (w:=n+t) (by omega) x allDom
  constructor
  · intro act
    obtain ⟨on,hval⟩ := base.mp act
    have proj := (projected_enabled C ao S valid (n+t) x).mp on
    exact ⟨⟨proj a aS,proj b bS⟩,hval⟩
  · rintro ⟨⟨ca,cb⟩,vt⟩
    apply base.mpr
    refine ⟨?_,vt⟩
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs path
      have small (i) (hi : i ∈ S) (p : strictInfluence n C i (n+s)) :
          W n C x (n+i) = true :=
        ih i (by have := source_lt_of_strict ao p; omega) hi (strict_trans p path)
      have eq := multi_agree C ao S (w:=n+s) (by have := valid s hs; omega) x small
      by_cases sa : s=a
      · subst s; exact eq.trans (ca path)
      by_cases sb : s=b
      · subst s; exact eq.trans (cb path)
      have j := extra s hs sa sb
      exact j.on x (small a aS j.first) (small b bS j.second)

theorem laminar_reader_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (orig C : Circuit) (least : IsLeastAO G orig) (ao : IsAO2 n C) (roots : Finset ℕ)
    (valid : ∀ t ∈ roots, t < C.size) (cover : ∀ x, graphFun G ∅ x = true ↔
      ∃ t ∈ roots, gateVal n C t x = true) (edge : G.edgeFinset.Nonempty)
    (near : C.size + roots.card ≤ orig.size + 2) (a b : ℕ) (S : Finset ℕ)
    (aS : a ∈ S) (bS : b ∈ S) (validS : ∀ i ∈ S, i < C.size)
    (extra : ∀ i ∈ S, i ≠ a → i ≠ b → JointSource (n := n) C a b i)
    (nested : Bool) (shape : ∀ t ∈ roots, strictInfluence n C a (n+t) →
      (strictInfluence n C b (n+t) ↔ nested = true))
    (dom : ∀ t ∈ roots, ∀ s, s=a ∨ s=b → strictInfluence n C s (n+t) →
      ∀ x, gateVal n C t x = true → gateVal n C s x = true) :
    (S.biUnion (readers n C)).card ≤ 3 := by
  apply laminar_quota G orig C least ao roots valid cover edge near a b (validS a aS) (validS b bS)
    nested shape S
  intro t ht x
  exact joint_wire C ao S aS bS validS (valid t ht) extra (dom t ht) x

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
