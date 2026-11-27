import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem independent_three {a b z : Fin n}
    (ab : ¬ G.Adj a b) (az : ¬ G.Adj a z) (bz : ¬ G.Adj b z) :
    ¬ ∃ x ∈ ({a,b,z} : Finset _), ∃ y ∈ ({a,b,z} : Finset _), G.Adj x y := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro ⟨x,rfl | rfl | rfl,y,rfl | rfl | rfl,e⟩
  all_goals first | exact G.irrefl e | exact ab e | exact az e | exact bz e |
    exact ab e.symm | exact az e.symm | exact bz e.symm

private theorem blocks_attachment (four : NoFourCycle G) {a m z w : Fin n}
    (az : a ≠ z) (edge : G.Adj m a) (res : s(m,a) ∈ Ustar G C)
    (wa : G.Adj w a) (wz : G.Adj w z) (star : s(w,a) ∈ starEdges G C) :
    ¬ G.Adj m z := by
  intro mz
  by_cases eq : w=m
  · exact (Finset.mem_sdiff.mp res).2 (eq ▸ star)
  · exact az (Finset.card_le_one.mp (four w m eq) a
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wa,edge⟩) z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wz,mz⟩))

/-- Four literal occurrences suffice to reject the four independent orientations
only if every occurrence is exactly the opposite pair, even off the four endpoints. -/
theorem tight_patterns (four : NoFourCycle G) (p : Bool → Bool → Fin n)
    (L : Fin 4 → Finset (Fin n))
    (hit : ∀ c i, p i false ∈ L c ∨ p i true ∈ L c)
    (clean : ∀ S : Finset (Fin n), (∀ c, ∃ v ∈ S, v ∈ L c) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj x y)
    (indep : ∀ x y, ¬ G.Adj (p false x) (p true y))
    (sep : ∀ x y, p false x ≠ p true y)
    (edge : ∀ i k, G.Adj (p i k) (p i (!k)))
    (res : ∀ i k, s(p i k,p i (!k)) ∈ Ustar G C)
    (anchor : ∀ c, ∀ x ∈ L c, ∀ y ∈ L c, x ≠ y →
      ∃ w, ∀ z ∈ L c, G.Adj w z ∧ s(w,z) ∈ starEdges G C) :
    ∃ f : Fin 4 ≃ (Bool → Bool), ∀ c, L c = {p false (f c false), p true (f c true)} := by
  classical
  let Miss (c : Fin 4) (t : Bool → Bool) := ∀ i, p i (t i) ∉ L c
  have reject (t : Bool → Bool) : ∃ c, Miss c t := by
    by_contra! none
    let a := p false (t false)
    let b := p true (t true)
    apply independent_three (a:=a) (b:=b) (z:=b) (indep _ _) (indep _ _) (G.loopless.irrefl b)
    apply clean
    intro d
    have no := none d
    change ¬ (∀ i, p i (t i) ∉ L d) at no
    push_neg at no
    obtain ⟨i,hi⟩ := no
    cases i
    · exact ⟨a, by simp, hi⟩
    · exact ⟨b, by simp, hi⟩
  choose pick picked using reject
  have same {d : Fin 4} {s t : Bool → Bool} (hs : Miss d s) (ht : Miss d t) : s=t := by
    funext i
    have h1 := hs i
    have h2 := ht i
    have h3 := hit d i
    cases es : s i <;> cases et : t i <;> simp_all
  have inj : Function.Injective pick := by
    intro s t eq
    exact same (eq ▸ picked s) (picked t)
  have onto : Function.Surjective pick :=
    ((Fintype.bijective_iff_injective_and_card pick).mpr ⟨inj,by decide⟩).2
  let en := Equiv.ofBijective pick ⟨inj,onto⟩
  let flip : (Bool → Bool) ≃ (Bool → Bool) :=
    ⟨fun t i => !(t i),fun t i => !(t i),fun t => funext fun i => by simp,
     fun t => funext fun i => by simp⟩
  refine ⟨en.symm.trans flip,?_⟩
  intro c
  let t := en.symm c
  have ht : pick t = c := en.apply_symm_apply c
  have missed : Miss c t := ht ▸ picked t
  have other (d : Fin 4) (ne : d ≠ c) : ∃ i, p i (t i) ∈ L d := by
    by_contra! h
    obtain ⟨s,rfl⟩ := onto d
    have st := same (picked s) h
    exact ne (st ▸ ht)
  have opposite (i : Bool) : p i (!(t i)) ∈ L c := by
    have h := hit c i
    have m := missed i
    cases ei : t i <;> simp_all
  let a := p false (!(t false))
  let b := p true (!(t true))
  obtain ⟨w,hw⟩ := anchor c a (opposite false) b (opposite true) (sep _ _)
  change L c = {a,b}
  apply Finset.ext
  intro z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    by_contra! outside
    let l := p false (t false)
    let r := p true (t true)
    have lz : ¬ G.Adj l z := blocks_attachment four (Ne.symm outside.1)
      (edge false _) (res false _) (hw a (opposite false)).1 (hw z hz).1 (hw a (opposite false)).2
    have rz : ¬ G.Adj r z := blocks_attachment four (Ne.symm outside.2)
      (edge true _) (res true _) (hw b (opposite true)).1 (hw z hz).1 (hw b (opposite true)).2
    apply independent_three (indep _ _) lz rz
    apply clean
    intro d
    by_cases eq : d=c
    · exact ⟨z, by simp, eq ▸ hz⟩
    · obtain ⟨i,hi⟩ := other d eq
      cases i
      · exact ⟨l, by simp [l], hi⟩
      · exact ⟨r, by simp [r], hi⟩
  · rintro (rfl | rfl)
    · exact opposite false
    · exact opposite true

theorem tight_clause (four : NoFourCycle G) (p : Bool → Bool → Fin n)
    (L : Fin 4 → Finset (Fin n))
    (hit : ∀ c i, p i false ∈ L c ∨ p i true ∈ L c)
    (clean : ∀ S : Finset (Fin n), (∀ c, ∃ v ∈ S, v ∈ L c) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj x y)
    (indep : ∀ x y, ¬ G.Adj (p false x) (p true y))
    (sep : ∀ x y, p false x ≠ p true y)
    (edge : ∀ i k, G.Adj (p i k) (p i (!k)))
    (res : ∀ i k, s(p i k,p i (!k)) ∈ Ustar G C)
    (anchor : ∀ c, ∀ x ∈ L c, ∀ y ∈ L c, x ≠ y →
      ∃ w, ∀ z ∈ L c, G.Adj w z ∧ s(w,z) ∈ starEdges G C)
    (c : Fin 4) : ∃ u v, L c = {u,v} := by
  obtain ⟨f,hf⟩ := tight_patterns four p L hit clean indep sep edge res anchor
  exact ⟨_,_,hf c⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
