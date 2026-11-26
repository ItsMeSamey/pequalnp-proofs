import Research.FirstGate

namespace IncidenceStrict

open FirstGate

private theorem swap {Z : Type*} {m : ℕ} {X : ℕ → Set Z} {o a b c : ℕ} {u v : Z}
    (hb : b < m) (ba : b ≠ a) (bc : b ≠ c)
    (hu : u ∈ X o) (hv : v ∉ X o) (bits : ∀ t < m, u ∈ X t → t = a ∨ t = c)
    (vb : v ∈ X b) (vc : v ∈ X c) : Distinguishes m X o a b := by
  refine ⟨u,hu,v,hv,fun _ => vb,?_,?_⟩
  · intro h
    exact False.elim ((bits b hb h).elim ba bc)
  · intro t ht na _ h
    exact (bits t ht h).elim (fun e => False.elim (na e)) (fun e => e ▸ vc)

private theorem symm {Z : Type*} {m : ℕ} {X : ℕ → Set Z} {o a b : ℕ}
    (h : Distinguishes m X o a b) : Distinguishes m X o b a := by
  obtain ⟨u,hu,v,hv,ab,ba,t⟩ := h
  exact ⟨u,hu,v,hv,ba,ab,fun k hk nb na => t k hk na nb⟩

theorem bound : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (0 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → x2 + x2 ≤ x9) := by
  intro q N I inst hq hN degree unique s o tags X ho inputs steps pos neg
  let one := fun (a b : Fin N) => decide (b = a)
  let avoid := fun (y : Fin N → Bool) (p : Fin N) => decide (¬ ∃ l, I p l ∧ y l = true)
  let P := fun (p l : Fin N) => (one p,one l)
  let V := fun (y : Fin N → Bool) => (avoid y,y)
  have positive (p l : Fin N) (h : I p l) : P p l ∈ X o := pos p l h
  have negOne (l : Fin N) : V (one l) ∉ X o := neg _ (by simp [one]; omega)
  have negZero : V (fun _ => false) ∉ X o := neg _ (by simp)
  have bits (p l : Fin N) (t : ℕ) (ht : t < N+N) (h : P p l ∈ X t) :
      t = p.val ∨ t = N+l.val := by
    by_cases low : t < N
    · let j : Fin N := ⟨t,low⟩
      rw [(inputs j).1] at h
      exact Or.inl (congrArg Fin.val (of_decide_eq_true h : j = p))
    · let j : Fin N := ⟨t-N,by omega⟩
      have e : t = N+j.val := by dsimp [j]; omega
      rw [e,(inputs j).2] at h
      exact Or.inr (e.trans (congrArg (fun x : Fin N => N+x.val) (of_decide_eq_true h : j = l)))
  have vline (l : Fin N) : V (one l) ∈ X (N+l.val) := by
    rw [(inputs l).2]; change decide (l=l) = true; simp
  have vpoint (k p : Fin N) (non : ¬ I p k) : V (one k) ∈ X p.val := by
    rw [(inputs p).1]; change avoid (one k) p = true
    apply decide_eq_true
    rintro ⟨l,hl,h⟩
    exact non ((of_decide_eq_true h : l = k) ▸ hl)
  have zpoint (p : Fin N) : V (fun _ => false) ∈ X p.val := by
    rw [(inputs p).1]; change avoid _ p = true; simp [avoid]
  have big : 2 ≤ N := by omega
  have other (p : Fin N) : ∃ r : Fin N, r ≠ p := by
    by_cases e : p.val=0
    · exact ⟨⟨1,by omega⟩,fun h => by have := congrArg Fin.val h; simp_all⟩
    · exact ⟨⟨0,by omega⟩,fun h => by have := congrArg Fin.val h; simp_all⟩
  have separateP (p r : Fin N) (ne : p ≠ r) : ∃ l, I p l ∧ ¬ I r l := by
    obtain ⟨k,hk,uk⟩ := unique p r ne
    have outside : ∃ t, ¬ I t k := by
      by_contra! all
      have d := degree k
      have eq : (Finset.univ.filter (fun t => I t k)) = Finset.univ := by ext; simp [all]
      rw [Fintype.card_subtype,eq,Finset.card_univ,Fintype.card_fin] at d
      have : 0 < q^2 := Nat.pow_pos (by omega)
      omega
    obtain ⟨t,ht⟩ := outside
    have pt : p ≠ t := fun e => ht (e ▸ hk.1)
    obtain ⟨l,hl,_⟩ := unique p t pt
    exact ⟨l,hl.1,fun hr => ht (uk l ⟨hl.1,hr⟩ ▸ hl.2)⟩
  have pts (l : Fin N) : 1 < (Finset.univ.filter (fun p => I p l)).card := by
    have d := degree l
    rw [Fintype.card_subtype] at d
    omega
  have separateL (l k : Fin N) (ne : l ≠ k) : ∃ p, I p l ∧ ¬ I p k := by
    by_contra! incl
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (pts l)
    have al := (Finset.mem_filter.mp ha).2
    have bl := (Finset.mem_filter.mp hb).2
    obtain ⟨t,_,ut⟩ := unique a b ab
    exact ne ((ut l ⟨al,bl⟩).trans (ut k ⟨incl a al,incl b bl⟩).symm)
  have pointLine (p : Fin N) : ∃ l, I p l := by
    obtain ⟨r,hr⟩ := other p
    obtain ⟨l,hl,_⟩ := separateP p r hr.symm
    exact ⟨l,hl⟩
  have linePoint (l : Fin N) : ∃ p, I p l := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one (pts l))
    exact ⟨p,(Finset.mem_filter.mp hp).2⟩
  have mixed (p l : Fin N) : Distinguishes (N+N) X o (N+l.val) p.val := by
    obtain ⟨r,hr,rp⟩ := Finset.exists_mem_ne (pts l) p
    have hp := p.isLt
    have hrv := r.isLt
    have pr : p.val ≠ r.val := fun e => rp (Fin.ext e.symm)
    exact swap (c := r.val) (by omega) (by omega) pr
      (positive r l (Finset.mem_filter.mp hr).2) negZero
      (fun t ht h => (bits r l t ht h).symm) (zpoint p) (zpoint r)
  refine lower (N+N) s X o ho ?_ (by omega) ?_ ?_
  · intro g hg
    obtain ⟨a,ha,b,hb,law⟩ := steps g hg
    exact ⟨a,ha,b,hb,law.imp_right (Or.imp_right (Or.imp_right And.left))⟩
  · intro i hi
    by_cases low : i < N
    · let p : Fin N := ⟨i,low⟩
      obtain ⟨l,inc⟩ := pointLine p
      refine ⟨_,positive p l inc,_,negOne l,?_⟩
      intro t ht ne h
      exact ((bits p l t ht h).resolve_left ne) ▸ vline l
    · let l : Fin N := ⟨i-N,by omega⟩
      have e : i = N+l.val := by dsimp [l]; omega
      obtain ⟨p,inc⟩ := linePoint l
      refine ⟨_,positive p l inc,_,negZero,?_⟩
      intro t ht ne h
      exact ((bits p l t ht h).resolve_right (by rwa [← e])) ▸ zpoint p
  · intro a ha b hb ab
    by_cases aP : a < N
    · let p : Fin N := ⟨a,aP⟩
      by_cases bP : b < N
      · let r : Fin N := ⟨b,bP⟩
        obtain ⟨l,pl,rl⟩ := separateP p r (fun e => ab (congrArg Fin.val e))
        exact swap (c := N+l.val) hb ab.symm (by omega) (positive p l pl)
          (negOne l) (bits p l) (vpoint l r rl) (vline l)
      · let l : Fin N := ⟨b-N,by omega⟩
        have e : b = N+l.val := by dsimp [l]; omega
        exact e ▸ symm (mixed p l)
    · let l : Fin N := ⟨a-N,by omega⟩
      have e : a = N+l.val := by dsimp [l]; omega
      by_cases bP : b < N
      · let p : Fin N := ⟨b,bP⟩
        exact e ▸ mixed p l
      · let k : Fin N := ⟨b-N,by omega⟩
        have f : b = N+k.val := by dsimp [k]; omega
        have lk : l ≠ k := by intro eq; rw [e,f,eq] at ab; contradiction
        obtain ⟨p,pl,pk⟩ := separateL l k lk
        have hp := p.isLt
        rw [e,f]
        exact swap (c := p.val) (by have := k.isLt; omega) (by omega) (by omega)
          (positive p l pl) (negOne k) (fun t ht h => (bits p l t ht h).symm) (vline k) (vpoint k p pk)

end IncidenceStrict
