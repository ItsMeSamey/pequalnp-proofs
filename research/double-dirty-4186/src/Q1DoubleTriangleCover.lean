import Q1DoubleTriangle
import Q1DoubleTriangleSmall

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {L : Type*} [DecidableEq L] (cl : L → Clause n)

/-- A projected batch over named physical primitive occurrences. Distinct
physical slots may carry identical supports. -/
structure Rows (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset L) (r : ℕ) where
  pt : Fin r → Bool → Fin n
  edges : ∀ i k, G.Adj (pt i k) (pt i (!k))
  res : ∀ i k, s(pt i k,pt i (!k)) ∈ Ustar G C
  sep : ∀ i j, i ≠ j → ∀ k l, pt i k ≠ pt j l
  induced : ∀ i j, i ≠ j → ∀ k l, ¬ G.Adj (pt i k) (pt j l)
  hits : ∀ l ∈ S, ∀ i, pt i false ∈ cl l ∨ pt i true ∈ cl l
  clean : ∀ T : Finset (Fin n), (∀ l ∈ S, ∃ v ∈ T, v ∈ cl l) → ∃ x ∈ T, ∃ y ∈ T, G.Adj x y
  anchor : ∀ l ∈ S, ∀ p ∈ cl l, ∀ q ∈ cl l, p ≠ q →
    ∃ v, ∀ z ∈ cl l, G.Adj v z ∧ s(v,z) ∈ starEdges G C

noncomputable def asClauses (S : Finset L) (i : Fin S.card) : Clause n := cl (S.equivFin.symm i)

noncomputable def Rows.pack {S W : Finset L} {r : ℕ} (P : Rows cl G C S r) (hw : W ⊆ S) :
    Batch G C (asClauses cl (S \ W)) (asClauses cl W) r where
  pt := P.pt
  edges := P.edges
  res := P.res
  sep := P.sep
  induced := P.induced
  hits := by
    intro c i
    cases c with
    | inl j => exact P.hits _ (Finset.mem_sdiff.mp ((S \ W).equivFin.symm j).property).1 i
    | inr j => exact P.hits _ (hw (W.equivFin.symm j).property) i
  clean := by
    intro T active
    apply P.clean T
    intro l hl
    by_cases inW : l ∈ W
    · simpa [literals,asClauses] using active (.inr (W.equivFin ⟨l,inW⟩))
    · have hm := Finset.mem_sdiff.mpr ⟨hl,inW⟩
      simpa [literals,asClauses] using active (.inl ((S \ W).equivFin ⟨l,hm⟩))
  anchor := by
    intro c
    cases c with
    | inl j => exact P.anchor _ (Finset.mem_sdiff.mp ((S \ W).equivFin.symm j).property).1
    | inr j => exact P.anchor _ (hw (W.equivFin.symm j).property)

def Covers {r : ℕ} (pt : Fin r → Bool → Fin n) (T : Finset (Fin n)) :=
  ∀ i, ∃ k, pt i k ∈ T

theorem component_pair {S T W U : Finset L} {r s t cost : ℕ}
    (P : Rows cl G C S r) (Q : Rows cl G C T s) (R : Rows cl G C U t)
    (four : NoFourCycle G) (sw : W ⊆ S) (tw : W ⊆ T) (hw : 0<W.card)
    (ha : W.card<S.card) (hb : W.card<T.card)
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (minCost : ∀ H : Finset (Fin n), Covers P.pt H → Covers Q.pt H → Covers R.pt H → cost ≤ H.card)
    (bound : cost ≤ r+s+t) : pairRule S.card T.card W.card r s (r+s+t-cost) := by
  classical
  let a := S \ W
  let b := T \ W
  have h₁ : a.card+W.card = S.card := Finset.card_sdiff_add_card_eq_card sw
  have h₂ : b.card+W.card = T.card := Finset.card_sdiff_add_card_eq_card tw
  have minimum (K : Finset (Fin n)) (kp : Covers P.pt K) (kq : Covers Q.pt K) : cost-t ≤ K.card := by
    let ext := Finset.univ.image (fun j => R.pt j false)
    have hh := minCost (K ∪ ext)
      (fun i => by obtain ⟨k,h⟩ := kp i; exact ⟨k,Finset.mem_union_left _ h⟩)
      (fun i => by obtain ⟨k,h⟩ := kq i; exact ⟨k,Finset.mem_union_left _ h⟩)
      (fun j => ⟨false,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩)
    have card : ext.card ≤ t := by
      simpa [ext] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun j => R.pt j false))
    have h := Finset.card_union_le K ext
    omega
  have hp := pair_rule_of_batches four (P.pack cl sw) (Q.pack cl tw) hw (show 0 < a.card by omega) (show 0 < b.card by omega)
    ex (cost-t) minimum
  change pairRule (a.card+W.card) (b.card+W.card) W.card r s (r+s-(cost-t)) at hp
  rw [h₁,h₂] at hp
  have mono (a b c r s x y : ℕ) (xy : x ≤ y) (h : pairRule a b c r s x) : pairRule a b c r s y := by
    have sf {a h c g} (base : singleForce a h c g x) : singleForce a h c g y := by
      intro hh hfreq
      obtain ⟨hg,hx⟩ := base hh hfreq
      exact ⟨hg,hx.trans xy⟩
    have rp {a b c r s} (base : richPair a b c r s x) : richPair a b c r s y := by
      rcases base with h | ⟨hs, h | ⟨h₁,h₂,h₃,h₄⟩ | ⟨h₁,h₂,h₃,h₄⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨hs,Or.inl h⟩
      · exact Or.inr ⟨hs,Or.inr (Or.inl ⟨h₁,h₂.trans xy,h₃,h₄⟩)⟩
      · exact Or.inr ⟨hs,Or.inr (Or.inr ⟨h₁,h₂.trans xy,h₃,h₄⟩)⟩
    refine ⟨sf h.1,sf h.2.1,?_⟩
    intro big
    have orig := h.2.2 big
    by_cases sr : s ≤ r <;> simp only [sr,if_pos,if_neg] at orig ⊢ <;> exact rp orig
  exact mono _ _ _ _ _ _ _ (by omega) hp

private noncomputable def blockIx {S T : Finset L} (sub : T ⊆ S) :
    ↥T ↪ (Fin (S \ S).card ⊕ Fin S.card) where
  toFun l := .inr (S.equivFin ⟨l.val,sub l.property⟩)
  inj' := by
    intro i j eq
    exact Subtype.ext (congrArg (fun z : ↥S => z.val) (S.equivFin.injective (Sum.inr.inj eq)))

theorem component_small {S T U W Y : Finset L} {r s t cost : ℕ}
    (P : Rows cl G C S r) (Q : Rows cl G C T s) (R : Rows cl G C U t)
    (four : NoFourCycle G) (ws : W ⊆ S) (wt : W ⊆ T) (ys : Y ⊆ S) (yu : Y ⊆ U)
    (dis : Disjoint W Y)
    (exQ : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (exR : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(R.pt j l,R.pt j (!l)))
    (minCost : ∀ H : Finset (Fin n), Covers P.pt H → Covers Q.pt H → Covers R.pt H → cost ≤ H.card) :
    smallRule S.card r W.card s Y.card t (r+s+t-cost) := by
  classical
  let X := Finset.univ.map (blockIx ws)
  let Z := Finset.univ.map (blockIx ys)
  have xz : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro l hx hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,_,eq⟩ := Finset.mem_map.mp hz
    have ev := congrArg (fun z : ↥S => z.val) (S.equivFin.injective (Sum.inr.inj eq))
    exact Finset.disjoint_left.mp dis i.property (ev ▸ j.property)
  have meet {B D : Finset L} {m : ℕ} (V : Rows cl G C D m) (bs : B ⊆ S) (bd : B ⊆ D)
      (l) (mem : l ∈ Finset.univ.map (blockIx bs)) (j : Fin m) :
      ∃ k, V.pt j k ∈ literals (asClauses cl (S \ S)) (asClauses cl S) l := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem
    have hh := V.hits i.val (bd i.property) j
    change ∃ k, V.pt j k ∈ cl (S.equivFin.symm (S.equivFin ⟨i.val,bs i.property⟩)).val
    rw [Equiv.symm_apply_apply]
    exact hh.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  have main := small_rule_of_batches four (P.pack cl (Finset.Subset.refl _ : S ⊆ S))
    (Q.pack cl (Finset.Subset.refl _ : T ⊆ T)) (R.pack cl (Finset.Subset.refl _ : U ⊆ U))
    X Z xz (meet Q ws wt) (meet R ys yu) exQ exR cost minCost
  simpa [X,Z] using main

/-- Three projected roots with three pairwise disjoint shared subtrees.
Returns the actual covering vertices. The footprint parameters are counts
of primitive occurrences and allow duplicate raw supports. -/
theorem triangle_cover {S T U W K M : Finset L} {x y z r s t : ℕ}
    (P : Rows cl G C S r) (Q : Rows cl G C T s) (R : Rows cl G C U t)
    (four : NoFourCycle G) (ws : W ⊆ S) (wt : W ⊆ T)
    (ks : K ⊆ S) (ku : K ⊆ U) (mt : M ⊆ T) (mu : M ⊆ U)
    (wk : Disjoint W K) (wm : Disjoint W M) (km : Disjoint K M)
    (hw : 1 ≤ W.card) (hk : 2 ≤ K.card) (hm : 2 ≤ M.card)
    (sizeP : S.card = W.card+K.card+x) (sizeQ : T.card = W.card+M.card+y)
    (sizeR : U.card = K.card+M.card+z)
    (pq : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (pr : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(R.pt j l,R.pt j (!l)))
    (qr : ∀ i j k l, s(Q.pt i k,Q.pt i (!k)) ≠ s(R.pt j l,R.pt j (!l))) :
    ∃ H : Finset (Fin n), Covers P.pt H ∧ Covers Q.pt H ∧ Covers R.pt H ∧
      H.card+r+s+t ≤ W.card+K.card+M.card+x+y+z+2 := by
  classical
  let good (d : ℕ) := ∃ H : Finset (Fin n), Covers P.pt H ∧ Covers Q.pt H ∧ Covers R.pt H ∧ H.card=d
  have baseline {u : ℕ} (pts : Fin u → Bool → Fin n) :
      ∃ H : Finset (Fin n), Covers pts H ∧ H.card ≤ u := by
    let H := Finset.univ.image (fun i => pts i false)
    exact ⟨H,fun i => ⟨false,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,
      by simpa [H] using Finset.card_image_le (s := (Finset.univ : Finset (Fin u))) (f := fun i => pts i false)⟩
  obtain ⟨A,pa,ca⟩ := baseline P.pt
  obtain ⟨B,qb,cb⟩ := baseline Q.pt
  obtain ⟨D,rd,cd⟩ := baseline R.pt
  let E := (A∪B)∪D
  have start : good E.card := by
    refine ⟨E,?_,?_,?_,rfl⟩
    · intro i; obtain ⟨k,h⟩ := pa i; exact ⟨k,Finset.mem_union_left _ (Finset.mem_union_left _ h)⟩
    · intro i; obtain ⟨k,h⟩ := qb i; exact ⟨k,Finset.mem_union_left _ (Finset.mem_union_right _ h)⟩
    · intro i; obtain ⟨k,h⟩ := rd i; exact ⟨k,Finset.mem_union_right _ h⟩
  let existsCost : ∃ d, good d := ⟨_,start⟩
  let cost := Nat.find existsCost
  obtain ⟨H,hp,hq,hr,hcard⟩ := Nat.find_spec existsCost
  have minCost (F : Finset (Fin n)) (p : Covers P.pt F) (q : Covers Q.pt F) (r : Covers R.pt F) :
      cost ≤ F.card := Nat.find_min' existsCost ⟨_,p,q,r,rfl⟩
  have upper : cost ≤ r+s+t := by
    have a := Finset.card_union_le A B
    have b := Finset.card_union_le (A∪B) D
    have c := Nat.find_min' existsCost start
    change cost ≤ (A∪B∪D).card at c
    omega
  have mAC (F pm rm qm) := minCost F pm qm rm
  have mBC (F qm rm pm) := minCost F pm qm rm
  have mBA (F qm pm rm) := minCost F pm qm rm
  have mCA (F rm pm qm) := minCost F pm qm rm
  have ab := component_pair cl P Q R four ws wt (by omega) (by omega) (by omega) pq minCost upper
  have ac := component_pair cl P R Q four ks ku (by omega) (by omega) (by omega) pr mAC (by omega : cost ≤ r+t+s)
  have bc := component_pair cl Q R P four mt mu (by omega) (by omega) (by omega) qr mBC (by omega : cost ≤ s+t+r)
  have sa := component_small cl P Q R four ws wt ks ku wk pq pr minCost
  have sb := component_small cl Q P R four wt ws mt mu wm (fun i j k l => Ne.symm (pq j i l k)) qr mBA
  have sc := component_small cl R P Q four ku ks mu mt km (fun i j k l => Ne.symm (pr j i l k))
    (fun i j k l => Ne.symm (qr j i l k)) mCA
  have power {F : Finset L} {m : ℕ} (V : Rows cl G C F m) : 2^m ≤ F.card := by
    simpa using (V.pack cl (Finset.Subset.refl _ : F ⊆ F)).power
  have main := charge W.card K.card M.card x y z r s t (r+s+t-cost) hw hk hm
    (by simpa [← sizeP] using power P) (by simpa [← sizeQ] using power Q)
    (by simpa [← sizeR] using power R)
    (by simpa [← sizeP,← sizeQ] using ab)
    (by simpa [← sizeP,← sizeR,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ac)
    (by simpa [← sizeQ,← sizeR,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using bc)
    (by simpa [← sizeP] using sa)
    (by simpa [← sizeQ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using sb)
    (by simpa [← sizeR,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using sc)
  exact ⟨H,hp,hq,hr,by omega⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
