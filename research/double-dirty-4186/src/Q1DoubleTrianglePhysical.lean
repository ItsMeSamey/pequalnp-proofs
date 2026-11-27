import Q1DoublePrivatePhysical
import Q1DoubleTriangleEndpoint
import Q1PrivateSignal
import Q1DoublePhysicalPrice
import Q1DoubleOccurrenceSemantics
import DDRegionClauses
import DDGuardClauses

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership


def pinStep (n : ℕ) (C : Circuit) (i j : ℕ) : Prop := ∃ b, opnd C j b = n+i

noncomputable def upstream (n : ℕ) (C : Circuit) (A : Finset ℕ) (g : ℕ) : Finset ℕ := by
  classical
  exact A.filter fun i => Relation.ReflTransGen (fun i j => j ∈ A ∧ pinStep n C i j) i g

theorem upstream_occurrences {n : ℕ} (C : Circuit) (A : Finset ℕ) (g : ℕ) :
    occurrences n C (upstream n C A g) ⊆ occurrences n C A := by
  classical
  rintro ⟨j,b⟩ hp
  obtain ⟨pin,out⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨inside,bmem⟩ := Finset.mem_product.mp pin
  obtain ⟨ja,path⟩ := Finset.mem_filter.mp inside
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_product.mpr ⟨ja,bmem⟩,?_⟩
  intro intra
  obtain ⟨i,ia,wire⟩ := (Finset.mem_filter.mp intra).2
  have below : Relation.ReflTransGen (fun i j => j ∈ A ∧ pinStep n C i j) i g :=
    (Relation.ReflTransGen.single (r := fun i j => j ∈ A ∧ pinStep n C i j) ⟨ja,b,wire⟩).trans path
  apply out
  exact Finset.mem_filter.mpr ⟨pin,i,Finset.mem_filter.mpr ⟨ia,below⟩,wire⟩

theorem disjoint_occurrences {n : ℕ} {C : Circuit} {A B : Finset ℕ} (dis : Disjoint A B) :
    Disjoint (occurrences n C A) (occurrences n C B) := by
  apply Finset.disjoint_left.mpr
  intro p ha hb
  exact Finset.disjoint_left.mp dis
    (Finset.mem_product.mp (Finset.mem_sdiff.mp ha).1).1
    (Finset.mem_product.mp (Finset.mem_sdiff.mp hb).1).1

theorem upstream_two {n : ℕ} {C : Circuit} (A : Finset ℕ) {g : ℕ} (hg : g ∈ A)
    (back : ∀ j ∈ A, ∀ b, opnd C j b < n+j) : 2 ≤ (occurrences n C (upstream n C A g)).card := by
  classical
  apply two_boundary
  · exact ⟨g,Finset.mem_filter.mpr ⟨hg,Relation.ReflTransGen.refl⟩⟩
  · intro j hj
    exact back _ (Finset.mem_filter.mp hj).1

theorem guard_nonempty {n : ℕ} {C : Circuit} (A : Finset ℕ) (ne : A.Nonempty)
    (back : ∀ j ∈ A, ∀ b, opnd C j b < n+j) (m : Pin) (hm : m ∈ occurrences n C A) :
    1 ≤ ((occurrences n C A).erase m).card := by
  have h := two_boundary A ne back
  have he := Finset.card_erase_add_one hm
  omega

def raw {n : ℕ} (C : Circuit) (p : Pin) : Finset (Fin n) := orIn n C (opnd C p.1 p.2)

structure Signal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset Pin) (term : (Fin n → Bool) → Bool) : Prop where
  below : ∀ x, term x = true → graphFun G ∅ x = true
  sem : ∀ x, term x = true ↔ ∀ p ∈ S, ∃ i ∈ raw C p, x i = true
  anchor : ∀ p ∈ S, ∀ a ∈ raw (n:=n) C p, ∀ b ∈ raw (n:=n) C p, a ≠ b →
    ∃ z, ∀ v ∈ raw C p, G.Adj z v ∧ s(z,v) ∈ starEdges G C

theorem rows_of_signal {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (S : Finset Pin) (term : (Fin n → Bool) → Bool)
    (signal : Signal G C S term) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (assigned : ∀ e ∈ E, AcceptPair term e) :
    ∃ P : Rows (raw C) G C S E.card,
      ∀ i, (E.equivFin.symm i).val = s(P.pt i false,P.pt i true) := by
  classical
  let A := asClauses (raw (n:=n) C) S
  let Z : Fin 0 → Private.Clause n := Fin.elim0
  obtain ⟨P,hp⟩ := Private.batch_of_signal four A Z E sub term assigned signal.below (by
    intro x
    rw [signal.sem]
    constructor
    · intro all c
      cases c with
      | inr j => exact Fin.elim0 j
      | inl i => exact all _ (S.equivFin.symm i).property
    · intro all p hp
      simpa [Private.literals,A,asClauses] using all (.inl (S.equivFin ⟨p,hp⟩))) (by
    intro c
    cases c with
    | inr j => exact Fin.elim0 j
    | inl i => exact signal.anchor _ (S.equivFin.symm i).property)
  let R : Rows (raw C) G C S E.card := {
    pt := P.pt, edges := P.edges, res := P.res, sep := P.sep, induced := P.induced
    hits := by
      intro p hp i
      simpa [Private.literals,A,asClauses] using P.hits (.inl (S.equivFin ⟨p,hp⟩)) i
    clean := by
      intro T h
      apply P.clean T
      intro c
      cases c with
      | inr j => exact Fin.elim0 j
      | inl i => exact h _ (S.equivFin.symm i).property
    anchor := signal.anchor }
  exact ⟨R,hp⟩

theorem enumerated_edges {n r : ℕ} (E : Finset (Sym2 (Fin n))) (pt : Fin r → Bool → Fin n)
    (en : ↥E ≃ Fin r) (repr : ∀ i, (en.symm i).val = s(pt i false,pt i true)) :
    Allocation.rowEdges pt = E := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact repr i ▸ (en.symm i).property
  · intro he
    apply Finset.mem_image.mpr
    exact ⟨en ⟨e,he⟩,Finset.mem_univ _,by simpa using (repr (en ⟨e,he⟩)).symm⟩

theorem exclusive_of_disjoint {n r s : ℕ} (P : Fin r → Bool → Fin n) (Q : Fin s → Bool → Fin n)
    (dis : Disjoint (Allocation.rowEdges P) (Allocation.rowEdges Q)) :
    ∀ i j k l, s(P i k,P i (!k)) ≠ s(Q j l,Q j (!l)) := by
  intro i j k l eq
  have mem {h : ℕ} (pt : Fin h → Bool → Fin n) (a : Fin h) (b : Bool) :
      s(pt a b,pt a (!b)) ∈ Allocation.rowEdges pt := by
    have base := Finset.mem_image_of_mem (fun i => s(pt i false,pt i true)) (Finset.mem_univ a)
    cases b
    · exact base
    · exact Sym2.eq_swap (a:=pt a false) (b:=pt a true) ▸ base
  exact Finset.disjoint_left.mp dis (mem P i k) (eq ▸ mem Q j l)

/-- The pivot consists of the split central owner and a distinct external
owner. Shared slots are computed from the actual gate indices upstream of
the two leak gates. The common guard needs only one surviving pin. -/
theorem finish_physical {n H : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card=1) (present : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (a b guard external : Finset ℕ) (leakA leakB : ℕ) (ha : leakA ∈ a) (hb : leakB ∈ b)
    (hg : guard.Nonempty) (m : Pin) (hm : m ∈ occurrences n C guard)
    (cuts : Finset Pin) (disAB : Disjoint a b) (disGA : Disjoint guard a) (disGB : Disjoint guard b)
    (disEA : Disjoint external a) (disEB : Disjoint external b)
    (backA : ∀ j ∈ a, ∀ k, opnd C j k < n+j)
    (backB : ∀ j ∈ b, ∀ k, opnd C j k < n+j) (backG : ∀ j ∈ guard, ∀ k, opnd C j k < n+j)
    (central outer : Finset (Sym2 (Fin n))) (disE : Disjoint central outer)
    (parts : D.edges D.pivot = central ∪ outer)
    (res : D.edges D.pivot ⊆ Ustar G C) (own : central ⊆ gammaE G C H)
    (p q e : (Fin n → Bool) → Bool) (split : ∀ x, gateVal n C H x = (p x || q x))
    (extOwn : ∀ f ∈ outer, AcceptPair e f)
    (sigP : Signal G C (occurrences n C a ∪ (occurrences n C guard).erase m) p)
    (sigQ : Signal G C (occurrences n C b ∪ (occurrences n C guard).erase m) q)
    (sigR : Signal G C (occurrences n C (upstream n C a leakA) ∪
      occurrences n C (upstream n C b leakB) ∪ (occurrences n C external \ cuts)) e)
    (budget : (occurrences n C a).card + (occurrences n C b).card +
      ((occurrences n C guard).erase m).card +
      (occurrences n C external \ cuts).card+2 ≤ D.allowance D.pivot+1) : Positive G C := by
  classical
  let A := occurrences n C a
  let B := occurrences n C b
  let W := (occurrences n C guard).erase m
  let K := occurrences n C (upstream n C a leakA)
  let M := occurrences n C (upstream n C b leakB)
  let Z := occurrences n C external \ cuts
  have ka : K ⊆ A := upstream_occurrences C a leakA
  have mb : M ⊆ B := upstream_occurrences C b leakB
  have wa : Disjoint W A := (disjoint_occurrences disGA).mono_left (Finset.erase_subset _ _)
  have wb : Disjoint W B := (disjoint_occurrences disGB).mono_left (Finset.erase_subset _ _)
  have km : Disjoint K M := (disjoint_occurrences disAB).mono ka mb
  have zk : Disjoint Z K := (disjoint_occurrences disEA).mono (Finset.sdiff_subset) ka
  have zm : Disjoint Z M := (disjoint_occurrences disEB).mono (Finset.sdiff_subset) mb
  have wk := wa.mono_right ka
  have wm := wb.mono_right mb
  have hw : 1 ≤ W.card := guard_nonempty guard hg backG m hm
  have hk : 2 ≤ K.card := upstream_two a ha backA
  have hl : 2 ≤ M.card := upstream_two b hb backB
  obtain ⟨L,R,lr,union,_,actL,actR⟩ := partitionProjected G C central own p q split
  have cc : central ⊆ Ustar G C := fun f hf => res (parts ▸ Finset.mem_union_left _ hf)
  have sr : outer ⊆ Ustar G C := fun f hf => res (parts ▸ Finset.mem_union_right _ hf)
  have lc : L ⊆ central := fun f hf => union ▸ Finset.mem_union_left _ hf
  have rc : R ⊆ central := fun f hf => union ▸ Finset.mem_union_right _ hf
  obtain ⟨P,ep⟩ := rows_of_signal four _ p sigP L (lc.trans cc) actL
  obtain ⟨Q,eq⟩ := rows_of_signal four _ q sigQ R (rc.trans cc) actR
  obtain ⟨F,ef⟩ := rows_of_signal four _ e sigR outer sr extOwn
  have pl := enumerated_edges L P.pt L.equivFin ep
  have qr := enumerated_edges R Q.pt R.equivFin eq
  have fe := enumerated_edges outer F.pt outer.equivFin ef
  have lhs := Finset.card_sdiff_add_card_eq_card ka
  have rhs := Finset.card_sdiff_add_card_eq_card mb
  have psize : (A∪W).card = W.card+K.card+(A \ K).card := by
    rw [Finset.card_union_of_disjoint wa.symm]; omega
  have qsize : (B∪W).card = W.card+M.card+(B \ M).card := by
    rw [Finset.card_union_of_disjoint wb.symm]; omega
  have fsize : (K∪M∪Z).card = K.card+M.card+Z.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨zk.symm,zm.symm⟩),
      Finset.card_union_of_disjoint km]
  obtain ⟨V,cP,cQ,cF,price⟩ := triangle_cover (raw C) P Q F four
    Finset.subset_union_right Finset.subset_union_right
    (ka.trans Finset.subset_union_left) (Finset.subset_union_left.trans Finset.subset_union_left)
    (mb.trans Finset.subset_union_left) (Finset.subset_union_right.trans Finset.subset_union_left)
    wk wm km hw hk hl psize qsize fsize
    (exclusive_of_disjoint _ _ (by rwa [pl,qr]))
    (exclusive_of_disjoint _ _ (by rw [pl,fe]; exact disE.mono_left lc))
    (exclusive_of_disjoint _ _ (by rw [qr,fe]; exact disE.mono_left rc))
  have cL := Allocation.coversRowEdges P.pt V cP
  have cR := Allocation.coversRowEdges Q.pt V cQ
  have cE := Allocation.coversRowEdges F.pt V cF
  rw [pl] at cL
  rw [qr] at cR
  rw [fe] at cE
  apply D.finishIncremental four edge least form one present paid res
  intro T _
  refine ⟨V,?_,?_⟩
  · intro u v mem
    rw [parts,← union] at mem
    rcases Finset.mem_union.mp mem with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (cL u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
      · exact (cR u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
    · exact (cE u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
  · have card := Finset.card_union_le T V
    have edgeCard := Finset.card_union_of_disjoint disE
    have centralCard := Finset.card_union_of_disjoint lr
    rw [union] at centralCard
    change V.card+L.card+R.card+outer.card ≤ W.card+K.card+M.card+(A \ K).card+(B \ M).card+Z.card+2 at price
    have vPrice : V.card + central.card + outer.card ≤ A.card+B.card+W.card+Z.card+2 := by
      rw [centralCard]
      omega
    rw [parts,edgeCard]
    exact (by omega : (T ∪ V).card + (central.card + outer.card) ≤ T.card + (A.card+B.card+W.card+Z.card+2)).trans
      (Nat.add_le_add_left budget T.card)

/-- The external region has two distinct cut pins, one for each leaked
subtree. Its remaining private occurrences may be empty. -/
theorem physical_price {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (a b g e : Finset ℕ) (ra rb h t : ℕ) (m u v : Pin)
    (raMem : ra ∈ a) (rbMem : rb ∈ b) (hMem : h ∈ g) (tMem : t ∈ e)
    (useA : ∀ j ∈ a.erase ra, ∃ p ∈ pins a, opnd C p.1 p.2=n+j)
    (useB : ∀ j ∈ b.erase rb, ∃ p ∈ pins b, opnd C p.1 p.2=n+j)
    (useG : ∀ j ∈ g.erase h, ∃ p ∈ pins g, opnd C p.1 p.2=n+j)
    (useE : ∀ j ∈ e.erase t, ∃ p ∈ pins e, opnd C p.1 p.2=n+j)
    (hm : m ∈ occurrences n C g) (hu : u ∈ occurrences n C e) (hv : v ∈ occurrences n C e)
    (uv : u ≠ v) (disAB : Disjoint a b) (disG : Disjoint (a∪b) (g.erase h))
    (disE : Disjoint (a∪b∪g.erase h) (e.erase t))
    (dirty : a∪b∪g.erase h∪e.erase t ⊆ D.dirty D.pivot)
    (topH : h ∈ D.roots D.pivot) (topT : t ∈ D.roots D.pivot) (ne : t ≠ h) :
    (occurrences n C a).card+(occurrences n C b).card+((occurrences n C g).erase m).card+
      (occurrences n C e \ {u,v}).card+2 ≤ D.allowance D.pivot+1 := by
  classical
  have cut : ({u,v} : Finset Pin) ⊆ occurrences n C e := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have price := physical_mixer_price n C {t} a b g (D.dirty D.pivot) (D.roots D.pivot)
    (fun _ => e) ra rb h (fun i => i) m (fun _ => {u,v}) raMem rbMem hMem
    (by intro i hi; simpa using (Finset.mem_singleton.mp hi ▸ tMem))
    useA useB useG (by intro i hi; simpa [Finset.mem_singleton.mp hi] using useE)
    hm (fun _ _ => cut) (by simp) disAB disG (by simpa using disE)
    (by simpa using dirty) topH (by simpa using ne) (by simpa using topT)
    (fun _ _ _ _ eq => eq)
  simpa [Allocation.allowance,uv,Nat.add_assoc] using price

/-- The raw head and guard terms have disjoint physical pin banks but can
be joined by a projection AND; repeated raw supports pose no issue. -/
theorem union_signal {n : ℕ} {C : Circuit} (S T : Finset Pin)
    (a b : (Fin n → Bool) → Bool)
    (ha : ∀ x, a x = true ↔ ∀ p ∈ S, ∃ i ∈ raw C p, x i = true)
    (hb : ∀ x, b x = true ↔ ∀ p ∈ T, ∃ i ∈ raw C p, x i = true) :
    ∀ x, (a x && b x) = true ↔ ∀ p ∈ S∪T, ∃ i ∈ raw C p, x i=true := by
  intro x
  rw [Bool.and_eq_true,ha,hb]
  exact ⟨fun h p hp => (Finset.mem_union.mp hp).elim (h.1 p) (h.2 p),
    fun h => ⟨fun p hp => h p (Finset.mem_union_left _ hp),fun p hp => h p (Finset.mem_union_right _ hp)⟩⟩

open PEqualNP.Outside.L_meta_4186_aux Q0.Factor S4183.S98 in
theorem central_signals {n m a b H : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (mix : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (four : NoFourCycle G)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (top : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (aDirty : a ∈ junk G C) (bDirty : b ∈ junk G C)
    (pm : (gateAt C m).inputs = [n+a,n+b]) :
    ∃ g ∈ leaves n C H, ∃ p q,
      Signal G C (leaves n C a ∪ (leaves n C H).erase g) p ∧
      Signal G C (leaves n C b ∪ (leaves n C H).erase g) q ∧
      ∀ x, gateVal n C H x = (p x || q x) := by
  have htop : BelowF G C H := by
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at top
    exact top.2.2
  classical
  obtain ⟨g,hg,_,hguard⟩ := guard_clause_decomposition mix edge least form top affected
  let guard := (leaves n C H).erase g
  obtain ⟨_,_,gplain,gval⟩ := hguard
  have mv (x : Fin n → Bool) : gateVal n C m x = (gateVal n C a x || gateVal n C b x) := by
    exact W_or n C x m (mixer_info mix).1 (mixer_info mix).2.1 (n+a) (n+b) pm
      (least.1.2.1 m (mixer_info mix).1 _ (by simp [pm]))
      (least.1.2.1 m (mixer_info mix).1 _ (by simp [pm]))
  let term (i : ℕ) (x : Fin n → Bool) := gateVal n C i x && clauseConjunction n C guard x
  have split (x) : gateVal n C H x = (term a x || term b x) := by
    rw [gval,mv]
    change ((gateVal n C a x || gateVal n C b x) && clauseConjunction n C guard x) = _
    dsimp only [term]
    cases gateVal n C a x <;> cases gateVal n C b x <;> cases clauseConjunction n C guard x <;> rfl
  have signal {i : ℕ} (dirty : i ∈ junk G C) (arm : n+i ∈ (gateAt C m).inputs)
      (sound : ∀ x, term i x = true → gateVal n C H x=true) :
      Signal G C (leaves n C i ∪ guard) (term i) := by
    obtain ⟨bound,op,_⟩ := (S4183.junk_iff G C i).mp dirty
    have rawA := arm_boundary_plain mix least.1 arm
    refine ⟨fun x hx => htop x (sound x hx),?_,?_⟩
    · apply union_signal (leaves n C i) guard (gateVal n C i) (clauseConjunction n C guard)
      · exact region_clause_semantics mix least.1 form bound op rawA
      · intro x
        simp [clauseConjunction,raw,leafSupport]
    · intro p hp x hx y hy ne
      apply region_clause_stars mix four least (leaves n C i ∪ guard)
        (fun z hz => (Finset.mem_union.mp hz).elim (rawA z) (gplain z))
        _ (Finset.mem_image_of_mem _ hp) x hx y hy ne
  exact ⟨g,hg,term a,term b,signal aDirty (by simp [pm]) (fun x h => by simp [split,h]),
    signal bDirty (by simp [pm]) (fun x h => by simp [split,h]),split⟩

open PEqualNP.Outside.L_meta_4186_aux Q0.Factor in
theorem external_signal {n m t : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (mix : DoubleDirty G C m) (four : NoFourCycle G) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (top : t ∈ tops G C)
    (external : ¬ Influence n C m (n+t)) :
    Signal G C (leaves n C t) (gateVal n C t) := by
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at top
  classical
  have h := top
  have plain := external_plain least.1 external
  refine ⟨h.2.2,region_clause_semantics mix least.1 form h.1 h.2.1 plain,?_⟩
  intro p hp a ha b hb ne
  exact region_clause_stars mix four least _ plain _ (Finset.mem_image_of_mem _ hp) a ha b hb ne

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
