import Q1DoubleTriangleEndpoint
import Q1DoubleOneLeakPair

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4186_aux.Q1Double

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {L : Type*} [DecidableEq L] {cl : L → Private.Clause n}

theorem rowCount {S : Finset L} {r : ℕ} (P : Triangle.Rows cl G C S r) :
    (rowEdges P.pt).card = r := by
  classical
  have inject : Function.Injective (fun i => s(P.pt i false,P.pt i true)) := by
    intro i j same
    by_contra ne
    rcases Sym2.eq_iff.mp same with eq | eq
    · exact P.sep i j ne false false eq.1
    · exact P.sep i j ne false true eq.1
  simp only [rowEdges,Finset.card_image_of_injective _ inject,Finset.card_univ,Fintype.card_fin]

theorem rowOption {S T W : Finset L} {r h : ℕ} (P : Triangle.Rows cl G C S r)
    (Q : Triangle.Rows cl G C T h) (four : NoFourCycle G) (sw : W ⊆ S) (tw : W ⊆ T)
    (hw : 0 < W.card) (hs : W.card < S.card) (ht : W.card < T.card)
    (ex : ∀ i j b d, s(P.pt i b,P.pt i (!b)) ≠ s(Q.pt j d,Q.pt j (!d))) :
    ∃ gain ∈ OneLeak.pairOptions S.card T.card W.card r h, ∃ F,
      OneLeak.covers F (rowEdges P.pt) ∧ OneLeak.covers F (rowEdges Q.pt) ∧ F.card+gain ≤ r+h := by
  have sCount := Finset.card_sdiff_add_card_eq_card sw
  have tCount := Finset.card_sdiff_add_card_eq_card tw
  have repr {m : ℕ} (p : Fin m → Bool → Fin n) :
      ∀ e ∈ rowEdges p, ∃ i, e = s(p i false,p i true) := by
    intro e he
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp he
    exact ⟨i,eq.symm⟩
  have opt := OneLeak.option_cover_of_batches four (P.pack cl sw) (Q.pack cl tw)
    hw (by omega) (by omega) ex (rowEdges P.pt) (rowEdges Q.pt) (repr P.pt) (repr Q.pt)
  simpa only [sCount,tCount] using opt

theorem finishLargeOneLeakRows (D : Allocation G C) (four : NoFourCycle G)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (p : OneLeak.Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z) (hb : 2 ≤ p.b) (hw : 1 ≤ p.w)
    {A B E K W : Finset L} (P : Triangle.Rows cl G C A p.r)
    (Q : Triangle.Rows cl G C B p.s) (Y : Triangle.Rows cl G C E p.h)
    (ak : K ⊆ A) (ek : K ⊆ E) (aw : W ⊆ A) (bw : W ⊆ B)
    (kCount : K.card = p.k) (wCount : W.card = p.w)
    (aCount : A.card = p.k+p.x+p.w) (bCount : B.card = p.b+p.w) (eCount : E.card = p.k+p.z)
    (pe : ∀ i j b d, s(P.pt i b,P.pt i (!b)) ≠ s(Y.pt j d,Y.pt j (!d)))
    (pq : ∀ i j b d, s(P.pt i b,P.pt i (!b)) ≠ s(Q.pt j d,Q.pt j (!d)))
    (partition : D.edges D.pivot = rowEdges P.pt ∪ rowEdges Q.pt ∪ rowEdges Y.pt)
    (exactFour : p.k=3 → p.k+p.z=4 → p.h=2 → p.r=0)
    (price : p.budget ≤ D.allowance D.pivot+1) : Positive G C := by
  have pow {T W' : Finset L} {r : ℕ} (X : Triangle.Rows cl G C T r) (ws : W' ⊆ T) :
      2^r ≤ T.card := by
    simpa only [Finset.card_sdiff_add_card_eq_card ws] using (X.pack cl ws).power
  apply D.finishLargeOneLeak four edge least form one paid p hk hz hb hw
    (aCount ▸ pow P ak) (bCount ▸ pow Q bw) (eCount ▸ pow Y ek) _ _ _ partition
    (rowCount P) (rowCount Q) (rowCount Y) _ _ exactFour price
  · simpa only [kCount,aCount,eCount] using
      (rowOption P Y four ak ek (by omega) (by omega) (by omega) pe)
  · simpa only [wCount,aCount,bCount] using
      (rowOption P Q four aw bw (by omega) (by omega) (by omega) pq)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
