import Q1DoubleTrianglePhysical
import Q1DoubleOneLeakPhysical
import Q1DoubleOneLeakTight
import Q1DoubleRowsEndpoint
import Q1DoubleSmallLeakEndpoint
import Q1DoublePrivateEndpoint
import Q1PrivateEnumerate

-- Source: DDOneLeakRowTight.lean (SHA-256 9a2a46b304143685328161d4b378875ff74222d7698ea2863babac480e19a687)
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds Triangle Allocation

/-- All tight consequences for one external root from actual rows and shared pin
inclusions. The first alternative supplies a cover even for an empty fresh batch. -/
theorem row_tight {n r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {L : Type*} [DecidableEq L] {cl : L → Private.Clause n} {S E K : Finset L}
    (P : Rows cl G C S r) (Y : Rows cl G C E 2) (four : NoFourCycle G)
    (size : E.card=4) (ks : K ⊆ S) (ke : K ⊆ E) (many : 2 ≤ K.card)
    (ex : ∀ i j b c, s(P.pt i b,P.pt i (!b)) ≠ s(Y.pt j c,Y.pt j (!c))) :
    (r ≤ 1 ∧ ∃ V : Finset (Fin n), covers V (rowEdges P.pt) ∧ covers V (rowEdges Y.pt) ∧ V.card ≤ 2) ∧
    (3 ≤ K.card → r=0) := by
  classical
  let ix (i : Bool) : Fin 2 := if i then 1 else 0
  let label (t : Pos) := Y.pt (ix t.1) t.2
  have inj : Function.Injective label := by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    have ij : i=j := by by_contra ne; exact Y.sep _ _ (by cases i <;> cases j <;> simp_all [ix]) b c eq
    subst j
    have bc : b=c := by
      by_contra ne
      have e : c=(!b) := by cases b <;> cases c <;> simp_all
      subst c
      exact G.ne_of_adj (Y.edges (ix i) b) eq
    subst c; rfl
  let idx : Fin 4 ≃ ↥E := (finCongr size.symm).trans E.equivFin.symm
  let lits (j : Fin 4) := cl (idx j).val
  let J := Finset.univ.filter (fun j : Fin 4 => (idx j).val ∈ K)
  have jc : J.card=K.card := by
    let f : ↥J ≃ ↥K := {
      toFun := fun j => ⟨(idx j.val).val,(Finset.mem_filter.mp j.property).2⟩
      invFun := fun k => ⟨idx.symm ⟨k.val,ke k.property⟩,by simp [J,k.property]⟩
      left_inv := by intro j; apply Subtype.ext; simp
      right_inv := by intro k; apply Subtype.ext; simp }
    simpa using Fintype.card_congr f
  have ind (x y : Bool) := Y.induced (ix false) (ix true) (by decide) x y
  obtain ⟨T,tc,hit⟩ := physical_four four label inj lits J
    (fun j i => Y.hits _ (idx j).property (ix i))
    (fun V hh => Y.clean V (fun c hc => by simpa [lits] using hh (idx.symm ⟨c,hc⟩)))
    ind (fun i b => Y.edges (ix i) b) (fun i b => Y.res (ix i) b)
    (fun j => Y.anchor _ (idx j).property)
  let fresh (a b : Fin n) := ∃ i, a=P.pt i false ∧ b=P.pt i true
  have sound : ∀ a b, fresh a b → G.Adj a b := by rintro a b ⟨i,rfl,rfl⟩; exact P.edges i false
  have alone : ∀ p q, ¬fresh (label p) (label q) := by
    apply exclusive_external G label fresh sound
    · intro p q ne
      exact Y.induced _ _ (by rcases p with ⟨i,b⟩; rcases q with ⟨j,c⟩; cases i <;> cases j <;> simp_all [ix]) _ _
    · rintro i b ⟨j,h₁,h₂⟩
      exact ex j (ix i) false b (by
        change s(P.pt j false,P.pt j true) = s(label (i,b),label (i,!b))
        rw [h₁,h₂])
  have meets : ∀ a b, fresh a b → ∀ t ∈ T, inSlot label t a ∨ inSlot label t b := by
    rintro a b ⟨i,rfl,rfl⟩
    apply hit
    intro j hj
    exact P.hits _ (ks (Finset.mem_filter.mp hj).2) i
  have three : 3 ≤ K.card → r=0 := by
    intro big
    by_contra ne
    have triple : ∀ X : Finset Pattern, 3 ≤ X.card → ∃ a∈X, ∃ b∈X, ∃ c∈X, a≠b ∧ a≠c ∧ b≠c := by decide
    obtain ⟨a,ha,b,hb,c,hc,ab,ac,bc⟩ := triple T (by omega)
    let i : Fin r := ⟨0,by omega⟩
    exact three_shared_impossible inj alone meets ha hb hc ab ac bc _ _ ⟨i,rfl,rfl⟩
  refine ⟨?_,three⟩
  have pair : ∀ X : Finset Pattern, 2 ≤ X.card → ∃ a∈X, ∃ b∈X, a≠b := by decide
  obtain ⟨a,ha,b,hb,ab⟩ := pair T (by omega)
  have hub : ∃ p, ∀ x y, fresh x y → label p=x ∨ label p=y := by
    by_cases e : ∃ x y, fresh x y
    · exact two_shared_hub inj alone meets ha hb ab e
    · exact ⟨(false,false),fun x y h => (e ⟨x,y,h⟩).elim⟩
  obtain ⟨p,hp⟩ := hub
  obtain ⟨V,small,ycov,pcov⟩ := cover_four_and_hub label fresh p hp
  refine ⟨hub_matching_card P.pt _ P.sep (fun i => hp _ _ ⟨i,rfl,rfl⟩),V,?_,?_,small⟩
  · apply coversRowEdges
    intro i
    rcases pcov _ _ ⟨i,rfl,rfl⟩ with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · apply coversRowEdges
    intro i
    have repr : ∃ b, i=ix b := by fin_cases i <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩
    obtain ⟨b,rfl⟩ := repr
    rcases ycov b with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

-- Source: DDOneLeakFinishRows.lean (SHA-256 79fb11f46464ac7717fcbc910738b9004a4852afd82c4e76231a519843cf1ce6)
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds Triangle Allocation
open PEqualNP.Outside.L_meta_4186_aux

theorem finishRows {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {L : Type*} [DecidableEq L] {cl : L → Private.Clause n} (D : Allocation G C)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (one : (orN G C \ lam G C).card=1)
    (present : D.pivot∈D.components) (paid : ∀ i∈D.components.erase D.pivot,D.Local i)
    (res : D.edges D.pivot ⊆ Ustar G C) (R S H : Finset (Sym2 (Fin n)))
    (parts : D.edges D.pivot=R∪S∪H) (rs : Disjoint R S) (rh : Disjoint R H)
    (A B W E K : Finset L) (ka : K ⊆ A) (ke : K ⊆ E)
    (aw : Disjoint A W) (bw : Disjoint B W) (hk : 2≤K.card) (hw : 1≤W.card)
    (hb : 2≤B.card) (hz : 1≤(E \ K).card)
    (P : Rows cl G C (A∪W) R.card) (Q : Rows cl G C (B∪W) S.card)
    (Y : Rows cl G C E H.card)
    (pr : ∀ i, (R.equivFin.symm i).val=s(P.pt i false,P.pt i true))
    (qr : ∀ i, (S.equivFin.symm i).val=s(Q.pt i false,Q.pt i true))
    (yr : ∀ i, (H.equivFin.symm i).val=s(Y.pt i false,Y.pt i true))
    (price : A.card+B.card+W.card+(E \ K).card+1≤D.allowance D.pivot+1) : Positive G C := by
  classical
  have pl := enumerated_edges R P.pt R.equivFin pr
  have ql := enumerated_edges S Q.pt S.equivFin qr
  have yl := enumerated_edges H Y.pt H.equivFin yr
  have pq := exclusive_of_disjoint P.pt Q.pt (by rwa [pl,ql])
  have py := exclusive_of_disjoint P.pt Y.pt (by rwa [pl,yl])
  have ca := Finset.card_sdiff_add_card_eq_card ka
  have ce := Finset.card_sdiff_add_card_eq_card ke
  have cas := Finset.card_union_of_disjoint aw
  have cbs := Finset.card_union_of_disjoint bw
  have kas : K ⊆ A∪W := ka.trans Finset.subset_union_left
  have applyTight {k : ℕ} (Y' : Rows cl G C E k) (yk : k=2) (sz : E.card=4)
      (ex : ∀ i j b c, s(P.pt i b,P.pt i (!b)) ≠ s(Y'.pt j c,Y'.pt j (!c))) :
      (R.card ≤ 1 ∧ ∃ V, covers V (rowEdges P.pt) ∧ covers V (rowEdges Y'.pt) ∧ V.card≤2) ∧
      (3≤K.card → R.card=0) := by
    subst k
    exact row_tight P Y' four sz kas ke hk ex
  have tight (two : H.card=2) (sz : E.card=4) :
      (R.card ≤ 1 ∧ ∃ V, covers V R ∧ covers V H ∧ V.card≤2) ∧ (3≤K.card → R.card=0) := by
    simpa only [pl,yl] using applyTight Y two sz py
  by_cases large : 3≤K.card
  · let p : Profile := ⟨K.card,(A \ K).card,(E \ K).card,B.card,W.card,R.card,S.card,H.card⟩
    apply D.finishLargeOneLeakRows four edge least form one paid p large hz hb hw P Q Y
      kas ke Finset.subset_union_right Finset.subset_union_right rfl rfl
    · dsimp [p]; omega
    · exact cbs
    · dsimp [p]; omega
    · exact py
    · exact pq
    · rwa [pl,ql,yl]
    · intro k z h
      apply (tight h (by dsimp [p] at z; omega)).2 large
    · dsimp [Profile.budget,p]; omega
  · have k2 : K.card=2 := by omega
    have y3 : 3 ≤ E.card := by omega
    let PA := P.pack cl (Finset.subset_union_right : W ⊆ A∪W)
    let QB := Q.pack cl (Finset.subset_union_right : W ⊆ B∪W)
    have minus (U : Finset L) (du : Disjoint U W) : (U∪W) \ W = U := by
      ext i
      simp only [Finset.mem_sdiff,Finset.mem_union]
      exact ⟨fun h => h.1.resolve_right h.2,fun h => ⟨Or.inl h,fun w => Finset.disjoint_left.mp du h w⟩⟩
    have aset := minus A aw
    have bset := minus B bw
    have ypow := (Y.pack cl ke).power
    have qpow := QB.power
    change 2^S.card ≤ ((B∪W) \ W).card+W.card at qpow
    rw [bset] at qpow
    apply D.finishSmallOneLeak four edge least form one present paid res A.card B.card W.card E.card
      R S H parts (by omega) y3 (fun _ => by omega) ((Q0Transversal.twice_le_pow _).trans qpow)
    · intro T outside
      obtain ⟨e,_⟩ := edge
      obtain ⟨p,hp,hq,en,eq⟩ := Private.concatenate e.out.1 R S (R∪S) rs rfl P.pt Q.pt pr qr
      have list : ∀ e∈R∪S, ∃ i<R.card+S.card, e=s(p i false,p i true) := by
        intro f hf
        obtain ⟨i,he⟩ := en.surjective ⟨f,hf⟩
        exact ⟨i,i.isLt,(congrArg Subtype.val he).symm.trans (eq i)⟩
      have ex : ∀ i<R.card+S.card, ∀ j<R.card+S.card, ∀ b c, p i b=p j c → p i (!b)=p j (!c) → i=j := by
        intro i hi j hj b c same mate
        have same' : en ⟨i,hi⟩ = en ⟨j,hj⟩ := by
          apply Subtype.ext
          rw [eq,eq]
          apply Sym2.eq_iff.mpr
          cases b <;> cases c
          · exact Or.inl ⟨same,mate⟩
          · exact Or.inr ⟨same,mate⟩
          · exact Or.inr ⟨mate,same⟩
          · exact Or.inl ⟨mate,same⟩
        exact congrArg Fin.val (en.injective same')
      obtain ⟨V,cv,card⟩ := Private.zeroLeak four (by rw [aset]; omega)
        (by rw [bset]; omega) hw PA QB p hp hq T ex (external_of_base G T _ p _ outside list)
      have cov : covers (T∪V) (R∪S) := by
        intro x y xy
        obtain ⟨i,hi,eq⟩ := list _ xy
        rcases Sym2.eq_iff.mp eq with ⟨e,f⟩ | ⟨e,f⟩
        · simpa only [e,f] using cv i hi
        · simpa only [e,f,or_comm] using cv i hi
      refine ⟨V,fun x y h => cov x y (Finset.mem_union_left S h),
        fun x y h => cov x y (Finset.mem_union_right R h),?_⟩
      simpa only [aset,bset,Nat.add_assoc] using card
    · exact fun h sz => (tight h sz).1
    · omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
