import ThresholdUpperFailedMass
import ThresholdUpperOverlapTwo
namespace ThresholdUpperActualSelection
open ThresholdUpperCatalogue ThresholdUpperSecond ThresholdUpperCollisionMass ThresholdUpperInjection
open Classical
def failCost (w z : Nat) : Nat :=
  6*(Fintype.card (Edges z)*(2*(z-2))*(Fintype.card (Edges z)-2).descFactorial (w-2))
def pairCost (w z q : Nat) : Nat :=
  (Fintype.card (Edges z)).descFactorial 4 * partitionCount q (2*q) *
    (Fintype.card (Edges z)-4-q).descFactorial (w-4-q)

noncomputable def freshEquiv {w} (Q R : Finset (Fin w)) :
    Fresh Q R ≃ ↥(R \ Q) where
  toFun x := ⟨x.val.val,Finset.mem_sdiff.mpr ⟨x.property,x.val.property⟩⟩
  invFun x := ⟨⟨x.val,(Finset.mem_sdiff.mp x.property).2⟩,(Finset.mem_sdiff.mp x.property).1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem pair_mass {w z} (F : Finset (Finset (Fin w))) (four : ∀ Q∈F,Q.card=4)
    (p : Finset (Finset (Fin w))) (hp : p∈F.powersetCard 2) :
    (Finset.univ.filter (event (z:=z) F p)).card≤
      if overlap p=2 then pairCost w z 2 else max (pairCost w z 3) (pairCost w z 4) := by
  classical
  obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp hp
  obtain ⟨Q,R,ne,pr⟩ := Finset.card_eq_two.mp sz
  have q4 := four Q (sub (by simp [pr]))
  have r4 := four R (sub (by simp [pr]))
  have op : overlap p=(Q∩R).card := by
    unfold overlap
    apply congrArg Finset.card
    ext a; simp [pr]
  let q := (R \ Q).card
  have decomp : q+overlap p=4 := by
    rw [op,Finset.inter_comm Q R]
    exact (Finset.card_sdiff_add_card_inter R Q).trans r4
  have pos : q≠0 := by
    intro zero
    have empty := Finset.card_eq_zero.mp zero
    have sub' : R⊆Q := by
      intro x hx; by_contra h
      have hit := Finset.mem_sdiff.mpr ⟨hx,h⟩
      rw [empty] at hit
      exact Finset.notMem_empty _ hit
    exact ne (Finset.eq_of_subset_of_card_le sub' (by omega)).symm
  have ok (u : Injection w z) (h : event F p u) :
      (terminal u Q).card=8 ∧ (terminal u R).card=8 ∧ terminal u R=terminal u Q := by
    obtain ⟨pool,coll⟩ := Finset.mem_filter.mp h
    have g := (Finset.mem_powersetCard.mp pool).1
    have qgood := (Finset.mem_filter.mp (g (show Q∈p by simp [pr]))).2
    have rgood := (Finset.mem_filter.mp (g (show R∈p by simp [pr]))).2
    refine ⟨Classical.not_not.mp qgood,Classical.not_not.mp rgood,?_⟩
    obtain ⟨a,ha,b,hb,ab,eq⟩ := coll
    simp only [pr,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp_all
  have fresh : Fintype.card (Fresh Q R)=q := by simpa only [Fintype.card_coe,q] using Fintype.card_congr (freshEquiv Q R)
  have rem : Fintype.card (Rest Q R)=w-4-q := by
    change Fintype.card {x : Out Q // ¬x.val∈R}=_
    rw [Fintype.card_subtype_compl]
    change Fintype.card {x : Fin w // x∉Q}-Fintype.card (Fresh Q R)=_
    rw [Fintype.card_subtype_compl]; simp [q4,fresh]
  have incl : (Finset.univ.filter (event (z:=z) F p))⊆Finset.univ.filter
      (fun u : Injection w z => (terminal u Q).card=8 ∧ (terminal u R).card=8 ∧ terminal u R=terminal u Q) :=
    fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok u (Finset.mem_filter.mp hu).2⟩
  by_cases one : q=1
  · have empty : Finset.univ.filter (event (z:=z) F p)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u h
      obtain ⟨qe,re,eq⟩ := ok u (Finset.mem_filter.mp h).2
      exact no_one Q R u q4 r4 one qe re eq
    simp [empty]
  · have est := (Finset.card_le_card incl).trans
      (mass (z:=z) Q R q4 r4 rfl (Fintype.equivFinOfCardEq fresh).symm)
    have cap : (Finset.univ.filter (event (z:=z) F p)).card≤pairCost w z q := by
      simpa [pairCost,Fintype.card_embedding_eq,q4,fresh,rem] using est
    by_cases ov : overlap p=2
    · simpa [ov,show q=2 by omega] using cap
    · rw [if_neg ov]
      rcases (show q=3 ∨ q=4 by omega) with h|h
      · exact cap.trans (h ▸ le_max_left _ _)
      · exact cap.trans (h ▸ le_max_right _ _)

theorem two_family {w} (F : Finset (Finset (Fin w))) :
    (F.powersetCard 2).filter (fun p => overlap p=2)=ThresholdUpperOverlapTwo.overlapTwo F := by
  classical
  have val (a b : Finset (Fin w)) : overlap {a,b}=(a∩b).card := by
    unfold overlap
    apply congrArg Finset.card
    ext i; simp
  ext p
  simp only [ThresholdUpperOverlapTwo.overlapTwo,Finset.mem_filter]
  constructor
  · rintro ⟨hp,ov⟩
    obtain ⟨a,b,_,eq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
    exact ⟨hp,a,b,eq,by simpa [eq,val] using ov⟩
  · rintro ⟨hp,a,b,rfl,ov⟩; exact ⟨hp,(val a b).trans ov⟩

theorem second {w z v k n : Nat} (G : FirstGraph (Finset.univ : Finset (Fin w)) v k)
    (room : w≤Fintype.card (Edges z))
    (budget :
      let P := G.F.powersetCard 2
      let T := P.filter (fun p => overlap p=2)
      Fintype.card (Injection w z)*n+G.F.card*failCost w z+
        T.card*pairCost w z 2+(P \ T).card*max (pairCost w z 3) (pairCost w z 4)
        ≤Fintype.card (Injection w z)*G.F.card) :
    ∃ u : Injection w z,n≤((goodBoxes G.F u).image (terminal u)).card := by
  classical
  have nonempty : Nonempty (Injection w z) := ⟨(Fin.castLEEmb room).trans
    (Fintype.equivFin (Edges z)).symm.toEmbedding⟩
  have four Q (h : Q∈G.F) := (Finset.mem_powersetCard.mp (G.four h)).2
  apply select_second G nonempty 1 (failCost w z) (pairCost w z 2)
    (max (pairCost w z 3) (pairCost w z 4)) (by decide)
  · intro Q h
    simpa [failCost] using ThresholdUpperFailedMass.failed_mass (z:=z) Q (four Q h)
  · intro p hp ov
    simpa [ov] using pair_mass (z:=z) G.F four p hp
  · intro p hp ov
    simpa [ov] using pair_mass (z:=z) G.F four p hp
  · simpa [Nat.add_assoc] using budget

theorem second_layers {w z v k n : Nat} (G : FirstGraph (Finset.univ : Finset (Fin w)) v k)
    (room : w≤Fintype.card (Edges z))
    (budget :
      let P := G.F.powersetCard 2
      let T := P.filter (fun p => overlap p=2)
      Fintype.card (Injection w z)*n+G.F.card*failCost w z+
        T.card*pairCost w z 2+(P \ T).card*max (pairCost w z 3) (pairCost w z 4)
        ≤Fintype.card (Injection w z)*G.F.card) :
    ∃ v'≤v,∃ w'≤w,∃ z'≤z,Nonempty (ThresholdThreeLayerUpper.Layers n v' w' z') :=
  select_layers G (second G room budget)
end ThresholdUpperActualSelection
