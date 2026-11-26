import ThresholdUpperFirstStage
import ThresholdUpperNormalize
import ThresholdUpperInjectionAverage
import ThresholdUpperExtension
namespace ThresholdUpperSecond
open scoped BigOperators
open ThresholdUpperCatalogue
open Classical

abbrev Edges (z : Nat) := ↥((Finset.univ : Finset (Fin z)).powersetCard 2)
abbrev Injection (w z : Nat) := Fin w ↪ Edges z
def terminal {w z} (u : Injection w z) (Q : Finset (Fin w)) := Q.biUnion (fun a => (u a).val)
def failed {w z} (Q : Finset (Fin w)) (u : Injection w z) : Prop := (terminal u Q).card≠8
noncomputable def goodBoxes {w z} (F : Finset (Finset (Fin w))) (u : Injection w z) :=
  F.filter (fun Q => ¬failed Q u)
def Crash {B X : Type*} [DecidableEq B] (key : B→X) (p : Finset B) :=
  ∃ a∈p,∃ b∈p,a≠b ∧ key a=key b
noncomputable def crashes {B X : Type*} [DecidableEq B] (good : Finset B) (key : B→X) :=
  (good.powersetCard 2).filter (Crash key)

theorem dedup {B X : Type*} [DecidableEq B] [DecidableEq X] (good : Finset B) (key : B→X) :
    good.card≤(good.image key).card+(crashes good key).card := by
  classical
  let im := good.image key
  let pick := fun x : ↥im => (Finset.mem_image.mp x.property).choose
  have ok (x : ↥im) : pick x∈good ∧ key (pick x)=x.val :=
    (Finset.mem_image.mp x.property).choose_spec
  let keep := im.attach.image pick
  have sz : keep.card ≤ im.card := by simpa [keep] using (Finset.card_image_le (s:=im.attach) (f:=pick))
  let rep := fun b => if h : key b∈im then pick ⟨_,h⟩ else b
  have repdata (b) (hb : b∈good) : rep b∈keep ∧ rep b∈good ∧ key (rep b)=key b := by
    have hit : key b∈im := Finset.mem_image_of_mem _ hb
    rw [show rep b=pick ⟨_,hit⟩ from dif_pos hit]
    exact ⟨Finset.mem_image.mpr ⟨⟨_,hit⟩,Finset.mem_attach _ _,rfl⟩,ok _⟩
  have cost : (good \ keep).card≤(crashes good key).card := by
    apply Finset.card_le_card_of_injOn (fun b => {rep b,b})
    · intro b hb
      obtain ⟨bg,no⟩ := Finset.mem_sdiff.mp hb
      obtain ⟨ins,rg,rk⟩ := repdata b bg
      have ne : rep b≠b := fun eq => no (eq ▸ ins)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨(by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rg; exact (Finset.mem_singleton.mp h) ▸ bg),by simp [ne]⟩,
        rep b,by simp,b,by simp,ne,rk⟩
    · intro a ha b hb eq
      change ({rep a,a}:Finset B)={rep b,b} at eq
      have mem : a∈({rep b,b}:Finset B) := by rw [←eq]; simp
      rcases Finset.mem_insert.mp mem with h|h
      · exact False.elim ((Finset.mem_sdiff.mp ha).2 (h.symm ▸ (repdata b (Finset.mem_sdiff.mp hb).1).1))
      · exact Finset.mem_singleton.mp h
  have cov : good⊆(good \ keep)∪keep := by
    intro b hb
    by_cases hu : b∈keep
    · exact Finset.mem_union_right _ hu
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hb,hu⟩)
  have bound := (Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  change keep.card ≤ (good.image key).card at sz
  omega

theorem layout_of_images {w z v k n : Nat}
    (G : FirstGraph (Finset.univ : Finset (Fin w)) v k) (u : Injection w z)
    (enough : n≤((goodBoxes G.F u).image (terminal u)).card) :
    ∃ v'≤v,∃ w'≤w,∃ z'≤z,Nonempty (ThresholdThreeLayerUpper.Layers n v' w' z') := by
  classical
  let D := (goodBoxes G.F u).image (terminal u)
  let select : Fin n ↪ ↥D := (Fin.castLEEmb enough).trans (Fintype.equivFinOfCardEq
    (show Fintype.card ↥D=D.card by simp)).symm.toEmbedding
  have selected (i : Fin n) := Finset.mem_image.mp (select i).property
  let q := fun i : Fin n => (selected i).choose
  have good (i) : q i∈goodBoxes G.F u := (selected i).choose_spec.1
  have eq (i) : terminal u (q i)=(select i).val := (selected i).choose_spec.2
  let Q := fun i : Fin n => (⟨q i,(Finset.mem_filter.mp (good i)).1⟩ : ↥G.F)
  let gnames : Fin v ≃ ↥G.R := (Fintype.equivFinOfCardEq (by simpa using G.edges :
    Fintype.card ↥G.R=v)).symm
  let edge := fun a : Fin v => (gnames a).val
  let first := fun i : Fin n => Finset.univ.filter (fun a => edge a∈(G.representative (Q i)).val)
  have mapped (i) : (first i).image edge=(G.representative (Q i)).val := by
    ext e
    constructor
    · intro h; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · intro h
      let a := gnames.symm ⟨e,(Finset.mem_powersetCard.mp (G.representative (Q i)).property).1 h⟩
      have ea : edge a=e := congrArg Subtype.val (gnames.apply_symm_apply _)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea.symm ▸ h⟩,ea⟩
  have size1 (i) : (first i).card=2 := by
    have ei : Function.Injective edge := fun a b h => gnames.injective (Subtype.ext h)
    rw [←Finset.card_image_of_injective _ ei,mapped]
    exact (Finset.mem_powersetCard.mp (G.representative (Q i)).property).2
  have mid (i) : (first i).biUnion edge=q i := by
    change (first i).biUnion edge=(Q i).val
    rw [←G.endpoints (Q i),←mapped]
    ext; simp
  have finish (i) : (first i).biUnion (fun a => (edge a).biUnion (fun b => (u b).val))=terminal u (q i) := by
    rw [←mid i]
    ext z
    simp only [terminal,Finset.mem_biUnion]
    constructor
    · rintro ⟨a,ha,b,hb,hz⟩; exact ⟨b,⟨a,ha,hb⟩,hz⟩
    · rintro ⟨b,⟨a,ha,hb⟩,hz⟩; exact ⟨a,ha,b,hb,hz⟩
  apply ThresholdUpperNormalize.normalize first edge (fun b => (u b).val) size1
    (fun a => (Finset.mem_powersetCard.mp (G.ambient (gnames a).property)).2)
    (fun b => (Finset.mem_powersetCard.mp (u b).property).2)
  · intro i
    rw [finish]
    exact Classical.not_not.mp (Finset.mem_filter.mp (good i)).2
  · intro i j h
    apply select.injective
    exact Subtype.ext ((eq i).symm.trans ((finish i).symm.trans (h.trans ((finish j).trans (eq j)))))

def overlap {w} (p : Finset (Finset (Fin w))) :=
  (Finset.univ.filter (fun a : Fin w => ∀ Q∈p,a∈Q)).card
def event {w z} (F : Finset (Finset (Fin w))) (p : Finset (Finset (Fin w)))
    (u : Injection w z) : Prop := p∈crashes (goodBoxes F u) (terminal u)

theorem select_second {w z v k n : Nat}
    (G : FirstGraph (Finset.univ : Finset (Fin w)) v k)
    (nonempty : Nonempty (Injection w z)) (den a b c : Nat)
    (positive : 0<den)
    (m₁ : ∀ Q∈G.F,den*(Finset.univ.filter (failed (z:=z) Q)).card≤a)
    (m₂ : ∀ p∈G.F.powersetCard 2,overlap p=2 →
      den*(Finset.univ.filter (event (z:=z) G.F p)).card≤b)
    (m₃ : ∀ p∈G.F.powersetCard 2,overlap p≠2 →
      den*(Finset.univ.filter (event (z:=z) G.F p)).card≤c)
    (budget :
      let P := G.F.powersetCard 2
      let T := P.filter (fun p => overlap p=2)
      Fintype.card (Injection w z)*den*n+
        (G.F.card*a+T.card*b+(P \ T).card*c)≤Fintype.card (Injection w z)*den*G.F.card) :
    ∃ u : Injection w z,n≤((goodBoxes G.F u).image (terminal u)).card := by
  classical
  let F := G.F
  let P := F.powersetCard 2
  let T := P.filter (fun p => overlap p=2)
  let sample := (Finset.univ : Finset (Injection w z))
  have sPos : sample.Nonempty := ⟨Classical.choice nonempty,Finset.mem_univ _⟩
  obtain ⟨u,_,debit⟩ := ThresholdUpperInjectionAverage.choose_injection sample F T (P \ T)
    failed (event F) (event F) den a b c sPos m₁
    (fun p hp => m₂ p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    (fun p hp => m₃ p (Finset.mem_sdiff.mp hp).1 (fun h =>
      (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,h⟩)))
  let good := goodBoxes F u
  let bad := F.filter (fun q => failed q u)
  have splitF : F.card=bad.card+good.card := by
    simpa [bad,good,goodBoxes] using (Finset.card_filter_add_card_filter_not
      (s:=F) (p:=fun q => failed q u)).symm
  let crash := crashes good (terminal u)
  have cin : crash⊆P := by
    intro p hp
    obtain ⟨pair,_⟩ := Finset.mem_filter.mp hp
    obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp pair
    exact Finset.mem_powersetCard.mpr ⟨sub.trans (Finset.filter_subset _ _),sz⟩
  have covered : crash⊆(T.filter (fun p => event F p u))∪((P \ T).filter (fun p => event F p u)) := by
    intro p hp
    by_cases inT : p∈T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inT,hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨cin hp,inT⟩,hp⟩)
  have loss := (Finset.card_le_card covered).trans (Finset.card_union_le _ _)
  have all := dedup good (terminal u)
  let count := Fintype.card (Injection w z)*den
  have cp : 0<count := Nat.mul_pos (Fintype.card_pos_iff.mpr nonempty) positive
  have costs : F.card≤(good.image (terminal u)).card+
      (bad.card+(T.filter (fun p => event F p u)).card+((P \ T).filter (fun p => event F p u)).card) := by
    change good.card≤_+crash.card at all
    omega
  have mul := Nat.mul_le_mul_left count costs
  simp only [Nat.mul_add] at mul
  simp only [Nat.mul_add,Finset.card_univ,sample] at debit
  refine ⟨u,Nat.le_of_mul_le_mul_left ?_ cp⟩
  change count*n≤count*(good.image (terminal u)).card
  change count*n+(F.card*a+T.card*b+(P \ T).card*c)≤count*F.card at budget
  dsimp only [count,bad] at *
  omega

theorem select_layers {w z v k n : Nat} (G : FirstGraph (Finset.univ : Finset (Fin w)) v k)
    (sel : ∃ u : Injection w z,n≤((goodBoxes G.F u).image (terminal u)).card) :
    ∃ v'≤v,∃ w'≤w,∃ z'≤z,Nonempty (ThresholdThreeLayerUpper.Layers n v' w' z') := by
  obtain ⟨u,hu⟩ := sel
  exact layout_of_images G u hu
end ThresholdUpperSecond
