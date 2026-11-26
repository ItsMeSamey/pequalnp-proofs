import ExactPlaneCoordinateSampler
namespace ExactPlanePinnedSampling
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneActivationSlice ExactPlaneDeterminant
open ExactPlaneLookupDeterminant ExactPlaneSamplerRank
variable {J P K T : Type*} [Fintype J] [DecidableEq J] [Fintype K] [Fintype T]
def Matched (test : P→Bool→Vec J →ₗ[F] F) (tag : P→Bool→F) (x : Vec J) (e : P) :=
  ∀ s,test e s x=tag e s

theorem sample (S : Finset (Vec J)) (sampling : OntoHits S (2*(Fintype.card T+2)+1))
    (anchor : T→P) (test : P→Bool→Vec J →ₗ[F] F) (tag : P→Bool→F)
    (e f : P) (a b c d : Residual J K) (x : Vec J)
    (keep : ∀ t,Matched test tag x (anchor t))
    (he : Matched test tag x e) (hf : Matched test tag x f)
    (hit : independent a.read b.read c.read d.read x) :
    ∃ l : List (Vec J), (∀ y∈l,y∈S ∧ (∀ t,Matched test tag y (anchor t)) ∧
      Matched test tag y e ∧ Matched test tag y f) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      (∀ t,Matched test tag l.sum (anchor t)) ∧ Matched test tag l.sum e ∧
      Matched test tag l.sum f ∧ independent a.read b.read c.read d.read l.sum := by
  classical
  let site : T ⊕ Bool → P := Sum.elim anchor (fun s => if s then f else e)
  let row := (T ⊕ Bool) × Bool
  have card : Fintype.card row=2*(Fintype.card T+2) := by
    simp [row,Fintype.card_prod,Fintype.card_sum,Nat.mul_comm]
  let name : row ≃ Fin (2*(Fintype.card T+2)) := Fintype.equivFinOfCardEq card
  let read := fun i => test (site (name.symm i).1) (name.symm i).2
  let target := fun i => tag (site (name.symm i).1) (name.symm i).2
  have ok (y : Vec J) : Active read 0 target y ↔
      (∀ t,Matched test tag y (anchor t)) ∧ Matched test tag y e ∧ Matched test tag y f := by
    constructor
    · intro h
      have on (p : T ⊕ Bool) (s : Bool) := h (name (p,s))
      refine ⟨fun t s => ?_,fun s => ?_,fun s => ?_⟩
      · simpa [read,target,site] using on (.inl t) s
      · simpa [read,target,site] using on (.inr false) s
      · simpa [read,target,site] using on (.inr true) s
    · rintro ⟨ha,h₀,h₁⟩ i
      obtain ⟨⟨p,s⟩,rfl⟩ := name.surjective i
      cases p with
      | inl t => simpa [read,target,site] using ha t s
      | inr v => cases v <;> simp [read,target,site,h₀ s,h₁ s]
  obtain ⟨l,inS,len,_,act,ind⟩ := onto_sampled_read_span S _ sampling _ le_rfl read 0 target a b c d
    ⟨x,(ok x).mpr ⟨keep,he,hf⟩,hit⟩
  exact ⟨l,fun y h=>⟨(inS y h).1,(ok y).mp (inS y h).2⟩,len,
    ((ok _).mp act).1,((ok _).mp act).2.1,((ok _).mp act).2.2,ind⟩
#print axioms sample
end ExactPlanePinnedSampling
