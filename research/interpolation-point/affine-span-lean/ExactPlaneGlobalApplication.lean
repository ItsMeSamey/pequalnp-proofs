import ExactPlaneGlobalSeed
import ExactPlaneFullDirections
import ExactPlaneSuccessTrace
namespace ExactPlaneGlobalApplication
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneResidualPivots ExactPlaneIndexedBranch ExactPlaneFullDirections ExactPlanePhysicalConverse
open scoped BigOperators
open Classical
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] [Module.Finite (ZMod 2) K] {N : ℕ}

noncomputable def accepted (priv : Fin N→K) (tag : Fin N→Plane)
    (g : K→ₗ[ZMod 2] Plane) : Finset (Fin N) :=
  Finset.univ.filter (fun i=>tag i=g (priv i))

def Recovered (priv : Fin N→K) (tag height : Fin N→Plane) (g : K→ₗ[ZMod 2] Plane) : Prop :=
  ExactTrace priv tag height (accepted priv tag g) ∧
    ∃ (U : Fin 2→Finset (Fin N)) (gains : Fin 2→Plane), LinearIndependent (ZMod 2) gains ∧
      (∀ j,U j⊆accepted priv tag g) ∧
      (∀ j,∑ i∈U j,ExactPlanePhysicalResidual.col priv tag height i=(0,0,gains j)) ∧ U 0≠U 1

private theorem number (T : Finset K) (p : K→Prop) :
    Fintype.card {i : ↥T // i∉Finset.univ.filter (fun j : ↥T=>p j.val)}=(T.filter fun i=>¬p i).card := by
  let e : {i : ↥T // i∉Finset.univ.filter (fun j : ↥T=>p j.val)} ≃ ↥(T.filter fun i=>¬p i) :=
    { toFun := fun i=>⟨i.val.val,Finset.mem_filter.mpr ⟨i.val.property,by simpa using i.property⟩⟩
      invFun := fun i=>⟨⟨i.val,(Finset.mem_filter.mp i.property).1⟩,by simpa using (Finset.mem_filter.mp i.property).2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem physical_decision_iff (priv : Fin N→K) (tag : Fin N→Plane)
    (full : Submodule.span (ZMod 2) (Set.range priv)=⊤) :
    let R := 2*(deficit (ZMod 2) priv tag+2)+1
    ∃ S : Finset (K→ₗ[ZMod 2] Plane),S.card≤max 1 ((2*(finrank (ZMod 2) K*2)*2^R)^2) ∧
      ∀ height : Fin N→Plane,
        (∃ A : Finset (Fin N),ExactTrace priv tag height A) ↔
          ∃ m : List (K→ₗ[ZMod 2] Plane),(∀ g∈m,g∈S) ∧
            (m.length=1 ∨ m.length=3 ∨ m.length=5) ∧ Recovered priv tag height m.sum := by
  intro R
  obtain ⟨S,cap,sample⟩ := ExactPlaneGlobalSeed.physical_seed K R
  refine ⟨S,cap,?_⟩
  intro height
  constructor
  · rintro ⟨A,trace⟩
    obtain ⟨g₀,old⟩ := ExactPlanePhysicalConverse.chart priv tag height A trace
    obtain ⟨g,T,D,idx,agree,coords,sites,count⟩ :=
      maximal_branch (ZMod 2) priv tag A g₀ old full
    let s : Selection D priv tag :=
      { full := Finset.univ.filter (fun j : ↥T=>Full priv tag j.val)
        available := by
          intro i hi v
          obtain ⟨e,h,b⟩ := (Finset.mem_filter.mp hi).2 v
          exact ⟨e,h.trans (coords i).symm,b⟩
        anchor := fun i _=>idx i
        anchor_key := fun i _=>(sites i).1 }
    have cnt : Fintype.card (Partial s)=deficit (ZMod 2) priv tag :=
      (number T (Full priv tag)).trans count
    have hits : ExactPlaneSamplerRank.OntoHits (S.image (coordinates D)) (2*(Fintype.card (Partial s)+2)+1) := by
      rw [cnt]; exact sample T D
    obtain ⟨l,inside,len,win⟩ := on_branch s height A trace g agree
      (fun i _=>by change tag (idx i)=g (priv (idx i)); rw [(sites i).1]; exact (sites i).2)
      (S.image (coordinates D)) hits
    obtain ⟨m,mem,size,_,value⟩ := ExactPlaneGlobalSeed.decode_list D S l inside
    refine ⟨m,mem,by simpa only [size] using len,?_⟩
    have same : active D priv tag l.sum=accepted priv tag m.sum := by
      unfold active accepted; rw [value]
    have recover := success_trace s height l.sum win
    rw [same] at recover
    exact ⟨recover,by simpa only [←same] using win.2⟩
  · rintro ⟨m,_,_,proof⟩
    exact ⟨accepted priv tag m.sum,proof.1⟩
#print axioms physical_decision_iff
end ExactPlaneGlobalApplication
