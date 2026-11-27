import ExactPlaneEagerDecision
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.VectorSpace
namespace ExactPlaneSuppliedCoordinates
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneResidualPivots ExactPlaneIndexedBranch ExactPlaneFullDirections ExactPlanePhysicalConverse
open ExactPlaneGlobalApplication ExactPlaneObservedSpan ExactPlaneSamplerRank ExactPlaneOddChartList
open scoped BigOperators
variable {d N : ℕ}
abbrev Key (d : ℕ) := Fin d → ZMod 2
abbrev Row (d : ℕ) := (Fin d × Bool) → ZMod 2

def value (x : Row d) (p : Key d) : Plane := ∑ j, p j • (x (j,false),x (j,true))

theorem value_chart (x : Row d) (p : Key d) :
    value x p = tagChart (Pi.basisFun (ZMod 2) (Fin d)) x p := by
  simp [value,tagChart,Basis.constr_apply_fintype,Basis.equivFun_apply,Pi.basisFun_repr,target]

def tables (rows : List (Row d)) (p : Fin N → Key d) :=
  rows.map fun x i => value x (p i)

section Abstract
open Classical
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] [Module.Finite (ZMod 2) K]
private theorem number (T : Finset K) (p : K→Prop) :
    Fintype.card {i : ↥T // i∉Finset.univ.filter (fun j : ↥T=>p j.val)}=(T.filter fun i=>¬p i).card := by
  let e : {i : ↥T // i∉Finset.univ.filter (fun j : ↥T=>p j.val)} ≃ ↥(T.filter fun i=>¬p i) :=
    { toFun := fun i=>⟨i.val.val,Finset.mem_filter.mpr ⟨i.val.property,by simpa using i.property⟩⟩
      invFun := fun i=>⟨⟨i.val,(Finset.mem_filter.mp i.property).1⟩,by simpa using (Finset.mem_filter.mp i.property).2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem supplied_physical (priv : Fin N→K) (tag : Fin N→Plane)
    (full : Submodule.span (ZMod 2) (Set.range priv)=⊤)
    (S : Finset (K→ₗ[ZMod 2] Plane))
    (sample : ∀ (T : Finset K) (D : Basis (↥T) (ZMod 2) K),
      OntoHits (S.image (coordinates D)) (2*(deficit (ZMod 2) priv tag+2)+1)) :
    ∀ height : Fin N→Plane,
        (∃ A : Finset (Fin N),ExactTrace priv tag height A) ↔
          ∃ m : List (K→ₗ[ZMod 2] Plane),(∀ g∈m,g∈S) ∧
            (m.length=1 ∨ m.length=3 ∨ m.length=5) ∧ Recovered priv tag height m.sum := by
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
end Abstract

private noncomputable def restrictL (W : Submodule (ZMod 2) (Key d)) :
    (Key d →ₗ[ZMod 2] Plane) →ₗ[ZMod 2] (W →ₗ[ZMod 2] Plane) where
  toFun g := g.comp W.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem supplied_decision (rows : List (Row d)) (priv : Fin N→Key d) (tag height : Fin N→Plane)
    (R : ℕ) (enough : 2*(deficit (ZMod 2) (key priv) tag+2)+1 ≤ R)
    (hits : OntoHits rows.toFinset R) :
    ExactPlaneEagerSelector.runBasis (tables rows priv) priv tag height ≠ none ↔
      ∃ A : Finset (Fin N), ExactTrace priv tag height A := by
  classical
  let W := observed priv
  let D₀ := Pi.basisFun (ZMod 2) (Fin d)
  let decode := (restrictL W).comp (ExactPlaneGlobalSeed.equiv D₀).symm.toLinearMap
  have onto : Function.Surjective decode :=
    (show Function.Surjective (restrictL W) from fun g => g.exists_extend).comp
      (ExactPlaneGlobalSeed.equiv D₀).symm.surjective
  let S := rows.toFinset.image decode
  have sample (T : Finset W) (D : Basis (↥T) (ZMod 2) W) :
      OntoHits (S.image (coordinates D)) (2*(deficit (ZMod 2) (key priv) tag+2)+1) := by
    intro k hk f hf y
    let E := (ExactPlaneGlobalSeed.equiv D).toLinearMap.comp decode
    obtain ⟨x,hx,eq⟩ := hits k (hk.trans enough) (f.comp E)
      (hf.comp ((ExactPlaneGlobalSeed.equiv D).surjective.comp onto)) y
    exact ⟨_,Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩,eq⟩
  let tab := fun (g : W→ₗ[ZMod 2] Plane) (i : Fin N) => g (key priv i)
  rw [ExactPlaneEagerSelector.runBasis_eq]
  constructor
  · intro pass
    cases ret : ExactPlaneGaussianSelector.runBasis (tables rows priv) priv tag height with
    | none => exact False.elim (pass ret)
    | some res =>
      unfold ExactPlaneGaussianSelector.runBasis ExactPlaneGaussianSelector.selectBasis at ret
      cases h : ExactPlaneGaussianSelector.selectCharts (candidates (tables rows priv)) priv tag height with
      | none => simp [h] at ret
      | some ans =>
        obtain ⟨_,_,_,_,_,tr⟩ := ExactPlaneGaussianSelector.first_success h
        exact ⟨_,tr⟩
  · rintro ⟨A,hA⟩ no
    obtain ⟨m,hm,len,win⟩ := (supplied_physical (key priv) tag (full priv) S sample height).mp
      ⟨A,(trace_iff priv tag height A).mpr hA⟩
    have mem : (m.map tab).sum ∈ candidates (tables rows priv) := by
      apply (mem_candidates _ _).mpr
      refine ⟨m.map tab,?_,by simpa using len,rfl⟩
      intro t ht
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hm g hg)
      refine List.mem_map.mpr ⟨x,List.mem_toFinset.mp hx,?_⟩
      exact funext fun i => value_chart x (priv i)
    have sumEq : (m.map tab).sum = tab m.sum := by
      clear hm len win mem
      induction m with
      | nil => rfl
      | cons g m ih => simp only [List.map_cons,List.sum_cons,ih]; rfl
    apply (ExactPlaneGaussianSelector.supplied_none _ priv tag height).mp no _ mem
    rw [sumEq]
    exact (trace_iff priv tag height _).mp win.1

theorem ambient_decision (rows : List (Row d)) (priv : Fin N→Key d) (tag height : Fin N→Plane)
    (hits : OntoHits rows.toFinset (2*(d+2)+1)) :
    ExactPlaneEagerSelector.runBasis (tables rows priv) priv tag height ≠ none ↔
      ∃ A : Finset (Fin N), ExactTrace priv tag height A := by
  apply supplied_decision rows priv tag height _ _ hits
  have dim : finrank (ZMod 2) (observed priv) ≤ d := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using (observed priv).finrank_le
  have low : deficit (ZMod 2) (key priv) tag ≤ finrank (ZMod 2) (observed priv) :=
    Nat.sub_le _ _
  omega

#print axioms supplied_decision
end ExactPlaneSuppliedCoordinates
