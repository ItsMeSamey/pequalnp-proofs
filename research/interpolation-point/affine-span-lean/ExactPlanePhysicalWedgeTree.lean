import ExactPlaneWedgeTree
import ExactPlaneWedgeSplit
namespace ExactPlanePhysicalWedgeTree
open Submodule ExactPlaneWedgeProduct ExactPlaneWedgeTree ExactPlaneWedgeSplit
open scoped BigOperators
variable {n : Nat} {K B : Type*} [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]

def keySpan (k : Fin n→K) : Tree n→Submodule F K
  | .leaf i => span F {k i}
  | .join l r => keySpan k l ⊔ keySpan k r

theorem key_mem (k : Fin n→K) (t : Tree n) : ∀ i∈leaves t,k i∈keySpan k t := by
  induction t with
  | leaf j =>
    intro i hi
    have e : i=j := Finset.mem_singleton.mp hi
    exact subset_span (Set.mem_singleton_iff.mpr (congrArg k e))
  | join l r hl hr =>
    intro i hi
    rcases Finset.mem_union.mp hi with left|right
    · exact (le_sup_left : keySpan k l ≤ keySpan k l ⊔ keySpan k r) (hl i left)
    · exact (le_sup_right : keySpan k r ≤ keySpan k l ⊔ keySpan k r) (hr i right)

theorem keySpan_eq (k : Fin n→K) (t : Tree n) :
    keySpan k t=span F (k '' (leaves t : Set (Fin n))) := by
  induction t with
  | leaf i => simp [keySpan,leaves]
  | join l r hl hr => simp [keySpan,leaves,hl,hr,Set.image_union,Submodule.span_union]

noncomputable def table (k : Fin n→K) (b : Fin n→B) : (t : Tree n)→(E : Submodule F K)→
    State (keySpan k t ⊓ E) B → Finset (Feature n)
  | .leaf i,_,s => thin (family {i} k b s)
  | .join l r,E,s =>
    thin (combine (Compatible (keySpan k l) (keySpan k r) E s)
      (fun x => (table k b l (keySpan k r ⊔ E) x : Set _))
      (fun y => (table k b r (keySpan k l ⊔ E) y : Set _)))

theorem table_exact (k : Fin n→K) (b : Fin n→B) (t : Tree n) (sep : separated t)
    (E : Submodule F K) (s : State (keySpan k t ⊓ E) B) :
    (table k b t E s : Set (Feature n)) ⊆ family (leaves t) k b s ∧
    LinearIndepOn F id (table k b t E s : Set (Feature n)) ∧
    span F (table k b t E s : Set (Feature n))=span F (family (leaves t) k b s) := by
  induction t generalizing E with
  | leaf i => exact thin_spec _
  | join l r hl hr =>
    let L := keySpan k l
    let R := keySpan k r
    let ok := Compatible L R E s
    let Lraw := fun x : State (L ⊓ (R⊔E)) B => family (leaves l) k b x
    let Rraw := fun y : State (R ⊓ (L⊔E)) B => family (leaves r) k b y
    let Lkeep := fun x : State (L ⊓ (R⊔E)) B => (table k b l (R⊔E) x : Set (Feature n))
    let Rkeep := fun y : State (R ⊓ (L⊔E)) B => (table k b r (L⊔E) y : Set (Feature n))
    have real : combine ok Lraw Rraw = family (leaves (.join l r)) k b s := by
      ext z
      exact (mem_combine ok Lraw Rraw z).trans
        (split_family (leaves l) (leaves r) sep.1 k b L R E (key_mem k l) (key_mem k r) s z).symm
    obtain ⟨sub,li,sp⟩ := thin_spec (combine ok Lkeep Rkeep)
    refine ⟨?_,li,?_⟩
    · rw [←real]
      intro z hz
      obtain ⟨i,j,hij,x,hx,y,hy,eq⟩ := (mem_combine ok Lkeep Rkeep z).mp (sub hz)
      exact (mem_combine _ _ _ _).mpr ⟨i,j,hij,x,(hl sep.2.1 (R⊔E) i).1 hx,
        y,(hr sep.2.2 (L⊔E) j).1 hy,eq⟩
    · exact sp.trans ((combine_span ok Lraw Lkeep Rraw Rkeep
        (fun i=>(hl sep.2.1 (R⊔E) i).2.2) (fun j=>(hr sep.2.2 (L⊔E) j).2.2)).trans
        (congrArg (span F) real))

def rootState (k : Fin n→K) (t : Tree n) : State (keySpan k t ⊓ ⊥) B :=
  ⟨0,0,0⟩

theorem root_hit (k : Fin n→K) (b : Fin n→B) (t : Tree n) (sep : separated t)
    (cover : leaves t=Finset.univ) (f : Feature n→ₗ[F] F) :
    (∃ x∈table k b t ⊥ (rootState k t), f x≠0) ↔
      ∃ (U V : Finset (Fin n)) (g : K→ₗ[F] B),
        (∀ i∈U∪V,g (k i)=b i) ∧ (∑ i∈U,k i)=0 ∧ (∑ i∈V,k i)=0 ∧
        f (actual (mask U) (mask V))≠0 := by
  classical
  obtain ⟨sub,_,sp⟩ := table_exact k b t sep ⊥ (rootState k t)
  constructor
  · rintro ⟨x,hx,positive⟩
    obtain ⟨U,V,g,_,_,ag,_,u,v,ax⟩ := sub hx
    exact ⟨U,V,g,ag,u,v,ax ▸ positive⟩
  · rintro ⟨U,V,g,ag,u,v,nz⟩
    by_contra! none
    have kill : span F (table k b t ⊥ (rootState k t) : Set _) ≤ LinearMap.ker f :=
      Submodule.span_le.mpr fun x hx => none x hx
    rw [sp] at kill
    apply nz
    apply kill
    apply Submodule.subset_span
    refine ⟨U,V,g,(by simp [cover]),(by simp [cover]),ag,?_,u,v,rfl⟩
    intro x
    have hx : (x:K)=0 := (Submodule.mem_bot _).mp x.property.2
    simp [hx,rootState]

#print axioms root_hit
#print axioms table_exact
end ExactPlanePhysicalWedgeTree
