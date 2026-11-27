import ExactPlaneWedgeHeight
import ExactPlanePhysicalWedgeTree
namespace ExactPlaneWedgeDecision
open ExactPlaneWedgeProduct ExactPlaneWedgeHeight ExactPlaneResidualPivots
open ExactPlaneWedgeTree ExactPlanePhysicalWedgeTree ExactPlanePhysicalConverse
open ExactPlaneFirstRelation ExactPlaneRelationPair
open scoped BigOperators
variable {n : Nat} {K : Type*} [AddCommGroup K] [Module (ZMod 2) K]
abbrev Sites (n : Nat) := Finset (Fin n)
def output (x : Feature n) : Sites n × Sites n := (support x.2.1,support x.2.2.1)
def find (h : Fin n→Plane) (xs : List (Feature n)) : Option (Sites n × Sites n) :=
  (xs.find? (fun x=>decide (score h x≠0))).map output

def Good (k : Fin n→K) (b h : Fin n→Plane) (U V : Sites n) : Prop :=
  ∃ g : K→ₗ[ZMod 2] Plane,(∀i∈U∪V,g (k i)=b i) ∧
    aggregate k (mask U)=0 ∧ aggregate k (mask V)=0 ∧
    Independent (aggregate h (mask U)) (aggregate h (mask V))

theorem good_trace (k : Fin n→K) (b h : Fin n→Plane) (U V : Sites n)
    (ok : Good k b h U V) : ExactTrace k b h (U∪V) := by
  obtain ⟨g,ag,u,v,ind⟩ := ok
  have lu : U⊆U∪V := Finset.subset_union_left
  have rv : V⊆U∪V := Finset.subset_union_right
  apply pair_trace k b h _ g ag (mask U) (mask V)
  · apply (mem_relation ..).mpr
    exact ⟨u,fun i hi=>ag i (lu (support_mask U ▸ hi))⟩
  · apply (mem_relation ..).mpr
    exact ⟨v,fun i hi=>ag i (rv (support_mask V ▸ hi))⟩
  · simpa using lu
  · simpa using rv
  · exact ind

private theorem mask_support (u : V n) : mask (support u)=u := by
  funext i
  have bits : ∀x : ZMod 2,x=0 ∨ x=1 := by decide
  rcases bits (u i) with a|a <;> simp [mask,support,a]

theorem root_spec (k : Fin n→K) (b h : Fin n→Plane) (xs : List (Feature n)) {J : Submodule (ZMod 2) K}
    (sound : ∀x∈xs,x∈ExactPlaneWedgeSplit.family Finset.univ k b
      (⟨0,0,0⟩ : ExactPlaneWedgeSplit.State J Plane))
    (sp : ∀ U V,Good k b h U V → ∃x∈xs,score h x≠0) :
    (∀ uv,find h xs=some uv → Good k b h uv.1 uv.2) ∧
    (find h xs≠none ↔ ∃A,ExactTrace k b h A) := by
  have extract : ∀x∈xs,score h x≠0 → Good k b h (output x).1 (output x).2 := by
    intro x hx nz
    obtain ⟨U,V,g,_,_,mt,_,u,v,rfl⟩ := sound x hx
    change Good k b h (support (mask U)) (support (mask V))
    rw [support_mask,support_mask]
    refine ⟨g,mt,?_,?_,(det_ne_iff _ _).mp ?_⟩
    · simpa [aggregate_support] using u
    · simpa [aggregate_support] using v
    · exact (score_actual h (mask U) (mask V)) ▸ nz
  have ret : ∀ uv,find h xs=some uv → Good k b h uv.1 uv.2 := by
    intro uv got
    unfold find at got
    cases e : xs.find? (fun x=>decide (score h x≠0)) with
    | none => rw [e] at got; cases got
    | some x =>
      rw [e] at got
      cases got
      exact extract x (List.mem_of_find?_eq_some e) (of_decide_eq_true (List.find?_some (p:=fun a=>decide (score h a≠0)) e))
  refine ⟨ret,?_,?_⟩
  · intro hit
    cases e : find h xs with
    | none => exact False.elim (hit e)
    | some z => exact ⟨_,good_trace k b h _ _ (ret z e)⟩
  · rintro ⟨A,tr⟩ no
    obtain ⟨g,mt⟩ := ExactPlanePhysicalConverse.chart k b h A tr
    obtain ⟨_,u,v,ma,ru,rv,su,sv,ind⟩ := (exact_pair k b h A).mp tr
    have r1 := (mem_relation ..).mp ru
    have r2 := (mem_relation ..).mp rv
    have good : Good k b h (support u) (support v) := by
      rw [Good,mask_support,mask_support]
      exact ⟨g,fun i hi=>mt i ((Finset.union_subset su sv) hi),r1.1,r2.1,ind⟩
    obtain ⟨x,hx,nz⟩ := sp _ _ good
    have none : xs.find? (fun a=>decide (score h a≠0))=Option.none := by
      unfold find at no
      cases eq : xs.find? (fun a=>decide (score h a≠0)) with
      | none => rfl
      | some a => rw [eq] at no; cases no
    have bad := List.find?_eq_none.mp none x hx
    simpa [nz] using bad
theorem retained (k : Fin n→K) (b h : Fin n→Plane) (t : Tree n) (cover : leaves t=Finset.univ)
    (xs : List (Feature n))
    (sub : ∀ x∈xs,x∈ExactPlaneWedgeSplit.family (leaves t) k b (rootState k t))
    (spanEq : Submodule.span (ZMod 2) {x | x∈xs} =
       Submodule.span (ZMod 2) (ExactPlaneWedgeSplit.family (leaves t) k b (rootState k t))) :
    (∀ uv,find h xs=some uv → Good k b h uv.1 uv.2) ∧
    (find h xs≠none ↔ ∃A,ExactTrace k b h A) := by
  apply root_spec k b h xs (J:=keySpan k t ⊓ ⊥)
  · intro x hx
    rw [←cover]
    exact sub x hx
  · rintro U V ⟨g,mt,u,v,ind⟩
    by_contra! no
    have kill : Submodule.span (ZMod 2) {x | x∈xs} ≤ LinearMap.ker (linear h) :=
      Submodule.span_le.mpr fun x hx => no x hx
    rw [spanEq] at kill
    have mem : actual (mask U) (mask V) ∈ ExactPlaneWedgeSplit.family (leaves t) k b (rootState k t) := by
      refine ⟨U,V,g,by simp [cover],by simp [cover],mt,?_,?_,?_,rfl⟩
      · intro x
        have z : (x:K)=0 := (Submodule.mem_bot _).mp x.property.2
        simp [z,rootState]
      · simpa [aggregate_support,rootState] using u
      · simpa [aggregate_support,rootState] using v
    have zero : score h (actual (mask U) (mask V))=0 := kill (Submodule.subset_span mem)
    exact (det_ne_iff _ _).mpr ind ((score_actual ..).symm.trans zero)
#print axioms retained
#print axioms root_spec
end ExactPlaneWedgeDecision
