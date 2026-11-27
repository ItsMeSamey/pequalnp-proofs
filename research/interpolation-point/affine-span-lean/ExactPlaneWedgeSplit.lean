import ExactPlaneWedgeBoundary
import ExactPlaneWedgeProduct
namespace ExactPlaneWedgeSplit
open ExactPlaneWedgeBoundary ExactPlaneWedgeProduct
open scoped BigOperators
variable {K B : Type*} [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B] {n : Nat}
structure State (J : Submodule F K) (B : Type*) [AddCommGroup B] [Module F B] where
  chart : J →ₗ[F] B
  p : J
  q : J
def mask (U : Finset (Fin n)) : V n := fun i => if i∈U then 1 else 0
def family (A : Finset (Fin n)) (k : Fin n→K) (b : Fin n→B) {J : Submodule F K}
    (s : State J B) : Set (Feature n) := {v |
  ∃ (U V : Finset (Fin n)) (g : K →ₗ[F] B), U⊆A ∧ V⊆A ∧ (∀ i∈U∪V,g (k i)=b i) ∧
    (∀ x:J,g x=s.chart x) ∧ (∑ i∈U,k i)=(s.p:K) ∧ (∑ i∈V,k i)=(s.q:K) ∧
    v=actual (mask U) (mask V)}
structure Compatible (L R E : Submodule F K) (s : State (parentBoundary L R E) B)
    (l : State (leftBoundary L R E) B) (r : State (rightBoundary L R E) B) : Prop where
  p : (l.p:K)+(r.p:K)=s.p
  q : (l.q:K)+(r.q:K)=s.q
  overlap : ∀ x : ↥(L⊓R),
    l.chart ⟨x.val,overlap_left L R E x.property⟩=r.chart ⟨x.val,overlap_right L R E x.property⟩
  outer : ∀ (a : leftBoundary L R E) (b : rightBoundary L R E) (x : parentBoundary L R E),
    (a:K)+(b:K)=x → l.chart a+r.chart b=s.chart x

private theorem mask_union {A C : Finset (Fin n)} (dc : Disjoint A C) :
    mask (A∪C)=mask A+mask C := by
  funext i
  by_cases a : i∈A
  · have c : i∉C := fun h => Finset.disjoint_left.mp dc a h
    simp [mask,a,c]
  · by_cases c : i∈C <;> simp [mask,a,c]
private theorem pieces {A C U : Finset (Fin n)} (dis : Disjoint A C) (sub : U⊆A∪C) :
    U∩A⊆A ∧ U∩C⊆C ∧ Disjoint (U∩A) (U∩C) ∧ (U∩A)∪(U∩C)=U := by
  refine ⟨Finset.inter_subset_right,Finset.inter_subset_right,
    dis.mono Finset.inter_subset_right Finset.inter_subset_right,?_⟩
  rw [← Finset.inter_union_distrib_left,Finset.inter_eq_left.mpr sub]
private def stateOf (g : K →ₗ[F] B) (J : Submodule F K) (x y : J) : State J B :=
  ⟨g.comp J.subtype,x,y⟩

theorem split_family (A C : Finset (Fin n)) (dis : Disjoint A C) (k : Fin n→K) (b : Fin n→B)
    (L R E : Submodule F K) (keysL : ∀i∈A,k i∈L) (keysR : ∀i∈C,k i∈R)
    (s : State (parentBoundary L R E) B) (y : Feature n) :
    y∈family (A∪C) k b s ↔ ∃ (l : State (leftBoundary L R E) B)
      (r : State (rightBoundary L R E) B), Compatible L R E s l r ∧
      y∈Set.image2 (fun a b=>bilinear n a b) (family A k b l) (family C k b r) := by
  classical
  constructor
  · rintro ⟨U,V,g,u,v,hit,bound,su,sv,rfl⟩
    obtain ⟨ul,ur,ud,ue⟩ := pieces dis u
    obtain ⟨vl,vr,vd,ve⟩ := pieces dis v
    have totals {T : Finset (Fin n)} (d : Disjoint (T∩A) (T∩C)) (eq : (T∩A)∪(T∩C)=T) :
        (∑ i∈T∩A,k i)+(∑ i∈T∩C,k i)=∑ i∈T,k i := by rw [←Finset.sum_union d,eq]
    have up := (totals ud ue).trans su
    have vp := (totals vd ve).trans sv
    have sides {T : Finset (Fin n)} (ext : (∑ i∈T∩A,k i)+(∑ i∈T∩C,k i)∈E) :=
      parts (E:=E) (L.sum_mem (fun i (hi : i∈T∩A)=>keysL i (Finset.mem_inter.mp hi).2))
        (R.sum_mem (fun i (hi : i∈T∩C)=>keysR i (Finset.mem_inter.mp hi).2)) ext
    have hp := sides (T:=U) (by rw [up]; exact s.p.property.2)
    have hq := sides (T:=V) (by rw [vp]; exact s.q.property.2)
    let l := stateOf g _ ⟨_,hp.1⟩ ⟨_,hq.1⟩
    let r := stateOf g _ ⟨_,hp.2⟩ ⟨_,hq.2⟩
    refine ⟨l,r,⟨up,vp,fun _=>rfl,?_⟩,actual (mask (U∩A)) (mask (V∩A)),?_,actual (mask (U∩C)) (mask (V∩C)),?_,?_⟩
    · intro a c x eq
      change g a.val + g c.val = s.chart x
      rw [←map_add,eq,bound]
    · exact ⟨U∩A,V∩A,g,ul,vl,fun i hi=>hit i (Finset.union_subset_union Finset.inter_subset_left Finset.inter_subset_left hi),fun _=>rfl,rfl,rfl,rfl⟩
    · exact ⟨U∩C,V∩C,g,ur,vr,fun i hi=>hit i (Finset.union_subset_union Finset.inter_subset_left Finset.inter_subset_left hi),fun _=>rfl,rfl,rfl,rfl⟩
    · dsimp only
      rw [actual_join,←mask_union ud,←mask_union vd,ue,ve]
  · rintro ⟨l,r,ok,_,⟨U,V,g,ul,vl,hitL,bdL,su,sv,rfl⟩,_,⟨X,Y,h,xr,yr,hitR,bdR,sx,sy,rfl⟩,rfl⟩
    obtain ⟨z,hz⟩ := glue L R (g.comp L.subtype) (h.comp R.subtype) (by
      intro x
      exact (bdL ⟨_,overlap_left L R E x.property⟩).trans
        ((ok.overlap x).trans (bdR ⟨_,overlap_right L R E x.property⟩).symm))
    obtain ⟨G,ext⟩ := LinearMap.exists_extend z
    have value (a c : K) (ha : a∈L) (hc : c∈R) : G (a+c)=g a+h c := by
      let w : ↥(L⊔R) := ⟨a+c,Submodule.mem_sup.mpr ⟨a,ha,c,hc,rfl⟩⟩
      exact (LinearMap.congr_fun ext w).trans (hz ⟨a,ha⟩ ⟨c,hc⟩ w rfl)
    have keepL {i : Fin n} (hi : i∈U∪V) : G (k i)=b i := by
      have hk := keysL i (Finset.union_subset ul vl hi)
      have e := value (k i) 0 hk R.zero_mem
      simpa [hitL i hi] using e
    have keepR {i : Fin n} (hi : i∈X∪Y) : G (k i)=b i := by
      have hk := keysR i (Finset.union_subset xr yr hi)
      have e := value 0 (k i) L.zero_mem hk
      simpa [hitR i hi] using e
    have du := dis.mono ul xr
    have dv := dis.mono vl yr
    refine ⟨U∪X,V∪Y,G,Finset.union_subset_union ul xr,Finset.union_subset_union vl yr,?_,?_,?_,?_,?_⟩
    · intro i hi
      rcases Finset.mem_union.mp hi with hi|hi
      · rcases Finset.mem_union.mp hi with hU|hX
        · exact keepL (Finset.mem_union_left _ hU)
        · exact keepR (Finset.mem_union_left _ hX)
      · rcases Finset.mem_union.mp hi with hV|hY
        · exact keepL (Finset.mem_union_right _ hV)
        · exact keepR (Finset.mem_union_right _ hY)
    · intro w
      obtain ⟨a,c,eq⟩ := parent_parts L R E w
      calc
        G w.val = G (a.val+c.val) := congrArg G eq.symm
        _ = g a.val+h c.val := value _ _ a.property.1 c.property.1
        _ = l.chart a+r.chart c := congrArg₂ (·+·) (bdL a) (bdR c)
        _ = s.chart w := ok.outer a c w eq
    · rw [Finset.sum_union du,su,sx,ok.p]
    · rw [Finset.sum_union dv,sv,sy,ok.q]
    · dsimp only
      rw [actual_join,mask_union du,mask_union dv]

#print axioms split_family
end ExactPlaneWedgeSplit
