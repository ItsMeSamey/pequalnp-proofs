import ExactPlaneWedgeCodec
namespace ExactPlaneWedgeLeaf
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgeSplit
open scoped BigOperators
variable {n d w : Nat}
def pick (i : Fin n) (on : Bool) : Finset (Fin n) := if on then {i} else ∅
def vals (k : Word d) (on : Bool) : Word d := if on then k else 0
def leaf (i : Fin n) (k : Fin n→Word d) (b : Fin n→F×F) (cols : Fin w→Word d) (c : Code w) :
    List (Feature n) :=
  [false,true].flatMap fun a => [false,true].flatMap fun v =>
  if vals (k i) a=image cols c.p ∧ vals (k i) v=image cols c.q ∧
      (a=true → gamma c c.p=b i) ∧ (v=true → gamma c c.q=b i) then
    [actual (mask (pick i a)) (mask (pick i v))]
  else []

private theorem pick_sum (i : Fin n) (k : Fin n→Word d) (a : Bool) :
    (∑j∈pick i a,k j)=vals (k i) a := by cases a <;> simp [pick,vals]

private theorem classified (i : Fin n) (U : Finset (Fin n)) (sub : U⊆{i}) :
    U=pick i (decide (i∈U)) := by
  by_cases h : i∈U
  · simpa [pick,h] using Finset.Subset.antisymm sub (Finset.singleton_subset_iff.mpr h)
  · have em : U=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj =>
      h ((Finset.mem_singleton.mp (sub hj)) ▸ hj)
    simp [em,pick]

theorem leaf_exact (i : Fin n) (k : Fin n→Word d) (b : Fin n→F×F)
    (cols : Fin w→Word d) (c : Code w) {J : Submodule F (Word d)} (s : State J (F×F))
    (p : (s.p : Word d)=image cols c.p) (q : (s.q : Word d)=image cols c.q)
    (gp : s.chart s.p=gamma c c.p) (gq : s.chart s.q=gamma c c.q) (x : Feature n) :
    x∈leaf i k b cols c ↔ x∈family {i} k b s := by
  have eqmem : x∈leaf i k b cols c ↔ ∃ a v : Bool,
      (vals (k i) a=image cols c.p ∧ vals (k i) v=image cols c.q ∧
        (a=true → gamma c c.p=b i) ∧ (v=true → gamma c c.q=b i)) ∧
      x=actual (mask (pick i a)) (mask (pick i v)) := by
    simp only [leaf,List.mem_flatMap]
    constructor
    · rintro ⟨a,_,v,_,hx⟩
      split at hx
      next h => exact ⟨a,v,h,List.mem_singleton.mp hx⟩
      next => simp at hx
    · rintro ⟨a,v,h,rfl⟩
      exact ⟨a,by cases a <;> simp,v,by cases v <;> simp,by rw [if_pos h]; exact List.mem_singleton_self _⟩
  rw [eqmem]
  constructor
  · rintro ⟨a,v,⟨ap,vq,ah,vh⟩,rfl⟩
    obtain ⟨G,ex⟩ := LinearMap.exists_extend s.chart
    have ext (x:J) : G x=s.chart x := LinearMap.congr_fun ex x
    refine ⟨_,_,G,by cases a <;> simp [pick],by cases v <;> simp [pick],?_,ext,
      (pick_sum i k a).trans (ap.trans p.symm),(pick_sum i k v).trans (vq.trans q.symm),rfl⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hj|hj
    · cases a <;> simp [pick] at hj
      subst j
      change k i=image cols c.p at ap
      rw [ap,←p,ext,gp,ah rfl]
    · cases v <;> simp [pick] at hj
      subst j
      change k i=image cols c.q at vq
      rw [vq,←q,ext,gq,vh rfl]
  · rintro ⟨U,V,G,su,sv,ag,ext,ku,kv,rfl⟩
    obtain ⟨a,au⟩ : ∃ a,U=pick i a := ⟨_,classified i U su⟩
    obtain ⟨v,vv⟩ : ∃ v,V=pick i v := ⟨_,classified i V sv⟩
    subst U V
    rw [pick_sum] at ku kv
    refine ⟨a,v,⟨ku.trans p,kv.trans q,?_,?_⟩,rfl⟩
    · rintro rfl
      change k i=(s.p : Word d) at ku
      rw [←gp,←ext,←ku]
      exact ag i (Finset.mem_union_left _ (by simp [pick]))
    · rintro rfl
      change k i=(s.q : Word d) at kv
      rw [←gq,←ext,←kv]
      exact ag i (Finset.mem_union_right _ (by simp [pick]))
#print axioms leaf_exact
end ExactPlaneWedgeLeaf
