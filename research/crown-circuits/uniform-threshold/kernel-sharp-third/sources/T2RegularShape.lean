import T2RawDirect
import T2SoleOrSplice
import T2PhysicalOverride

namespace T2RegularOrDelete
open ResidualSurplus T2PhysicalOverride PEqualNP.CircuitLowerBounds

def Regular (n : Nat) (gs : List Raw) : Prop :=
  (∀ i : Fin n, (gs.filter (rawReads i.val)).length = 2 ∧
     ∀ r ∈ gs, rawReads i.val r = true → r.1 = Op.or) ∧
  ∀ r ∈ gs, r.2.1 ≠ r.2.2

theorem read_iff {r : Raw} {i : Nat} :
    rawReads i r = true ↔ r.2.1=i ∨ r.2.2=i := by simp [rawReads]

theorem unread_native {gs : List Raw} {i : Nat} (skip : ∀ r ∈ gs, ¬rawReads i r) :
    ∀ g ∈ gs.map native, i ∉ g.inputs := by
  intro g mem h
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  apply skip r hr
  apply read_iff.mpr
  change i ∈ [r.2.1,r.2.2] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  exact h.imp Eq.symm Eq.symm

theorem one_position {gs : List Raw} {i : Nat}
    (len : (gs.filter (rawReads i)).length = 1) :
    ∃ a r b, gs=a++r::b ∧ rawReads i r = true ∧
      (∀ g ∈ a.map native, i ∉ g.inputs) ∧ (∀ g ∈ b.map native, i ∉ g.inputs) := by
  obtain ⟨r,eq⟩ := List.length_eq_one_iff.mp len
  obtain ⟨a,b,shape,l,yes,tail⟩ := List.filter_eq_cons_iff.mp eq
  exact ⟨a,r,b,shape,yes,unread_native l,unread_native (List.filter_eq_nil_iff.mp tail)⟩

theorem two_positions {gs : List Raw} {i : Nat}
    (len : (gs.filter (rawReads i)).length = 2) :
    ∃ a r b s c, gs=a++r::(b++s::c) ∧ rawReads i r = true ∧ rawReads i s = true ∧
      (∀ t ∈ gs, rawReads i t = true → t=r ∨ t=s) := by
  obtain ⟨r,s,eq⟩ : ∃ r s, gs.filter (rawReads i) = [r,s] :=
    ⟨_,_,List.eq_getElem_of_length_eq_two _ len⟩
  obtain ⟨a,tail,sh,_,yr,t⟩ := List.filter_eq_cons_iff.mp eq
  obtain ⟨b,c,sh',_,ys,_⟩ := List.filter_eq_cons_iff.mp t
  refine ⟨a,r,b,s,c,sh'.symm ▸ sh,yr,ys,?_⟩
  intro u hu ur
  have m : u ∈ gs.filter (rawReads i) := List.mem_filter.mpr ⟨hu,ur⟩
  simpa only [eq,List.mem_cons,List.not_mem_nil,or_false] using m
end T2RegularOrDelete
