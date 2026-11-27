import DDIndexedIsolatedAddress
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

theorem cap_apart {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (z : SplitData G C m)
    (a b w : Fin (n+rank n C (splitCuts n C (orT G C) m) C.size)) (oa ob ow : Origin)
    (ha : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.a) = some (oa,a.val))
    (hb : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.b) = some (ob,b.val))
    (hw : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.t) = some (ow,w.val)) :
    let p := splitCuts n C (orT G C) m
    let E := (tops G C).erase z.t
    let D := capPrefix n C p C.size a b w
    ∀ r ∈ rootIndices n C p E, ∀ t ∈ rootIndices n C p E, ¬ strictInfluence n D r (n+t) := by
  let p := splitCuts n C (orT G C) m
  let K := rank n C p C.size
  let D := capPrefix n C p C.size a b w
  change ∀ r ∈ rootIndices n C p ((tops G C).erase z.t), ∀ t ∈ rootIndices n C p ((tops G C).erase z.t), ¬ strictInfluence n D r (n+t)
  intro r hr t _ path
  obtain ⟨j,hj⟩ := first_reader path
  obtain ⟨jb,hpin⟩ := Finset.mem_filter.mp hj
  have jlen := Finset.mem_range.mp jb
  have spec := cap_prefix_spec C p least.1 (k:=C.size) le_rfl a b w
  have early := spec.1.2.1 j jlen _ hpin
  have rj : r<j := by omega
  have bound : j<K+2 := by simpa [D,K,capPrefix,Circuit.size,rank] using jlen
  have tail (lo : K≤j) : (gateAt D j).inputs = [a.val,w.val] ∨ (gateAt D j).inputs = [b.val,w.val] := by
    have eq : j=K ∨ j=K+1 := by omega
    rcases eq with rfl|rfl <;> simp [D,K,gateAt,capPrefix,rank,List.getD_eq_getElem?_getD]
  rcases Finset.mem_insert.mp hr with rfl|hr
  · obtain eq | eq := tail (by omega)
    all_goals rw [eq] at hpin; simp only [List.mem_cons,List.not_mem_nil,or_false] at hpin
    all_goals
      change n+K = _ ∨ n+K = _ at hpin
      have la : a.val < n+K := a.isLt
      have lb : b.val < n+K := b.isLt
      have lw : w.val < n+K := w.isLt
      omega
  rcases Finset.mem_insert.mp hr with rfl|hr
  · omega
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨ne,top⟩ := Finset.mem_erase.mp he
  obtain ⟨ge,paid⟩ := external_paid edge least form top (fun p => ne (z.onlyAffected _ top p))
  have iso : ∀ k ≤ C.size, ∀ u < n+k, ∀ o, ref (build n C p k) u =
      some (o,n+rank n C p e) → u=n+e := address_isolated edge least form top paid
  by_cases pre : j<K
  · obtain ⟨i,ilen,g,ig,eq⟩ := physical_owner C p pre
    have gate : gateAt D j = g := by
      rw [←eq]
      have lt := paid_strict C p ig ilen
      simp [D,gateAt,capPrefix,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,retains_instruction C p ig ilen]
    rw [gate] at hpin
    have decoded : ∃ l r : Origin × ℕ, pin (build n C p i) n C p i 0 = some l ∧
        pin (build n C p i) n C p i 1 = some r ∧ p.omit i = false ∧ g.inputs=[l.2,r.2] := by
      unfold ins at ig
      cases l : pin (build n C p i) n C p i 0 <;> cases r : pin (build n C p i) n C p i 1 <;>
        cases skip : p.omit i <;> simp_all [instruction]
      rw [←ig]
    obtain ⟨l,r,hl,hr,keep,pins⟩ := decoded
    have ban (d : Fin 2) (z' : Origin × ℕ) (hit : pin (build n C p i) n C p i d = some z')
        (addr : n+rank n C p e = z'.2) : False := by
      have mem := opnd_mem least.1 ilen d
      have lt := least.1.2.1 i ilen _ mem
      simp only [pin] at hit
      split at hit
      · contradiction
      · have pair : z' = (z'.1,n+rank n C p e) := Prod.ext rfl addr.symm
        have eqw := iso i (Nat.le_of_lt ilen) _ lt z'.1 (hit.trans (congrArg some pair))
        rw [eqw] at mem
        have clean := isolated_clean_reader edge least form top (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ilen,mem⟩)
        simp [p,splitCuts,clean] at keep
    rw [pins] at hpin
    rcases (by simpa using hpin : n+rank n C p e=l.2 ∨ n+rank n C p e=r.2) with h|h
    · exact ban 0 l hl h
    · exact ban 1 r hr h
  · have notarm (i : ℕ) (hi : i∈junk G C) {o : Origin} {v : ℕ}
        (refeq : ref (build n C p C.size) (n+i) = some (o,v)) : n+rank n C p e ≠ v := by
      rintro rfl
      obtain ⟨ir,_,bad⟩ := (S4183.junk_iff G C i).mp hi
      have ilt : i<C.size := ir
      have eq := iso C.size le_rfl (n+i) (Nat.add_lt_add_left ilt n) _ refeq
      have id : i=e := by omega
      exact bad (id.symm ▸ (Finset.mem_filter.mp top).2.2)
    have na := notarm z.a z.aJunk ha
    have nb := notarm z.b z.bJunk hb
    have nw : n+rank n C p e ≠ w.val := by
      intro eq
      rw [←eq] at hw
      have tl : z.t<C.size := Finset.mem_range.mp (Finset.mem_filter.mp z.top).1
      have same := iso C.size le_rfl (n+z.t) (Nat.add_lt_add_left tl n) _ hw
      exact ne (by omega)
    obtain eq|eq := tail (by omega)
    all_goals rw [eq] at hpin; simp_all
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
