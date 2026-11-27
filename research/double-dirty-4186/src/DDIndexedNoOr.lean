import DDIndexedOwnership
import DDIndexedReaders
import Q1DoubleSplitCost
import Q1DoubleTopology

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double S4183
attribute [local instance] gateOpDecEq

private theorem ref_input {n k i : ℕ} (C : Circuit) (p : Cuts) (hi : i < n) :
    ref (build n C p k) i = some (.input i,i) := by
  induction k with
  | zero => simp [build,ref,initial,List.getD_eq_getElem?_getD,hi]
  | succ k ih => rw [stable_ref C p (by omega),ih]

/-- OR rows cannot alias an earlier gate: they retain their own tag or are symbolic true. -/
theorem or_tag {n t k i v : ℕ} (C : Circuit) (p : Cuts) (ht : t < k)
    (op : (gateAt C t).op = .or) (tag : ref (build n C p k) (n+t) = some (.gate i,v)) : t=i := by
  rw [row_ref C p ht,op] at tag
  cases hl : pin (build n C p t) n C p t 0 <;> cases hr : pin (build n C p t) n C p t 1 <;>
    cases skip : p.omit t <;> simp_all [dest]

theorem no_or_from_and {n m j i v : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : DoubleDirty G C m) (ao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C i).op = .and) (hor : (gateAt C j).op = .or)
    (keep : (splitCuts n C (orT G C) m).omit j = false) (b : Fin 2) :
    pin (build n C (splitCuts n C (orT G C) m) j) n C (splitCuts n C (orT G C) m) j b ≠
      some (.gate i,v) := by
  let p := splitCuts n C (orT G C) m
  have ne : j ≠ m ∧ j ∉ orT G C := by simpa [splitCuts] using keep
  have bad : ¬ BelowF G C j := fun h =>
    ne.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hor,h⟩)
  have orn : j ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hor,bad⟩
  have lam' : j ∈ lam G C := by
    by_contra no
    have mem := Finset.mem_sdiff.mpr ⟨orn,no⟩
    rw [D.exception,Finset.mem_singleton] at mem
    exact ne.1 mem
  obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp lam'
  have support : (orIn n C (opnd C j b)).Nonempty := by fin_cases b <;> assumption
  intro issue
  change pin (build n C p j) n C p j b = _ at issue
  simp only [pin] at issue
  split at issue
  · contradiction
  · let w := opnd C j b
    have bounded : w < n+j := ao.2.1 j hj w (by
      obtain ⟨_,a,d,pins,_,_⟩ := S98.AO_of_IsAO2 n C ao j hj
      fin_cases b <;> simp [w,opnd,pins])
    by_cases raw : w < n
    · change ref (build n C p j) w = _ at issue
      rw [ref_input C p raw] at issue
      simp at issue
    · let t := w-n
      have eq : w = n+t := by dsimp [t];omega
      have ht : t < j := by omega
      have htlen : t < C.gates.length := by omega
      have ops := (S98.AO_of_IsAO2 n C ao t htlen).1
      change (orIn n C w).Nonempty at support
      change ref (build n C p j) w = _ at issue
      rw [eq] at issue support
      rcases ops with ta | tor
      · rw [Q0.and_empty_support ta] at support
        simpa using support
      · have same := or_tag C p ht tor issue
        subst i
        rw [tor] at hand
        contradiction


theorem retained_reader_and {n m j i : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : DoubleDirty G C m) (ao : IsAO2 n C) (hj : j < C.gates.length) {gi gj : Gate}
    (hand : (gateAt C i).op = .and)
    (src : ins n C (splitCuts n C (orT G C) m) i = some gi)
    (reader : ins n C (splitCuts n C (orT G C) m) j = some gj)
    (used : n+rank n C (splitCuts n C (orT G C) m) i ∈ gj.inputs) : gj.op = .and := by
  let p := splitCuts n C (orT G C) m
  change ins n C p j = some gj at reader
  change n+rank n C p i ∈ gj.inputs at used
  have decode : ∃ a b : Origin × ℕ, pin (build n C p j) n C p j 0 = some a ∧
      pin (build n C p j) n C p j 1 = some b ∧ p.omit j = false ∧ gj = ⟨(gateAt C j).op,[a.2,b.2]⟩ := by
    unfold ins at reader
    cases l : pin (build n C p j) n C p j 0 <;> cases r : pin (build n C p j) n C p j 1 <;>
      cases skip : p.omit j <;> simp_all [instruction]
  obtain ⟨a,b,hl,hr,hs,rfl⟩ := decode
  change (gateAt C j).op = .and
  apply (S98.AO_of_IsAO2 n C ao j hj).1.resolve_right
  intro hor
  have bad (d : Fin 2) (z : Origin × ℕ) (h : pin (build n C p j) n C p j d = some z)
      (e : n+rank n C p i = z.2) : False := by
    have tag := tag_of_address src h e.symm
    have same : z = (.gate i,z.2) := Prod.ext tag rfl
    apply no_or_from_and D ao hj hand hor hs d
    exact h.trans (congrArg some same)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  exact used.elim (bad 0 a hl) (bad 1 b hr)
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
