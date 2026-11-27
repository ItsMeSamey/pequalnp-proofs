import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

/-- Concatenate two disjoint, already enumerated edge batches; the default vertex
is read only at indices outside both batches. -/
theorem concatenate {V : Type*} [DecidableEq V] (defaultVertex : V)
    (R S E : Finset (Sym2 V)) (dis : Disjoint R S) (unionEq : R ∪ S = E)
    (l : Fin R.card → Bool → V) (r : Fin S.card → Bool → V)
    (hl : ∀ i, (R.equivFin.symm i).val = s(l i false,l i true))
    (hr : ∀ i, (S.equivFin.symm i).val = s(r i false,r i true)) :
    ∃ p : ℕ → Bool → V, (∀ i : Fin R.card, ∀ b, p i.val b = l i b) ∧
      (∀ j : Fin S.card, ∀ b, p (R.card+j.val) b = r j b) ∧
      ∃ labels : Fin (R.card+S.card) ≃ ↥E,
        ∀ i, (labels i).val = s(p i.val false,p i.val true) := by
  classical
  let p (k : ℕ) (b : Bool) :=
    if h : k<R.card then l ⟨k,h⟩ b else if h' : k-R.card<S.card then r ⟨k-R.card,h'⟩ b else defaultVertex
  have left (i : Fin R.card) (b : Bool) : p i.val b = l i b := by simp [p,i.isLt]
  have right (i : Fin S.card) (b : Bool) : p (R.card+i.val) b = r i b := by
    have lo : ¬R.card+i.val<R.card := by omega
    simp [p,lo,i.isLt]
  have mem {e : Sym2 V} : e ∈ R.disjUnion S dis ↔ e ∈ E := by
    rw [← unionEq]; simp
  let finish : ↥(R.disjUnion S dis) ≃ ↥E :=
    ⟨fun x => ⟨x.val,mem.mp x.property⟩,fun x => ⟨x.val,mem.mpr x.property⟩,
     fun _ => rfl, fun _ => rfl⟩
  let labels := (finSumFinEquiv (m:=R.card) (n:=S.card)).symm.trans
    ((R.equivFin.symm.sumCongr S.equivFin.symm).trans ((Equiv.Finset.disjUnionEquiv R S dis).trans finish))
  refine ⟨p,left,right,labels,?_⟩
  intro i
  obtain ⟨z,rfl⟩ := (finSumFinEquiv (m:=R.card) (n:=S.card)).surjective i
  cases z with
  | inl j =>
    simpa [labels,Equiv.trans_apply,finSumFinEquiv_apply_left,finish,left] using hl j
  | inr j =>
    simpa [labels,Equiv.trans_apply,finSumFinEquiv_apply_right,finish,right] using hr j

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
