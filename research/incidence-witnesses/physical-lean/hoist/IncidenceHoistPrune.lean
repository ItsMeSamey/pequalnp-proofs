import IncidenceHoistBinarySource
import Mathlib.Data.Finset.Sort

namespace IncidenceHoistPrune
open CircuitRewire SparseIncidence IncidenceStartNormalization
variable {n : Nat}

inductive Anc (C : Circuit n) : Nat → Prop
  | output : Anc C C.output
  | left (j : Nat) (valid : j<C.size) (parent : Anc C (n+n+j)) : Anc C (C.code j).left
  | right (j : Nat) (valid : j<C.size) (parent : Anc C (n+n+j)) : Anc C (C.code j).right

def Live (C : Circuit n) := ∀ j<C.size, Anc C (n+n+j)

private theorem bound {C : Circuit n} {i : Nat} (h : Anc C i) : i<n+n+C.size := by
  cases h with
  | output => exact C.output_lt
  | left j hj _ => have := (C.earlier j hj).1; omega
  | right j hj _ => have := (C.earlier j hj).2; omega

theorem prune (C : Circuit n) (bin : binary C) :
    ∃ D : Circuit n, D.size≤C.size ∧ binary D ∧ Live D ∧
      D.wire D.output=C.wire C.output ∧ ∀ i<n+n,D.wire i=C.wire i := by
  classical
  let m := n+n
  let K := (Finset.range C.size).filter (fun j => Anc C (m+j))
  let e : Fin K.card ≃o K := K.orderIsoOfFin rfl
  let enc : Nat → Nat := fun i => if i<m then i else
    if h : i-m ∈ K then m + (e.symm ⟨i-m,h⟩).val else 0
  let dec : Nat → Nat := fun i => if i<m then i else
    if h : i-m<K.card then m+(e ⟨i-m,h⟩).val else 0
  have alive {j : Nat} (hj : j∈K) : j<C.size ∧ Anc C (m+j) := by simpa [K] using hj
  have member {i : Nat} (hi : Anc C i) (lo : m≤i) : i-m∈K := by
    have sz := bound hi
    change i<m+C.size at sz
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [Nat.add_sub_of_le lo]⟩
  have en (j : K) : enc (m+j.val) = m+(e.symm j).val := by simp [enc,j.property]
  have de (k : Fin K.card) : dec (m+k.val) = m+(e k).val := by simp [dec,k.isLt]
  have inverse (i : Nat) (hi : Anc C i) : dec (enc i) = i := by
    by_cases h : i<m
    · simp [enc,dec,h]
    · let j : K := ⟨i-m,member hi (by omega)⟩
      have form : i=m+j.val := by dsimp [j]; omega
      calc
        dec (enc i) = dec (m+(e.symm j).val) := congrArg dec ((congrArg enc form).trans (en j))
        _ = m+(e (e.symm j)).val := de _
        _ = i := by rw [e.apply_symm_apply]; exact form.symm
  have earlier {i : Nat} (hi : Anc C i) (j : K) (before : i<m+j.val) :
      enc i < m+(e.symm j).val := by
    by_cases h : i<m
    · simp [enc,h]; omega
    · let k : K := ⟨i-m,member hi (by omega)⟩
      have form : i=m+k.val := by dsimp [k]; omega
      have lt : k<j := show k.val<j.val by omega
      rw [form,en]
      exact Nat.add_lt_add_left (e.symm.strictMono lt) m
  let code : Nat → Gate := fun k => if h : k<K.card then
    let g := C.code (e ⟨k,h⟩).val
    ⟨g.op,enc g.left,enc g.right⟩ else ⟨.zero,0,0⟩
  have cg (k : Fin K.card) : code k.val =
      ⟨(C.code (e k).val).op,enc (C.code (e k).val).left,enc (C.code (e k).val).right⟩ := by
    simp [code,k.isLt]
  have outBound : enc C.output < m+K.card := by
    by_cases h : C.output<m
    · simp [enc,h]; omega
    · let j : K := ⟨C.output-m,member Anc.output (by omega)⟩
      have form : C.output = m+j.val := by dsimp [j]; omega
      rw [form,en]
      exact Nat.add_lt_add_left (e.symm j).isLt m
  let D : Circuit n := {
    size := K.card
    output := enc C.output
    code := code
    wire := fun i => C.wire (dec i)
    output_lt := outBound
    earlier := by
      intro k hk
      let ix : Fin K.card := ⟨k,hk⟩
      let j := e ix
      obtain ⟨valid,anc⟩ := alive j.property
      obtain ⟨hl,hr⟩ := C.earlier j.val valid
      have l := earlier (Anc.left _ valid anc) j hl
      have r := earlier (Anc.right _ valid anc) j hr
      rw [cg ix]
      simpa only [j,e.symm_apply_apply] using And.intro l r
    law := by
      intro k hk
      let ix : Fin K.card := ⟨k,hk⟩
      let j := e ix
      obtain ⟨valid,anc⟩ := alive j.property
      change C.wire (dec (m+ix.val)) = (code ix.val).eval _
      rw [de ix,cg ix,C.law j.val valid]
      change (C.code j.val).op.eval (C.wire (C.code j.val).left) (C.wire (C.code j.val).right) =
        (C.code j.val).op.eval (C.wire (dec (enc (C.code j.val).left)))
          (C.wire (dec (enc (C.code j.val).right)))
      rw [inverse _ (Anc.left _ valid anc),inverse _ (Anc.right _ valid anc)]
    inputs := by
      intro i
      have lo : i.val<m := by dsimp [m]; omega
      have hi : n+i.val<m := by dsimp [m]; omega
      simpa [dec,lo,hi] using C.inputs i }
  have transfer {i : Nat} (h : Anc C i) : Anc D (enc i) := by
    induction h with
    | output => exact Anc.output
    | left j valid anc ih =>
      let a : K := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr valid,anc⟩⟩
      let k := e.symm a
      have mapped : enc (n+n+j) = m+k.val := en a
      rw [mapped] at ih
      have step := Anc.left (C := D) k.val k.isLt ih
      change Anc D (code k.val).left at step
      rw [cg k] at step
      simpa [k,a] using step
    | right j valid anc ih =>
      let a : K := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr valid,anc⟩⟩
      let k := e.symm a
      have mapped : enc (n+n+j) = m+k.val := en a
      rw [mapped] at ih
      have step := Anc.right (C := D) k.val k.isLt ih
      change Anc D (code k.val).right at step
      rw [cg k] at step
      simpa [k,a] using step
  refine ⟨D,?_,?_,?_,?_,?_⟩
  · change K.card ≤ C.size
    simpa using Finset.card_le_card (Finset.filter_subset (fun j => Anc C (m+j)) (Finset.range C.size))
  · intro k hk
    let a : Fin K.card := ⟨k,hk⟩
    change (code k).op = .join ∨ (code k).op = .meet
    rw [cg a]
    exact bin _ (alive (e a).property).1
  · intro k hk
    let a : Fin K.card := ⟨k,hk⟩
    have h := transfer (alive (e a).property).2
    rw [en,e.symm_apply_apply] at h
    exact h
  · exact congrArg C.wire (inverse _ Anc.output)
  · intro i hi
    change C.wire (dec i) = C.wire i
    simp [dec,show i<m from hi]

theorem source_live (C : Circuit n) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hn : n=401^2+401+1) (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (pos : flags C I) (neg : negatives C I n 401) :
    ∃ D : Circuit n, D.size≤C.size ∧ binary D ∧ Live D ∧
      D.wire D.output=C.wire C.output ∧ (∀ i<n+n,D.wire i=C.wire i) ∧
      flags D I ∧ negatives D I n 401 := by
  obtain ⟨B,hB,bin,out,raw,_,_⟩ := IncidenceHoistBinarySource.source C I hn degree pos neg
  obtain ⟨D,hD,ops,live,outD,rawD⟩ := prune B bin
  refine ⟨D,hD.trans hB,ops,live,outD.trans out,fun i hi => (rawD i hi).trans (raw i hi),?_,?_⟩
  · intro p l h
    rw [outD,out]
    exact pos p l h
  · intro a b ha hb h
    rw [outD,out]
    exact neg a b ha hb h

#print axioms source_live
#print axioms prune
end IncidenceHoistPrune
