import IncidenceStartNormalization

namespace IncidenceHoistBinarySource
open CircuitRewire SparseIncidence IncidenceStartNormalization
variable {n : Nat}

/-- Forward copies and constant-zero signals at their literal references.
Original inputs retain their physical labels. -/
theorem exists_binary (C : Circuit n) (live : (C.wire C.output).Nonempty) :
    ∃ D : Circuit n, D.size≤C.size ∧ binary D ∧ D.wire D.output=C.wire C.output ∧
      ∀ i<n+n,D.wire i=C.wire i := by
  let m := n+n
  let pg := compile m m C.code some C.size
  obtain ⟨_,bound,norm,Y,inputs,gates,allRef⟩ := compile_correct m m C.size C.code some C.wire C.wire
    (fun j hj k eq => by cases eq; exact hj) (fun _ _ => rfl) C.earlier C.law
  have sem := allRef C.output C.output_lt
  change C.wire C.output = read Y (pg.refs C.output) at sem
  cases h : pg.refs C.output with
  | none =>
    rw [h] at sem
    exact ((Set.nonempty_iff_ne_empty.mp live) sem).elim
  | some out =>
    rw [h] at sem
    let D : Circuit n := ⟨pg.size,out,pg.code,Y,bound C.output C.output_lt out h,
      fun j hj => ⟨(norm j hj).1,(norm j hj).2.1⟩,gates,fun i => by
        have l := inputs i.val (by dsimp [m]; omega)
        have r := inputs (n+i.val) (by dsimp [m]; omega)
        exact ⟨l.trans (C.inputs i).1,r.trans (C.inputs i).2⟩⟩
    exact ⟨D,compile_size ..,fun j hj => (norm j hj).2.2.2,sem.symm,inputs⟩

theorem source (C : Circuit n) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hn : n=401^2+401+1) (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (pos : flags C I) (neg : negatives C I n 401) :
    ∃ D : Circuit n, D.size≤C.size ∧ binary D ∧ D.wire D.output=C.wire C.output ∧
      (∀ i<n+n,D.wire i=C.wire i) ∧ flags D I ∧ negatives D I n 401 := by
  let l : Fin n := ⟨0,by omega⟩
  have populated : Nonempty {p // I p l} := Fintype.card_pos_iff.mp (by rw [degree]; decide)
  obtain ⟨⟨p,inc⟩⟩ := populated
  obtain ⟨D,size,ops,out,inputs⟩ := exists_binary C ⟨_,pos p l inc⟩
  refine ⟨D,size,ops,out,inputs,?_,?_⟩
  · intro p l inc
    rw [out]
    exact pos p l inc
  · intro a b pa lb independent
    rw [out]
    exact neg a b pa lb independent

#print axioms exists_binary
#print axioms source
end IncidenceHoistBinarySource
