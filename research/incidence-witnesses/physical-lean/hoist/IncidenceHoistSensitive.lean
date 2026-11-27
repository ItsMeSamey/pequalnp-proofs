import IncidenceHoistWalk

namespace IncidenceHoistSensitive
open CircuitRewire SparseIncidence IncidenceStartNormalization IncidenceHoistSparse
open IncidenceHoistPrefix IncidenceHoistWalk IncidenceHoistShield IncidenceHoistFlow
open IncidenceHoistReaders
variable {n : Nat} (C : Circuit n) (I : Fin n → Fin n → Prop)

theorem output_ne_owner (neg : negatives C I n 401) (line : Bool) (x : Fin n) :
    C.output ≠ owner line x := by
  intro eq
  exact witness_neg C I neg line x (eq.symm ▸ owner_hot C line x)

theorem output_not_raw (neg : negatives C I n 401) (i : Nat) (hi : i<n+n) :
    C.output ≠ i := by
  by_cases left : i<n
  · exact output_ne_owner C I neg false ⟨i,left⟩
  · let x : Fin n := ⟨i-n,by omega⟩
    have form : i = owner true x := by change i=n+(i-n); omega
    rw [form]
    exact output_ne_owner C I neg true x

private theorem agree_raw (line : Bool) (x : Fin n) (u v : Input n) (agr : AgreeOff line x u v)
    (i : Nat) (hi : i<n+n) (ne : i ≠ owner line x) : u∈C.wire i ↔ v∈C.wire i := by
  by_cases lo : i<n
  · let j : Fin n := ⟨i,lo⟩
    rw [(C.inputs j).1]
    cases line
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.2 j (fun eq => ne (congrArg Fin.val eq))]
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.1]
  · let j : Fin n := ⟨i-n,by omega⟩
    have form : i=n+j.val := by dsimp [j]; omega
    rw [form,(C.inputs j).2]
    cases line
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.1]
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.2 j (by intro eq; apply ne; change i=n+x.val; rw [← eq]; exact form)]

private theorem no_escape (line : Bool) (x : Fin n) {w : Nat} {H : Finset Nat}
    (p : Prefix C (owner line x) w H (witness line x)) (dead : uses C w = 0)
    (u v : Input n) (agr : AgreeOff line x u v) :
    ∀ i<n+n+C.size, i∉H → (u∈C.wire i ↔ v∈C.wire i) := by
  have empty : occurrences C w = [] :=
    List.length_eq_zero_iff.mp ((occurrence_count C w).trans dead)
  have parent (j : Nat) (hj : j<C.size) (b : Bool) (outside : n+n+j∉H) :
      keep (C.code j) b ∉ H := by
    intro h
    have eq := (p.leaves j hj b h).resolve_right outside
    have mem := (occurrence_mem C w j b).mpr ⟨hj,eq⟩
    rw [empty] at mem
    exact List.not_mem_nil mem
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro good outside
    by_cases raw : i<n+n
    · exact agree_raw C line x u v agr i raw (fun eq => outside (eq ▸ p.ownerInside))
    let j := i-(n+n)
    have atGate : i=n+n+j := by dsimp [j]; omega
    have valid : j<C.size := by omega
    obtain ⟨hl,hr⟩ := C.earlier j valid
    have l := ih (C.code j).left (by omega) (by omega) (parent j valid true (atGate ▸ outside))
    have r := ih (C.code j).right (by omega) (by omega) (parent j valid false (atGate ▸ outside))
    rw [atGate,C.law j valid]
    cases op : (C.code j).op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto

theorem exit_used_of_neighbor (neg : negatives C I n 401) (pos : flags C I) (line : Bool)
    (x y : Fin n) (inc : if line then I y x else I x y) {w : Nat} {H : Finset Nat}
    (p : Prefix C (owner line x) w H (witness line x)) : 0 < uses C w := by
  by_contra! dead
  have zero : uses C w=0 := by omega
  have out : C.output∉H := fun h => witness_neg C I neg line x (p.hot _ h)
  cases line
  · let u : Input n := (single x,single y)
    have agree : AgreeOff false x u (witness true y) := by
      refine ⟨rfl,?_⟩
      intro i ne
      simp [u,witness,single,ne]
    have same := no_escape C false x p zero _ _ agree C.output C.output_lt out
    exact witness_neg C I neg true y (same.mp (pos x y inc))
  · let u : Input n := (single y,single x)
    have agree : AgreeOff true x u (witness false y) := by
      refine ⟨rfl,?_⟩
      intro i ne
      simp [u,witness,single,ne]
    have same := no_escape C true x p zero _ _ agree C.output C.output_lt out
    exact witness_neg C I neg false y (same.mp (pos y x inc))

theorem exit_used [DecidableRel I] (hn : n=401^2+401+1)
    (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    (neg : negatives C I n 401) (pos : flags C I) (line : Bool) (x : Fin n)
    {w : Nat} {H : Finset Nat} (p : Prefix C (owner line x) w H (witness line x)) :
    0 < uses C w := by
  cases line
  · obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < (IncidenceRobust.lines I x).card by
      rw [IncidenceRobust.lines_card I degree unique (by decide : 0<401) hn]; decide)
    exact exit_used_of_neighbor C I neg pos false x y (Finset.mem_filter.mp hy).2 p
  · obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < (IncidenceRobust.points I x).card by
      rw [IncidenceRobust.points_card I degree]; decide)
    exact exit_used_of_neighbor C I neg pos true x y (Finset.mem_filter.mp hy).2 p

#print axioms exit_used
#print axioms output_not_raw
end IncidenceHoistSensitive
