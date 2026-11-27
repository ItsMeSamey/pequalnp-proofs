import IncidenceHoistWalk
namespace IncidenceHoistDisjoint
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistSparse IncidenceHoistFlow
open IncidenceHoistPrefix IncidenceHoistWalk
variable {n : ℕ} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
variable (degree : ∀ l, Fintype.card {p // I p l} = 401+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 401)

private theorem singleBound (x : Fin n) : Fintype.card {j // single x j=true} ≤ 1 := by
  let f : {j // single x j=true} → Unit := fun _ => ()
  have h : Function.Injective f := by
    intro a b _
    exact Subtype.ext ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  simpa using Fintype.card_le_of_injective f h

include degree unique pos neg in
theorem cold (hn : n=401^2+401+1) (line : Bool) (x y : Fin n) (sib : ℕ)
    (bound : sib<n+n+C.size) (shield : Shield C line x sib) :
    witness line y ∉ C.wire sib := by
  have one := singleBound y
  cases line
  · apply point_safe C I degree unique pos neg hn x sib bound shield (single y) (fun _ => false)
    · omega
    · simp
    · simp
  · apply line_safe C I degree unique pos neg x sib bound shield (fun _ => false) (single y)
    · omega
    · simp

include degree unique pos neg in
theorem no_opposite (hn : n=401^2+401+1) (line : Bool) (j : ℕ) (b d : Bool)
    (a : (j,b)∈pool C line) (c : (j,d)∈pool C line) : b=d := by
  obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp a
  obtain ⟨y,_,hy⟩ := List.mem_flatMap.mp c
  obtain ⟨_,valid,sh⟩ := walk_shields C (witness_neg C I neg line x) _ _ _
    (initial C _ _ (owner_hot C line x)) (j,b) hx
  have hit := walk_hot C _ _ _ (initial C _ _ (owner_hot C line y)) (j,d) hy
  have ⟨hl,hr⟩ := C.earlier j valid
  have bound : other (C.code j) b<n+n+C.size := by
    cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
  have no := cold C I degree unique pos neg hn line x y _ bound sh
  by_contra diff
  have eq : keep (C.code j) d = other (C.code j) b := by cases b <;> cases d <;> simp_all [keep,other]
  exact no (eq ▸ hit)

private theorem find_gate (xs : List (ℕ × Bool)) (j : ℕ) (b : Bool)
    (inside : (j,b)∈xs) (only : ∀ d, (j,d)∈xs → d=b) :
    xs.find? (fun e => decide (e.1=j))=some (j,b) := by
  induction xs with
  | nil => simp at inside
  | cons p xs ih =>
    obtain ⟨k,d⟩ := p
    by_cases same : k=j
    · subst k
      have db := only d (by simp)
      simp [List.find?,db]
    · have tail : (j,b)∈xs := (List.mem_cons.mp inside).resolve_left (by intro h; exact same (congrArg Prod.fst h).symm)
      have back := ih tail (fun v hv => only v (List.mem_cons_of_mem _ hv))
      simpa [List.find?,same] using back

include degree unique pos neg in
theorem chooses (hn : n=401^2+401+1) (line : Bool) (x : Fin n) (e : ℕ × Bool)
    (inWalk : e∈walk C C.size (IncidenceHoistShield.owner line x)) :
    select C line e.1=some e.2 := by
  obtain ⟨j,b⟩ := e
  have inPool : (j,b)∈pool C line := List.mem_flatMap.mpr ⟨x,by simp,inWalk⟩
  have pick := find_gate (pool C line) j b inPool (fun d hd =>
    no_opposite C I degree unique pos neg hn line j d b hd inPool)
  simp [select,pick]

#print axioms chooses
#print axioms no_opposite
end IncidenceHoistDisjoint
