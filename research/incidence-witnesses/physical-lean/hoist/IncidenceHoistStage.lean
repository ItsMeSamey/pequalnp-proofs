import IncidenceHoistWalk
import IncidenceHoistRealize
namespace IncidenceHoistStage
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow
open IncidenceHoistSparse IncidenceHoistWalk IncidenceHoistCompile IncidenceHoistRealize
variable {n : ℕ} (C : Circuit n) (I : Fin n → Fin n → Prop) [DecidableRel I]

def transform (line : Bool) := circuit C (select C line)

theorem budget (line : Bool) : (transform C line).size=C.size := rfl

private def bin (g : Gate) := g.op=.join ∨ g.op=.meet

private theorem kept_binary (sel : ℕ→Option Bool) (t : ℕ) (ht : t≤C.size) (old : binary C) :
    ∀ g∈(buildPrefix (n+n) C.code sel t).kept, bin g := by
  induction t with
  | zero => simp [buildPrefix]
  | succ t ih =>
    cases e : sel t with
    | some b => simpa only [buildPrefix,e] using ih (by omega)
    | none =>
      intro g hg
      simp only [buildPrefix,e,List.mem_append,List.mem_singleton] at hg
      rcases hg with prev|rfl
      · exact ih (by omega) g prev
      · exact old t (by omega)

private theorem joins_binary (k a : ℕ) (xs : List ℕ) : ∀ g∈appendJoins k a xs, bin g := by
  induction xs generalizing k a with
  | nil => simp [appendJoins]
  | cons x xs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|tail
    · exact Or.inl rfl
    · exact ih _ _ g tail

theorem ops (line : Bool) (old : binary C) : binary (transform C line) := by
  let sel := select C line
  let gs := codeList (n+n) C.size C.output C.code sel
  intro j hj
  have jl : j<gs.length := by
    rw [show gs.length=C.size from physical_size ..]
    exact hj
  change bin (gs.getD j ⟨.zero,0,0⟩)
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem jl,Option.getD_some]
  have mem : gs[j]∈gs := List.getElem_mem ..
  rcases List.mem_append.mp mem with kept|extra
  · exact kept_binary C sel C.size le_rfl old _ kept
  · exact joins_binary _ _ _ _ extra

/-- Actual output sandwich, specialized to deterministic simultaneous spine selection. -/
theorem output_bounds (neg : negatives C I n 401) (line : Bool) :
    C.wire C.output ⊆ (transform C line).wire (transform C line).output ∧
    (transform C line).wire (transform C line).output ⊆ C.wire C.output ∪
      lost C.size C.code (select C line) C.wire := by
  let sel := select C line
  let Y := value C.wire C.code sel (n+n) C.size
  have op (j : ℕ) (_ : j<C.size) (b : Bool) (h : sel j=some b) : (C.code j).op=.join := by
    obtain ⟨_,join,_,_⟩ := selected_safe C neg h
    exact join
  have hs := sandwich (n+n) C.size C.wire C.code sel C.earlier C.law op
  have he : (transform C line).wire (transform C line).output=Y C.output ∪ lost C.size C.code sel Y :=
    realize C sel
  rw [he]
  refine ⟨(hs _ C.output_lt).2,?_⟩
  rintro z (old|⟨j,hj,b,hb,hit⟩)
  · exact Or.inl ((hs _ C.output_lt).1 old)
  · have ⟨l,r⟩ := C.earlier j hj
    have bound : other (C.code j) b<n+n+C.size := by
      cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
    exact Or.inr ⟨j,hj,b,hb,(hs _ bound).1 hit⟩

theorem positive (neg : negatives C I n 401) (pos : flags C I) (line : Bool) :
    flags (transform C line) I := fun p l inc => (output_bounds C I neg line).1 (pos p l inc)

variable (degree : ∀ l, Fintype.card {p // I p l} = 401+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 401)

include degree unique pos neg in
theorem line_negative : negatives (transform C true) I n 401 := by
  intro a b ha hb ind present
  rcases (output_bounds C I neg true).2 present with old|⟨j,hj,d,hd,hit⟩
  · exact neg a b ha hb ind old
  · obtain ⟨x,_,_,shield⟩ := selected_safe C neg hd
    have ⟨l,r⟩ := C.earlier j hj
    have valid : other (C.code j) d<n+n+C.size := by
      cases d <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
    exact line_safe C I degree unique pos neg x _ valid shield a b hb ind hit

include degree unique pos neg in
theorem point_negative (hn : n=401^2+401+1) :
    negatives (transform C false) I 401 400 := by
  intro a b ha hb ind present
  rcases (output_bounds C I neg false).2 present with old|⟨j,hj,d,hd,hit⟩
  · exact neg a b (by omega) (by omega) ind old
  · obtain ⟨x,_,_,shield⟩ := selected_safe C neg hd
    have ⟨l,r⟩ := C.earlier j hj
    have valid : other (C.code j) d<n+n+C.size := by
      cases d <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
    exact point_safe C I degree unique pos neg hn x _ valid shield a b ha hb ind hit

#print axioms positive
#print axioms line_negative
#print axioms point_negative
end IncidenceHoistStage
