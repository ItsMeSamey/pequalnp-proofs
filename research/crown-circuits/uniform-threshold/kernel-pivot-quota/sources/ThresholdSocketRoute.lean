import ThresholdPhysicalFirstCut
namespace ThresholdSocketRoute
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition T2SoleOrSplice
open ThresholdEffectiveColumns ThresholdLeakPins
variable {C : Circuit} {n : Nat} (L : Layout C n)

private theorem after_start {i ps z} (w : Walk L i ps z) {q : Pin C} (mem : q∈ps) :
    i<q.1 := by
  induction w with
  | nil => simp at mem
  | cons e _ ih =>
    rcases List.mem_cons.mp mem with rfl | h
    · exact feeds_later L e
    · exact lt_trans (feeds_later L e) (ih h)

private theorem walk_nodup {i ps z} (w : Walk L i ps z) (p : Pin C) (start : p.1=i) :
    ((p::ps).map Prod.fst).Nodup := by
  induction w generalizing p with
  | nil => simp
  | cons e rest ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro eq
      obtain ⟨q,hq,eq⟩ := List.mem_map.mp (show p.1∈(_::_).map Prod.fst from eq)
      have lt := after_start L (.cons e rest) hq
      rw [eq,start] at lt
      exact lt_irrefl _ lt
    · exact ih _ rfl

private theorem follow {i ps z} (w : Walk L i ps z) (M : LexMinimum n C)
    (mark : boundary (n:=n) z) (p : Pin C) (start : p.1=i)
    {q r : Pin C} (old : q∈p::ps) (off : ¬boundary (n:=n) q.1)
    (edge : feeds L q.1 r) : r∈p::ps := by
  induction w generalizing p with
  | nil =>
    have eq : q=p := List.mem_singleton.mp old
    subst q
    exact (off (start.symm ▸ mark)).elim
  | @cons i a ps z e rest ih =>
    rcases List.mem_cons.mp old with eq | mem
    · subst q
      rw [start] at edge off
      have uniq := (unmarked_step L M i off).choose_spec.2.2
      have same := (uniq r edge).trans (uniq a e).symm
      simp [same]
    · exact List.mem_cons_of_mem _ (ih mark a rfl mem)

noncomputable def route (M : LexMinimum n C) (p : Pin C) : List (Pin C) :=
  p::(trace L M p.1).1

theorem unique_rows (M : LexMinimum n C) (p : Pin C) :
    ((route L M p).map Prod.fst).Nodup :=
  walk_nodup L (trace_ok L M p.1).1 p rfl

theorem next_mem (M : LexMinimum n C) (p : Pin C) {q r : Pin C}
    (old : q∈route L M p) (off : ¬boundary (n:=n) q.1) (edge : feeds L q.1 r) :
    r∈route L M p :=
  follow L (trace_ok L M p.1).1 M (trace_ok L M p.1).2 p rfl old off edge

theorem side_unique {ps : List (Pin C)} (unique : (ps.map Prod.fst).Nodup)
    {a b : Pin C} (ha : a∈ps) (hb : b∈ps) (eq : a.1=b.1) : a=b := by
  induction ps with
  | nil => simp at ha
  | cons p tail ih =>
    obtain ⟨out,distinct⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp ha with rfl|haTail <;> rcases List.mem_cons.mp hb with rfl|hbTail
    · rfl
    · exact (out (List.mem_map.mpr ⟨_,hbTail,eq.symm⟩)).elim
    · exact (out (List.mem_map.mpr ⟨_,haTail,eq⟩)).elim
    · exact ih distinct haTail hbTail

end ThresholdSocketRoute
