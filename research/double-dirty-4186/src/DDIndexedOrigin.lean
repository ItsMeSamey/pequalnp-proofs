import DDIndexedRows

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
attribute [local instance] gateOpDecEq

def address (n : ℕ) (C : Circuit) (p : Cuts) : Origin → ℕ
  | .input i => i
  | .gate j => n + rank n C p j

private def OK (n : ℕ) (C : Circuit) (p : Cuts) (r : Ref) : Prop :=
  ∀ a, r = some a → a.2 = address n C p a.1

private theorem get_ok {n : ℕ} {C : Circuit} {p : Cuts} (s : State)
    (H : ∀ r ∈ s.refs, OK n C p r) (w : ℕ) : OK n C p (ref s w) := by
  by_cases hw : w < s.refs.length
  · unfold ref
    rw [List.getD_eq_getElem _ _ hw]
    exact H _ (List.getElem_mem hw)
  · unfold ref
    rw [List.getD_eq_default _ _ (by omega)]
    simp [OK]

private theorem pin_ok {n : ℕ} {C : Circuit} {p : Cuts} (s : State)
    (H : ∀ r ∈ s.refs, OK n C p r) (j : ℕ) (b : Fin 2) : OK n C p (pin s n C p j b) := by
  simp only [pin]
  split
  · simp [OK]
  · exact get_ok s H _

private theorem dest_ok (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) (op : GateOp)
    (skip : Bool) (l r : Ref) (hl : OK n C p l) (hr : OK n C p r) :
    OK n C p (dest op skip j (n+rank n C p j) l r) := by
  cases skip <;> cases l <;> cases r <;> by_cases h : op = .and <;>
    simp_all [OK,dest,address,Option.orElse]

private theorem refs_ok (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    ∀ r ∈ (build n C p k).refs, OK n C p r := by
  induction k with
  | zero =>
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    simp [OK,address]
  | succ k ih =>
    intro r hr
    change r ∈ _ ++ [_] at hr
    rcases List.mem_append.mp hr with old | last
    · exact ih _ old
    · obtain rfl := List.mem_singleton.mp last
      exact dest_ok n C p k _ _ _ _ (pin_ok _ ih k 0) (pin_ok _ ih k 1)

theorem ref_address {n k w v : ℕ} {C : Circuit} {p : Cuts} {o : Origin}
    (h : ref (build n C p k) w = some (o,v)) : v = address n C p o :=
  get_ok _ (refs_ok n C p k) w _ h

theorem pin_address {n k v : ℕ} {C : Circuit} {p : Cuts} {b : Fin 2} {o : Origin}
    (h : pin (build n C p k) n C p k b = some (o,v)) : v = address n C p o :=
  pin_ok _ (refs_ok n C p k) k b _ h

theorem producer_ref {n k w i : ℕ} {C : Circuit} {p : Cuts}
    (h : producer (build n C p k) w = some i) :
    ref (build n C p k) w = some (.gate i,n+rank n C p i) := by
  unfold producer at h
  cases hr : ref (build n C p k) w with
  | none => simp [hr] at h
  | some t =>
    rcases t with ⟨o,v⟩
    cases o with
    | input j => simp [hr] at h
    | gate j =>
      simp [hr] at h
      subst i
      have hv := ref_address hr
      simp_all [address]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
