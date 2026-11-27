import IncidenceHoistShield
import IncidenceHoistFlow
namespace IncidenceHoistPrefix
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow IncidenceHoistSparse
variable {n : ℕ} (C : Circuit n)

structure Prefix (raw last : ℕ) (H : Finset ℕ) (z : Input n) : Prop where
  ownerInside : raw∈H
  latest : ∀ i∈H, i≤last
  hot : ∀ i∈H, z∈C.wire i
  member : last∈H
  leaves : ∀ j<C.size, ∀ b, keep (C.code j) b∈H →
    keep (C.code j) b=last ∨ n+n+j∈H

structure Next (last j : ℕ) (b : Bool) : Prop where
  valid : j<C.size
  reads : keep (C.code j) b=last
  unique : ∀ k<C.size, ∀ d, keep (C.code k) d=last → k=j ∧ d=b

theorem initial (raw : ℕ) (z : Input n) (h : z∈C.wire raw) : Prefix C raw raw {raw} z := by
  exact ⟨by simp, by simp, by simpa using h, by simp, fun _ _ _ h => Or.inl (Finset.mem_singleton.mp h)⟩

theorem later {last j : ℕ} {b : Bool} (u : Next C last j b) : last<n+n+j := by
  have h := C.earlier j u.valid
  rw [← u.reads]
  cases b
  · exact h.2
  · exact h.1

theorem grow {raw last j : ℕ} {H : Finset ℕ} {z : Input n} {b : Bool}
    (p : Prefix C raw last H z) (q : Next C last j b) (op : (C.code j).op=.join) :
    Prefix C raw (n+n+j) (insert (n+n+j) H) z := by
  refine ⟨Finset.mem_insert_of_mem p.ownerInside,?_,?_,Finset.mem_insert_self ..,?_⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact le_rfl
    · exact (p.latest i h).trans (later C q).le
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · rw [C.law j q.valid]
      have present := p.hot last p.member
      rw [← q.reads] at present
      cases b <;> simp only [keep,Bool.false_eq_true,if_true,if_false] at present <;>
        simp only [Gate.eval,op,Op.eval,Set.mem_union] <;> tauto
    · exact p.hot i h
  · intro k hk d read
    rcases Finset.mem_insert.mp read with h|h
    · exact Or.inl h
    · rcases p.leaves k hk d h with wasLast|inside
      · have atCut := (q.unique k hk d wasLast).1
        subst k
        exact Or.inr (Finset.mem_insert_self ..)
      · exact Or.inr (Finset.mem_insert_of_mem inside)

theorem shielding {line : Bool} {x : Fin n} {last j : ℕ} {b : Bool} {H : Finset ℕ} {z : Input n}
    (p : Prefix C (IncidenceHoistShield.owner line x) last H z)
    (q : Next C last j b) (op : (C.code j).op=.join) (rejected : z∉C.wire C.output) :
    Shield C line x (other (C.code j) b) := by
  have newOutside : n+n+j∉H := fun h => (Nat.not_lt_of_ge (p.latest _ h)) (later C q)
  have only (k : ℕ) (hk : k<C.size) (d : Bool) (outside : n+n+k∉H) (read : keep (C.code k) d∈H) :
      k=j ∧ d=b :=
    q.unique k hk d ((p.leaves k hk d read).resolve_right outside)
  have switch : other (C.code j) b = keep (C.code j) (!b) := by cases b <;> rfl
  apply IncidenceHoistShield.shield C line x H j _ q.valid p.ownerInside
    (fun h => rejected (p.hot _ h))
  · rw [switch]
    intro h
    have impossible := (only j q.valid (!b) newOutside h).2
    cases b <;> contradiction
  · intro k hk ne outside
    exact ⟨fun h => ne (only k hk true outside h).1,
      fun h => ne (only k hk false outside h).1⟩
  · exact op
  · cases b <;> simp [other]

#print axioms grow
#print axioms shielding
end IncidenceHoistPrefix
