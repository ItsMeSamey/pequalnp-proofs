import IncidenceHoistPrefix
import IncidenceHoistReaders
namespace IncidenceHoistWalk
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow IncidenceHoistSparse
open IncidenceHoistPrefix IncidenceHoistReaders
variable {n : ℕ} (C : Circuit n)

def step? (w : ℕ) : Option (ℕ × Bool) := do
  let (j,b) ← reader? C w
  if uses C w=1 ∧ (C.code j).op=.join then some (j,b) else none

theorem step_sound {w j : ℕ} {b : Bool} (h : step? C w=some (j,b)) :
    Next C w j b ∧ (C.code j).op=.join := by
  unfold step? at h
  cases e : reader? C w with
  | none => simp [e] at h
  | some p =>
    obtain ⟨k,d⟩ := p
    simp only [e,bind,Option.bind] at h
    split at h
    next yes =>
      cases h
      obtain ⟨a,c,f,v,r,u⟩ := unique_reader C w yes.1
      rw [e] at f
      cases f
      exact ⟨⟨v,r,u⟩,yes.2⟩
    next => contradiction

def walk (fuel w : ℕ) : List (ℕ × Bool) :=
  match fuel with
  | 0 => []
  | f+1 => match step? C w with
    | none => []
    | some (j,b) => (j,b) :: walk f (n+n+j)

theorem walk_shields {line : Bool} {x : Fin n} {z : Input n}
    (rejected : z∉C.wire C.output) (fuel w : ℕ) (H : Finset ℕ)
    (p : Prefix C (IncidenceHoistShield.owner line x) w H z) :
    ∀ e∈walk C fuel w, (C.code e.1).op=.join ∧ e.1<C.size ∧
      Shield C line x (other (C.code e.1) e.2) := by
  induction fuel generalizing w H with
  | zero => simp [walk]
  | succ f ih =>
    cases eq : step? C w with
    | none => simp [walk,eq]
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,op⟩ := step_sound C eq
      simp only [walk,eq,List.mem_cons]
      rintro a (rfl|tail)
      · exact ⟨op,q.valid,shielding C p q op rejected⟩
      · exact ih _ _ (grow C p q op) a tail

theorem walk_hot {raw : ℕ} {z : Input n} (fuel w : ℕ) (H : Finset ℕ)
    (p : Prefix C raw w H z) :
    ∀ e∈walk C fuel w, z∈C.wire (keep (C.code e.1) e.2) := by
  induction fuel generalizing w H with
  | zero => simp [walk]
  | succ f ih =>
    cases eq : step? C w with
    | none => simp [walk,eq]
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,op⟩ := step_sound C eq
      simp only [walk,eq,List.mem_cons]
      rintro a (rfl|tail)
      · exact q.reads.symm ▸ p.hot w p.member
      · exact ih _ _ (grow C p q op) a tail

def pool (line : Bool) : List (ℕ × Bool) :=
  (List.finRange n).flatMap fun x =>
    walk C C.size (IncidenceHoistShield.owner line x)

def select (line : Bool) (j : ℕ) : Option Bool :=
  ((pool C line).find? (fun e => decide (e.1=j))).map Prod.snd

theorem selected_mem {line : Bool} {j : ℕ} {b : Bool} (h : select C line j=some b) :
    ∃ x : Fin n, (j,b) ∈ walk C C.size (IncidenceHoistShield.owner line x) := by
  unfold select at h
  cases eq : (pool C line).find? (fun e => decide (e.1=j)) with
  | none => simp [eq] at h
  | some e =>
    obtain ⟨k,d⟩ := e
    have hit := List.find?_some eq
    have mem := List.mem_of_find?_eq_some eq
    simp [eq] at h
    have kj : k=j := of_decide_eq_true hit
    subst k
    subst d
    obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp mem
    exact ⟨x,hx⟩

def witness (line : Bool) (x : Fin n) : Input n :=
  if line then (fun _ => false,single x) else (single x,fun _ => false)

theorem owner_hot (line : Bool) (x : Fin n) :
    witness line x ∈ C.wire (IncidenceHoistShield.owner line x) := by
  cases line
  · rw [(show IncidenceHoistShield.owner false x=x.val from rfl),(C.inputs x).1]
    simp [witness,single]
  · rw [(show IncidenceHoistShield.owner true x=n+x.val from rfl),(C.inputs x).2]
    simp [witness,single]

theorem witness_neg (I : Fin n→Fin n→Prop) (neg : negatives C I n 401) (line : Bool) (x : Fin n) :
    witness line x ∉ C.wire C.output := by
  have one : Fintype.card {j // single x j=true} ≤ 1 := by
    let f : {j // single x j=true} → Unit := fun _ => ()
    have h : Function.Injective f := by
      intro a b _
      apply Subtype.ext
      exact (of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm
    simpa using Fintype.card_le_of_injective f h
  cases line
  · apply neg
    · exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    · simp
    · simp
  · apply neg
    · simp
    · omega
    · simp

theorem selected_safe {I : Fin n→Fin n→Prop} (neg : negatives C I n 401)
    {line : Bool} {j : ℕ} {b : Bool} (h : select C line j=some b) :
    ∃ x : Fin n, (C.code j).op=.join ∧ j<C.size ∧
      Shield C line x (other (C.code j) b) := by
  obtain ⟨x,hx⟩ := selected_mem C h
  exact ⟨x,walk_shields C (witness_neg C I neg line x) _ _ _
    (initial C _ _ (owner_hot C line x)) (j,b) hx⟩

#print axioms walk_shields
#print axioms selected_safe
end IncidenceHoistWalk
