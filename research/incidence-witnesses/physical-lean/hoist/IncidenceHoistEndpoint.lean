import IncidenceHoistDisjoint
import IncidenceHoistCompile
namespace IncidenceHoistEndpoint
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow
open IncidenceHoistPrefix IncidenceHoistWalk IncidenceHoistReaders IncidenceHoistCompile
variable {n : ℕ} (C : Circuit n)

def endpoint (fuel w : ℕ) : ℕ :=
  match fuel with
  | 0 => w
  | f+1 => match step? C w with
    | none => w
    | some (j,_) => endpoint f (n+n+j)

theorem complete {raw : ℕ} {z : Input n} (fuel w : ℕ) (H : Finset ℕ)
    (p : Prefix C raw w H z) (enough : n+n+C.size ≤ max (n+n) (w+1) + fuel) :
    ∃ K, Prefix C raw (endpoint C fuel w) K z ∧ step? C (endpoint C fuel w)=none := by
  induction fuel generalizing w H with
  | zero =>
    refine ⟨H,p,?_⟩
    change step? C w=none
    cases eq : step? C w with
    | none => rfl
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,_⟩ := step_sound C eq
      have hi := later C q
      have bound := q.valid
      omega
  | succ f ih =>
    cases eq : step? C w with
    | none => simpa [endpoint,eq] using (show ∃ K, Prefix C raw w K z ∧ step? C w=none from ⟨H,p,eq⟩)
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,op⟩ := step_sound C eq
      have hi := later C q
      simpa [endpoint,eq] using ih _ _ (grow C p q op) (by omega)

theorem walk_reads (fuel w : ℕ) : ∀ e∈walk C fuel w,
    step? C (keep (C.code e.1) e.2)=some e := by
  induction fuel generalizing w with
  | zero => simp [walk]
  | succ f ih =>
    cases eq : step? C w with
    | none => simp [walk,eq]
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,_⟩ := step_sound C eq
      simp only [walk,eq,List.mem_cons]
      rintro a (rfl|ha)
      · exact q.reads.symm ▸ eq
      · exact ih _ a ha

theorem not_principal {line : Bool} {j endWire : ℕ} {b : Bool}
    (sel : select C line j=some b) (stop : step? C endWire=none) :
    keep (C.code j) b≠endWire := by
  obtain ⟨x,hx⟩ := selected_mem C sel
  have active := walk_reads C _ _ (j,b) hx
  intro eq
  change step? C (keep (C.code j) b)=some (j,b) at active
  rw [eq,stop] at active
  contradiction

theorem ref_stable (m : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) (t k i : ℕ)
    (early : i<m+t) : (buildPrefix m code sel (t+k)).ref i=(buildPrefix m code sel t).ref i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases e : sel (t+k) <;> simpa [buildPrefix,e,put,show i≠m+(t+k) by omega] using ih

theorem ref_gate (m s : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (js : j<s) (selected : sel j=some b) (before : keep (code j) b<m+j) :
    (buildPrefix m code sel s).ref (m+j)=(buildPrefix m code sel s).ref (keep (code j) b) := by
  have final (t i : ℕ) (ht : t≤s) (hi : i<m+t) :
      (buildPrefix m code sel s).ref i=(buildPrefix m code sel t).ref i := by
    have eq : s=t+(s-t) := by omega
    conv_lhs => rw [eq]
    exact ref_stable _ _ _ _ _ _ hi
  rw [final (j+1) (m+j) (by omega) (by omega), final j _ (by omega) before]
  simp [buildPrefix,selected,put]

theorem ref_walk (sel : ℕ → Option Bool) (fuel w : ℕ)
    (selected : ∀ e∈walk C fuel w, sel e.1=some e.2) :
    (buildPrefix (n+n) C.code sel C.size).ref (endpoint C fuel w)=
      (buildPrefix (n+n) C.code sel C.size).ref w := by
  induction fuel generalizing w with
  | zero => rfl
  | succ f ih =>
    cases eq : step? C w with
    | none => simp [endpoint,eq]
    | some e =>
      obtain ⟨j,b⟩ := e
      obtain ⟨q,_⟩ := step_sound C eq
      have active := selected (j,b) (by simp [walk,eq])
      have prev := ref_gate (n+n) C.size C.code sel j b q.valid active
        (q.reads.symm ▸ later C q)
      rw [q.reads] at prev
      simpa [endpoint,eq] using (ih (n+n+j) (fun e he => selected e (by simp [walk,eq,he]))).trans prev

#print axioms complete
#print axioms ref_walk
end IncidenceHoistEndpoint
