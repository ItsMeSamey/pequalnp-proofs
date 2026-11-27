import IncidenceCleanupLabels
namespace IncidenceCleanupGate
open CircuitRewire IncidenceForwardPins IncidenceSurvivingReads IncidenceLabelHistory IncidenceCleanupLabels
def compressed (k j : ℕ) := if j<k then j else j-1
def original (k i : ℕ) := if i<k then i else i+1
def rewire (m k replacement w : ℕ) :=
  if w<m+k then w else if w=m+k then replacement else w-1
def eraseGate (m k replacement : ℕ) (g : ℕ→Gate) (i : ℕ) : Gate :=
  let G := g (original k i)
  ⟨G.op,rewire m k replacement G.left,rewire m k replacement G.right⟩
theorem backward {k j : ℕ} (ne : j≠k) : original k (compressed k j)=j := by
  by_cases lo : j<k
  · simp [original,compressed,lo]
  · have no : ¬j-1<k := by omega
    simp [original,compressed,lo,no]; omega

theorem shock (m s k replacement : ℕ) (g : ℕ→Gate) (L : Finset ℕ)
    (ks : k<s) (raw : L⊆Finset.range m) :
    let h := eraseGate m k replacement g
    (drops (snap s g L) (snap (s-1) h L) ∪ andLost (snap s g L) (snap (s-1) h L)).card≤2 := by
  let h := eraseGate m k replacement g
  let map := fun p : Pin=>(compressed k p.1,p.2)
  have neq {p : Pin} (ok : p.1∉({k} : Finset ℕ)) : p.1≠k := by simpa using ok
  have keep : ∀p∈pins s,p.1∉({k} : Finset ℕ) → readPin g p∈L →
      map p∈pins (s-1) ∧ readPin h (map p)=readPin g p := by
    intro p hp hk hl
    have old := (mem_pins p s).mp hp
    have ne := neq hk
    have lab := Finset.mem_range.mp (raw hl)
    constructor
    · apply (mem_pins _ _).mpr
      change compressed k p.1<s-1
      unfold compressed
      split <;> omega
    · change (if p.2 then (h (compressed k p.1)).right else (h (compressed k p.1)).left)=readPin g p
      unfold h eraseGate
      rw [backward ne]
      cases bit : p.2 <;> simp [readPin,bit] at lab ⊢
      · simp [rewire,show (g p.1).left<m+k by omega]
      · simp [rewire,show (g p.1).right<m+k by omega]
  have inj : Set.InjOn map (↑((pins s).filter (fun p=>p.1∉({k} : Finset ℕ))) : Set Pin) := by
    intro p hp q hq eq
    have a := neq (Finset.mem_filter.mp hp).2
    have b := neq (Finset.mem_filter.mp hq).2
    have left : compressed k p.1=compressed k q.1 := congrArg Prod.fst eq
    have right : (map p).2=(map q).2 := congrArg Prod.snd eq
    exact Prod.ext ((backward a).symm.trans ((congrArg (original k) left).trans (backward b))) right
  have survives : ∀p∈pins s,p.1∉({k} : Finset ℕ) → (g p.1).op=.meet → (h (map p).1).op=.meet := by
    intro p _ hk op
    simpa [h,map,eraseGate,backward (neq hk)] using op
  simpa [h] using bill g h s (s-1) L L {k} map keep inj survives
#print axioms shock
end IncidenceCleanupGate
