import IncidenceOperandLedger

namespace IncidenceForwardPins
open CircuitRewire
abbrev Pin := ℕ × Bool
def readPin (g : ℕ → Gate) (p : Pin) : ℕ :=
  if p.2 then (g p.1).right else (g p.1).left

/-- Trace a receiving pin backwards through the unique high input of a bypass OR.
    Every outgoing copy of a gate names the same predecessor, irrespective of fanout. -/
def predPin (n : ℕ) (g : ℕ → Gate) (z : ℕ → Bool) (p : Pin) : Option Pin :=
  let w := readPin g p
  if w < n then none else
    let j := w-n
    let G := g j
    if G.op = .join ∧ z G.left ≠ z G.right then some (j,z G.left) else none

theorem raw_start (g : ℕ → Gate) (z : ℕ → Bool) (n : ℕ) (p : Pin)
    (h : readPin g p < n) : predPin n g z p=none := by simp [predPin,h]

inductive Route (pred : Pin → Option Pin) (start : Pin) : Pin → Prop
  | here : Route pred start start
  | next {p t} : Route pred start p → pred t=some p → Route pred start t

theorem unique_start {pred : Pin → Option Pin} {a b t : Pin}
    (ha : pred a=none) (hb : pred b=none)
    (ra : Route pred a t) (rb : Route pred b t) : a=b := by
  induction ra with
  | here =>
    cases rb with
    | here => rfl
    | next _ h => simp [ha] at h
  | next r h ih =>
    cases rb with
    | here => simp [hb] at h
    | next r' h' =>
      have eq := Option.some.inj (h.symm.trans h')
      cases eq
      exact ih r'

theorem terminal_injective (n : ℕ) (g : ℕ → Gate) (z : ℕ → Bool)
    (S : Finset Pin) (raw : ∀p∈S,readPin g p<n)
    (finish : Pin → Pin) (route : ∀p∈S,Route (predPin n g z) p (finish p)) :
    Set.InjOn finish (S : Set Pin) := by
  intro p hp q hq eq
  apply unique_start (raw_start g z n p (raw p hp)) (raw_start g z n q (raw q hq)) (route p hp)
  rw [eq]
  exact route q hq

/-- The distinguished high socket of a one-zero AND is unique per physical gate. -/
theorem high_socket_injective (g : ℕ → Gate) (z : ℕ → Bool) (P : Finset Pin)
    (mode : ∀p∈P,p.2=z (g p.1).left) :
    Set.InjOn Prod.fst (P : Set Pin) := by
  intro p hp q hq h
  apply Prod.ext h
  rw [mode p hp,mode q hq,h]
def bypass (g : ℕ → Gate) (z : ℕ → Bool) (j : ℕ) : Prop :=
  (g j).op=.join ∧ z (g j).left ≠ z (g j).right

theorem forward_pin (n : ℕ) (g : ℕ → Gate) (z : ℕ → Bool) (p q : Pin)
    (hi : z (readPin g p)=false) (atGate : bypass g z p.1)
    (out : readPin g q=n+p.1) : predPin n g z q=some p := by
  rcases p with ⟨j,side⟩
  change (g j).op=.join ∧ z (g j).left ≠ z (g j).right at atGate
  have sideEq : z (g j).left=side := by
    cases side <;> cases l : z (g j).left <;> cases r : z (g j).right <;>
      simp_all [readPin]
  have jr : readPin g q=n+j := out
  have ne : side ≠ z (g j).right := sideEq ▸ atGate.2
  simp [predPin,jr,atGate.1,sideEq,ne]

theorem append {pred : Pin → Option Pin} {u v w : Pin}
    (x : Route pred u v) (y : Route pred v w) : Route pred u w := by
  induction y with
  | here => exact x
  | next _ e ih => exact .next ih e

/-- The output exception is returned explicitly for discharge by test semantics. -/
theorem live_route (n s out : ℕ) (g : ℕ → Gate) (z : ℕ → Bool)
    (live : ∀ j<s, j≠out → ∃ q : Pin, j<q.1 ∧ q.1<s ∧ readPin g q=n+j)
    (eval : ∀ j<s,z (n+j)=IncidenceOperandLedger.zeroAt z (g j))
    (p : Pin) (small : p.1<s) (high : z (readPin g p)=false) :
    ∃ t : Pin, Route (predPin n g z) p t ∧ t.1<s ∧ z (readPin g t)=false ∧
      (¬bypass g z t.1 ∨ t.1=out) := by
  classical
  by_cases h : bypass g z p.1
  · by_cases o : p.1=out
    · exact ⟨p,.here,small,high,Or.inr o⟩
    obtain ⟨q,l,b,eq⟩ := live p.1 small o
    have next := forward_pin n g z p q high h eq
    have yh : z (readPin g q)=false := by
      rw [eq,eval _ small]
      obtain ⟨op,ne⟩ := h
      cases a : z (g p.1).left <;> cases b : z (g p.1).right <;>
        simp_all [IncidenceOperandLedger.zeroAt]
    obtain ⟨t,rt,bound,bit,last⟩ := live_route n s out g z live eval q b yh
    exact ⟨t,append (.next .here next) rt,bound,bit,last⟩
  · exact ⟨p,.here,small,high,Or.inl h⟩
termination_by s-p.1
decreasing_by omega

/-- A forwarding chain denotes its starting signal on the entire restricted
    domain if every dense-zero wire is empty there. -/
theorem pred_semantics {Z : Type*} (n : ℕ) (g : ℕ → Gate) (z : ℕ → Bool)
    (v : ℕ → Set Z) (dark : ∀w,z w=true → v w=∅)
    (join : ∀j,bypass g z j → v (n+j)=v (g j).left ∪ v (g j).right)
    {p t : Pin} (step : predPin n g z t=some p) :
    v (readPin g t) = v (readPin g p) := by
  unfold predPin at step
  dsimp only at step
  split at step
  · contradiction
  rename_i high
  split at step
  · rename_i mode
    obtain ⟨op,diff⟩ := mode
    let j := readPin g t-n
    have eq : readPin g t=n+j := by dsimp [j]; omega
    have pp : (j,z (g j).left) = p := Option.some.inj step
    subst p
    rw [eq,join j ⟨op,diff⟩]
    cases a : z (g j).left <;> cases b : z (g j).right <;>
      simp_all [readPin]
  · contradiction

theorem route_semantics {Z : Type*} (n : ℕ) (g : ℕ → Gate) (z : ℕ → Bool)
    (v : ℕ → Set Z) (dark : ∀w,z w=true → v w=∅)
    (join : ∀j,bypass g z j → v (n+j)=v (g j).left ∪ v (g j).right)
    {p t : Pin} (r : Route (predPin n g z) p t) :
    v (readPin g t)=v (readPin g p) := by
  induction r with
  | here => rfl
  | next _ e ih => exact (pred_semantics n g z v dark join e).trans ih
/-- Positive losses are summed per raw label; gains for a different raw cannot cancel losses.
    Each disappearing source pin must consume a different surplus gate. -/
theorem sum_positive_losses {W : Type*} [DecidableEq W] (labels : Finset W)
    (start keep : Finset Pin) (label : Pin → W) (allowed : Finset ℕ)
    (survives : Pin → Bool) (finish : Pin → Pin) (bill : Pin → ℕ)
    (toKeep : ∀p∈start,survives p=true → finish p∈keep ∧ label (finish p)=label p)
    (injKeep : Set.InjOn finish (↑(start.filter (fun p=>survives p=true)) : Set Pin))
    (toBill : ∀p∈start,survives p=false → bill p∈allowed)
    (injBill : Set.InjOn bill (↑(start.filter (fun p=>survives p=false)) : Set Pin))
    (inLabels : ∀p∈start,label p∈labels) :
    (∑ w∈labels, ((start.filter (fun p=>label p=w)).card -
        (keep.filter (fun p=>label p=w)).card)) ≤ allowed.card := by
  classical
  let lost := start.filter (fun p=>survives p=false)
  have step (w : W) :
      (start.filter (fun p=>label p=w)).card - (keep.filter (fun p=>label p=w)).card
        ≤ (lost.filter (fun p=>label p=w)).card := by
    let A := start.filter (fun p=>label p=w)
    have bound : (A.filter (fun p=>survives p=true)).card ≤
        (keep.filter (fun p=>label p=w)).card := by
      apply Finset.card_le_card_of_injOn finish
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨ha,yes⟩
        rcases Finset.mem_filter.mp ha with ⟨hs,lw⟩
        obtain ⟨kin,keq⟩ := toKeep p hs yes
        exact Finset.mem_filter.mpr ⟨kin,keq.trans lw⟩
      · apply injKeep.mono
        intro p hp
        obtain ⟨ha,y⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,y⟩
    have pos := Finset.card_filter_add_card_filter_not (s:=A) (fun p=>survives p=true)
    have lf : A.filter (fun p=>¬survives p=true) = lost.filter (fun p=>label p=w) := by
      ext p
      cases h : survives p <;> simp [A,lost,h,and_comm,and_left_comm]
    rw [lf] at pos
    change A.card - _ ≤ _
    omega
  calc
    _ ≤ ∑ w∈labels, (lost.filter (fun p=>label p=w)).card := Finset.sum_le_sum (fun w _=>step w)
    _ = lost.card := by
      have ht : ∀p∈lost,label p∈labels := fun p hp=>inLabels p (Finset.mem_filter.mp hp).1
      simpa using (Finset.sum_fiberwise_of_maps_to ht (fun _ : Pin=> (1 : ℕ)))
    _ ≤ _ := Finset.card_le_card_of_injOn bill
      (fun p hp=>toBill p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2) injBill

/-- A compensated gate has exactly one dead physical input. Two distinct
    deleted raws cannot both bill it, even if they were allowed to choose pins. -/
theorem compensation_injective (g : ℕ→Gate) (z : ℕ→Bool) (D : Finset ℕ)
    (reader : ℕ→Pin) (actual : ∀x∈D,readPin g (reader x)=x)
    (dead : ∀x∈D,z x=true)
    (uniqueDead : ∀x∈D,z (g (reader x).1).left ≠ z (g (reader x).1).right) :
    Set.InjOn (fun x=>(reader x).1) (D : Set ℕ) := by
  intro x hx y hy h
  have ex := actual x hx
  have ey := actual y hy
  have dx := dead x hx
  have dy := dead y hy
  have ne := uniqueDead x hx
  rcases px : reader x with ⟨j,u⟩
  rcases py : reader y with ⟨j',v⟩
  simp only [px,py] at h ex ey ne
  change j=j' at h
  subst j'
  cases u <;> cases v <;> simp [readPin] at ex ey <;> grind
/-- Two distinct surviving singleton tests at the compensating gate's wide operand
    suffice to exclude it from all forwarding routes of singleton raw signals. -/
theorem cannot_end_at_wide_operand {Z : Type*} (n : ℕ) (g : ℕ→Gate) (z : ℕ→Bool)
    (v : ℕ→Set Z) (dark : ∀w,z w=true → v w=∅)
    (join : ∀j,bypass g z j → v (n+j)=v (g j).left ∪ v (g j).right)
    (p t : Pin) (a b : Z) (ab : a≠b)
    (raw : ∀ x∈v (readPin g p),∀y∈v (readPin g p), x=y)
    (ha : a∈v (readPin g t)) (hb : b∈v (readPin g t)) :
    ¬Route (predPin n g z) p t := by
  intro r
  have eq := route_semantics n g z v dark join r
  rw [eq] at ha hb
  exact ab (raw a ha b hb)
#print axioms compensation_injective
#print axioms terminal_injective
#print axioms live_route
#print axioms route_semantics
end IncidenceForwardPins
