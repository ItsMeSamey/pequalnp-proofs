import IncidenceStartNormalization
namespace IncidenceHoistPorts
open CircuitRewire IncidenceStartNormalization

/-- Each erased gate is a join. flip records its actual ordered operands;
acc is the wire feeding its new output-aggregation join. -/
inductive Entry
  | keep (g : Gate)
  | spine (flip : Bool) (main sibling acc : Nat)

def old : Entry → Gate
  | .keep g => g
  | .spine false m s _ => ⟨.join,m,s⟩
  | .spine true m s _ => ⟨.join,s,m⟩

def kept (f : Nat → Nat) : Entry → List Gate
  | .keep g => [⟨g.op,f g.left,f g.right⟩]
  | .spine .. => []

def extra (f : Nat → Nat) : Entry → List Gate
  | .keep _ => []
  | .spine _ _ s acc => [⟨.join,acc,f s⟩]

def emit (f : Nat → Nat) (es : List Entry) :=
  es.flatMap (kept f) ++ es.flatMap (extra f)

def hit (wire queried : Nat) : Nat := if wire = queried then 1 else 0

def count (w : Op → Nat) (i : Nat) (gs : List Gate) :=
  (gs.map (fun g => w g.op * (hit g.left i + hit g.right i))).sum

theorem emit_length (f : Nat → Nat) (es : List Entry) : (emit f es).length = es.length := by
  unfold emit
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp [kept,extra,List.length_append] at ih ⊢ <;> omega

/-- Per-occurrence conditions on the surviving operands. A shared exit
used as another spine's sibling moves to a new aggregate join. -/
def Tracks (f : Nat → Nat) (source dest : Nat) : Entry → Prop
  | .keep g => (f g.left = dest ↔ g.left = source) ∧ (f g.right = dest ↔ g.right = source)
  | .spine _ m s acc => m ≠ source ∧ acc ≠ dest ∧ (f s = dest ↔ s = source)

private theorem hit_eq {a b x y} (h : a = x ↔ b = y) : hit a x = hit b y := by
  simp only [hit, h]

private theorem local_count (f : Nat → Nat) (i j : Nat) (w : Op → Nat) (e : Entry)
    (h : Tracks f i j e) :
    count w j (kept f e) + count w j (extra f e) = count w i [old e] := by
  cases e with
  | keep g =>
    obtain ⟨hl,hr⟩ := h
    simp [kept,extra,old,count,hit_eq hl,hit_eq hr]
  | spine flip m s acc =>
    obtain ⟨hm,ha,hs⟩ := h
    have em : hit m i = 0 := by simp [hit,hm]
    have ea : hit acc j = 0 := by simp [hit,ha]
    cases flip <;> simp [kept,extra,old,count,em,ea,hit_eq hs]

private theorem count_append (w : Op → Nat) (i : Nat) (a b : List Gate) :
    count w i (a++b) = count w i a + count w i b := by simp [count]

theorem port_transfer (f : Nat → Nat) (i j : Nat) (es : List Entry)
    (w : Op → Nat) (tr : ∀ e ∈ es, Tracks f i j e) :
    count w j (emit f es) = count w i (es.map old) := by
  unfold emit
  induction es with
  | nil => rfl
  | cons e es ih =>
    have one := local_count f i j w e (tr e (by simp))
    have tail := ih (fun x hx => tr x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.map_cons, count_append] at tail ⊢
    rw [show count w i (old e :: es.map old) = count w i [old e] + count w i (es.map old)
      from count_append w i [old e] (es.map old)]
    omega

/-- Preserve each old exit occurrence even if additional operands alias its owner. -/
def Retains (f : Nat → Nat) (i j : Nat) : Entry → Prop
  | .keep g => (g.left = i → f g.left = j) ∧ (g.right = i → f g.right = j)
  | .spine _ m s _ => m ≠ i ∧ (s = i → f s = j)

private theorem hit_le {a b x y} (h : b = y → a = x) : hit b y ≤ hit a x := by
  by_cases e : b = y
  · simp [hit,e,h e]
  · simp [hit,e]

theorem exit_uses_le (f : Nat → Nat) (i j : Nat) (es : List Entry)
    (tr : ∀ e ∈ es, Retains f i j e) :
    count (fun _ => 1) i (es.map old) ≤ count (fun _ => 1) j (emit f es) := by
  unfold emit
  induction es with
  | nil => exact le_rfl
  | cons e es ih =>
    have tail := ih (fun x hx => tr x (List.mem_cons_of_mem _ hx))
    have h := tr e (by simp)
    have one : count (fun _ => 1) i [old e] ≤
        count (fun _ => 1) j (kept f e) + count (fun _ => 1) j (extra f e) := by
      cases e with
      | keep g =>
        obtain ⟨hl,hr⟩ := h
        simpa [old,kept,extra,count] using Nat.add_le_add (hit_le hl) (hit_le hr)
      | spine flip m s acc =>
        obtain ⟨hm,hs⟩ := h
        have le := hit_le hs
        have zm : hit m i = 0 := by simp [hit,hm]
        cases flip <;> simp [old,kept,extra,count,zm] <;> omega
    simp only [List.flatMap_cons,List.map_cons,count_append] at tail ⊢
    rw [show count (fun _ => 1) i (old e :: es.map old) =
      count (fun _ => 1) i [old e] + count (fun _ => 1) i (es.map old) from
      count_append _ i [old e] (es.map old)]
    omega

def circuitCode {n} (C : Circuit n) := (List.range C.size).map C.code

theorem actual_uses {n} (C : Circuit n) (i : Nat) :
    count (fun _ => 1) i (circuitCode C) = uses C i := by
  simp [count,circuitCode,IncidenceStartNormalization.uses,hit,Function.comp_def]

theorem circuit_transfer {n} (C D : Circuit n) (f : Nat → Nat) (i j : Nat)
    (es : List Entry) (src : circuitCode C = es.map old) (dst : circuitCode D = emit f es)
    (tr : ∀ e ∈ es, Tracks f i j e) : uses D j = uses C i := by
  rw [← actual_uses,← actual_uses,dst,src]
  exact port_transfer f i j es _ tr

def privateOnly (i : Nat) (gs : List Gate) :=
  ∀ g ∈ gs, g.left = i ∨ g.right = i → g.op = .meet

private def bad (op : Op) : Nat := if op = .meet then 0 else 1

private theorem bad_zero_iff (i : Nat) (gs : List Gate) :
    count bad i gs = 0 ↔ privateOnly i gs := by
  induction gs with
  | nil => simp [count,privateOnly]
  | cons g gs ih =>
    have step : count bad i (g::gs) = bad g.op * (hit g.left i + hit g.right i) + count bad i gs := rfl
    rw [step, Nat.add_eq_zero_iff, ih]
    by_cases h : g.op = .meet <;> by_cases l : g.left=i <;> by_cases r : g.right=i <;>
      simp [bad,hit,h,l,r,privateOnly]

theorem private_transfer (f : Nat → Nat) (i j : Nat) (es : List Entry)
    (tr : ∀ e ∈ es, Tracks f i j e) :
    privateOnly j (emit f es) ↔ privateOnly i (es.map old) := by
  rw [← bad_zero_iff, ← bad_zero_iff,port_transfer f i j es bad tr]

private theorem code_private {n} (C : Circuit n) (i : Nat) :
    privateOnly i (circuitCode C) ↔
    ∀ g < C.size, (C.code g).left = i ∨ (C.code g).right = i → (C.code g).op = .meet := by
  constructor
  · intro h g hg
    exact h _ (List.mem_map.mpr ⟨g,List.mem_range.mpr hg,rfl⟩)
  · intro h g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    exact h _ (List.mem_range.mp hj)

theorem opposite_soleAnd {n} (C D : Circuit n) (f : Nat → Nat) (off : Nat) (es : List Entry)
    (src : circuitCode C = es.map old) (dst : circuitCode D = emit f es)
    (tr : ∀ i < n, ∀ e ∈ es, Tracks f (off+i) (off+i) e)
    (ha : soleAnd C off) : soleAnd D off := by
  intro i hi hu
  have h := circuit_transfer C D f (off+i) (off+i) es src dst (tr i hi)
  have before := (code_private C (off+i)).mpr (ha i hi (h ▸ hu))
  rw [src] at before
  apply (code_private D (off+i)).mp
  rw [dst]
  exact (private_transfer f _ _ es (tr i hi)).mpr before

#print axioms opposite_soleAnd
#print axioms circuit_transfer
#print axioms private_transfer
end IncidenceHoistPorts
