import SignedPhysicalPath

namespace SignedTrace.FirstDivergence
open PEqualNP.CircuitLowerBounds SignedTrace.Physical

abbrev Hop := Nat × Nat

/-- Operand occurrence on a real, earlier wire. Repeated operands have distinct pins. -/
def Live (C : Circuit) (n v : Nat) (h : Hop) : Prop :=
  n ≤ h.1 ∧ v < h.1 ∧ ∃ g : Gate, C.gates[h.1 - n]? = some g ∧
    g.inputs[h.2]? = some v ∧
    (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ h.2 = 0))

def pinSource (C : Circuit) (n : Nat) (h : Hop) : Option Nat := do
  let g ← C.gates[h.1 - n]?
  g.inputs[h.2]?

theorem Live.pinSource_eq {C : Circuit} {n v : Nat} {h : Hop}
    (hp : Live C n v h) : pinSource C n h = some v := by
  obtain ⟨_, _, g, hg, hi, _⟩ := hp
  simp [pinSource, hg, hi]

def nextSign (C : Circuit) (n : Nat) (h : Hop) (s : Bool) : Bool :=
  match (C.gates[h.1 - n]?).map Gate.op with
  | some .not => !s
  | _ => s

/-- Read a forward path starting at a wire with a specified accumulated sign. -/
def Run (C : Circuit) (n : Nat) (v : Nat) (s : Bool)
    (z : Nat) (t : Bool) : List Hop → Prop
  | [] => v = z ∧ s = t
  | h :: hs => Live C n v h ∧ Run C n h.1 (nextSign C n h s) z t hs

abbrev Walk (C : Circuit) (n v z : Nat) (t : Bool) (hs : List Hop) :=
  Run C n v false z t hs

private theorem appendRun {C : Circuit} {n v u z : Nat} {s b t : Bool}
    {xs ys : List Hop} (hx : Run C n v s u b xs) (hy : Run C n u b z t ys) :
    Run C n v s z t (xs ++ ys) := by
  induction xs generalizing v s with
  | nil =>
    obtain ⟨rfl,rfl⟩ := hx
    exact hy
  | cons a as ih => exact ⟨hx.1, ih hx.2⟩

private theorem run_le {C : Circuit} {n v z : Nat} {s t : Bool}
    {xs : List Hop} (h : Run C n v s z t xs) : v ≤ z := by
  induction xs generalizing v s with
  | nil => exact le_of_eq h.1
  | cons a as ih => exact Nat.le_trans (Nat.le_of_lt h.1.2.1) (ih h.2)

private theorem lift_finish (C : Circuit) (n d : Nat) (gs : List Gate) :
    ∀ w (r : Reader), n ≤ w →
    (∀ j g, gs[j]? = some g → C.gates[(w+j)-n]? = some g) →
    (∀ v s hs, r v s hs → v < w ∧ Walk C n d v s hs.reverse) →
    ∀ v s hs, finishReader gs w r v s hs → Walk C n d v s hs.reverse := by
  induction gs with
  | nil => intro w r _ _ hr v s hs h; exact (hr v s hs h).2
  | cons g gs ih =>
    intro w r hn hlookup hr
    refine ih (w+1) (fun i => if i = w then gateReader g w r else r i) ?_ ?_ ?_
    · omega
    · intro j g' hj
      have he := hlookup (j+1) g' (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    · intro v s hs h
      by_cases hv : v = w
      · subst v
        simp only [if_pos rfl] at h
        obtain ⟨p, tail, rfl, hpin⟩ := h
        have hg : C.gates[w-n]? = some g := by
          simpa using hlookup 0 g (by simp)
        have hget : g.inputs[p.val]? = some (g.inputs.get p) := by simp [p.isLt]
        refine ⟨by omega, ?_⟩
        rw [List.reverse_cons]
        rcases hpin with ⟨hop,ht⟩ | ⟨hop,hzero,ht⟩
        · obtain ⟨hv,hw⟩ := hr _ _ _ ht
          apply appendRun hw
          refine ⟨⟨hn,hv,g,hg,hget,?_⟩,rfl,?_⟩
          · rcases hop with ha | ho
            · exact Or.inl ha
            · exact Or.inr (Or.inl ho)
          · rcases hop with hop | hop <;> simp [nextSign, hg, hop]
        · obtain ⟨hv,hw⟩ := hr _ _ _ ht
          apply appendRun hw
          exact ⟨⟨hn,hv,g,hg,hget,Or.inr (Or.inr ⟨hop,hzero⟩)⟩,rfl,
            by simp [nextSign,hg,hop]⟩
      · simp only [if_neg hv] at h
        obtain ⟨hlt,hw⟩ := hr _ _ _ h
        exact ⟨by omega,hw⟩

theorem certificate_walk {C : Circuit} {n d : Nat} {s : Bool} {hs : Hops}
    (h : certificate C n d s hs) : Walk C n d C.output s hs.reverse := by
  refine lift_finish C n d C.gates n (rawReader n d) (by omega) ?_ ?_ C.output s hs h
  · intro j g hj
    simpa using hj
  · intro v t xs hv
    obtain ⟨hlt,rfl,rfl,rfl⟩ := hv
    exact ⟨hlt,rfl,rfl⟩

private theorem fork_run {C : Circuit} {n v z : Nat} {s t u : Bool}
    {xs ys : List Hop} (hx : Run C n v s z t xs) (hy : Run C n v s z u ys)
    (hne : t ≠ u) :
    ∃ pre a b qa qb w q,
      xs = pre ++ a :: qa ∧ ys = pre ++ b :: qb ∧
      Run C n v s w q pre ∧ a ≠ b ∧ Live C n w a ∧ Live C n w b ∧
      Run C n a.1 (nextSign C n a q) z t qa ∧
      Run C n b.1 (nextSign C n b q) z u qb := by
  induction xs generalizing v s ys with
  | nil =>
    obtain ⟨rfl,rfl⟩ := hx
    cases ys with
    | nil => exact (hne hy.2).elim
    | cons b bs =>
      have hlt := hy.1.2.1
      have hle := run_le hy.2
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have he := hy.1
      have hlt := hx.1.2.1
      have hle := run_le hx.2
      omega
    | cons b bs =>
      by_cases hab : a = b
      · subst b
        obtain ⟨pre,c,e,qa,qb,w,q,hx',hy',hp,hd,hc,he,hqa,hqb⟩ :=
          ih hx.2 hy.2
        exact ⟨a::pre,c,e,qa,qb,w,q,congrArg (a :: ·) hx',
          congrArg (a :: ·) hy',⟨hx.1,hp⟩,hd,hc,he,hqa,hqb⟩
      · exact ⟨[],a,b,as,bs,v,s,rfl,rfl,⟨rfl,rfl⟩,hab,hx.1,hy.1,hx.2,hy.2⟩

/-- Opposite traces from one physical donor share their prefix up to
two distinct live operand occurrences. Both suffixes reach the same output. -/
theorem opposite_fork {C : Circuit} {n d : Nat} {xs ys : Hops}
    (hx : certificate C n d false xs) (hy : certificate C n d true ys) :
    ∃ pre a b qa qb w q,
      xs.reverse = pre ++ a :: qa ∧ ys.reverse = pre ++ b :: qb ∧
      Walk C n d w q pre ∧ a ≠ b ∧ Live C n w a ∧ Live C n w b ∧
      Run C n a.1 (nextSign C n a q) C.output false qa ∧
      Run C n b.1 (nextSign C n b q) C.output true qb :=
  fork_run (certificate_walk hx) (certificate_walk hy) (by decide)

end SignedTrace.FirstDivergence
