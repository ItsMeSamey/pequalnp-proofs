import SignedTrace

namespace SignedTrace.Physical
open SignedTrace.Expression SignedTrace.Gates PEqualNP.CircuitLowerBounds

/-- The first component is the producing gate's output wire; the second is
its zero-based operand position. Hops run from output toward input. -/
abbrev Hops := List (Nat × Nat)
abbrev Reader := Nat → Bool → Hops → Prop

def rawReader (n d : Nat) : Reader :=
  fun i s hops => i < n ∧ i = d ∧ s = false ∧ hops = []

/-- The pin is bounded by this gate's actual arity. NOT uses only pin zero. -/
def gateReader (g : Gate) (w : Nat) (r : Reader) (s : Bool) (hops : Hops) : Prop :=
  ∃ p : Fin g.inputs.length, ∃ tail : Hops,
    hops = (w, p.val) :: tail ∧
      (((g.op = .and ∨ g.op = .or) ∧ r (g.inputs.get p) s tail) ∨
       (g.op = .not ∧ p.val = 0 ∧ r (g.inputs.get p) (!s) tail))

def finishReader : List Gate → Nat → Reader → Reader
  | [], _, r => r
  | g :: gs, w, r => finishReader gs (w+1)
      (fun i => if i=w then gateReader g w r else r i)

def certificate (C : Circuit) (n d : Nat) (s : Bool) (hops : Hops) : Prop :=
  finishReader C.gates n (rawReader n d) C.output s hops

private theorem gate_equiv (g : Gate) (w d : Nat) (s : Bool)
    (r : Reader) (read : Nat → Expr Nat) (hg : Good g)
    (hr : ∀ i b, path d b (read i) ↔ ∃ hops, r i b hops) :
    path d s (expand g read) ↔ ∃ hops, gateReader g w r s hops := by
  by_cases hb : g.op = .and ∨ g.op = .or
  · rw [binary_pin_path g read d s hb]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨t, ht⟩ := (hr _ _).mp hp
      exact ⟨_, p, t, rfl, Or.inl ⟨hb, ht⟩⟩
    · rintro ⟨_, p, t, _, h | h⟩
      · exact ⟨p, (hr _ _).mpr ⟨t, h.2⟩⟩
      · have hn := h.1
        rcases hb with ha | ho <;> simp_all
  have hn : g.op = .not := by
    rcases hg with ha | ho | hn
    · exact (hb (Or.inl ha)).elim
    · exact (hb (Or.inr ho)).elim
    · exact hn
  rw [neg_pin_path g read d s hn]
  cases he : g.inputs with
  | nil =>
    constructor
    · intro h; exact h.elim
    · rintro ⟨_, p, _⟩
      have := p.isLt
      simp [he] at this
  | cons a as =>
    constructor
    · intro hp
      obtain ⟨t, ht⟩ := (hr _ _).mp hp
      let p : Fin g.inputs.length := ⟨0, by simp [he]⟩
      have hp0 : g.inputs.get p = a := by simp [p, he]
      exact ⟨_, p, t, rfl, Or.inr ⟨hn, rfl, by simpa only [hp0] using ht⟩⟩
    · rintro ⟨_, p, t, _, h | h⟩
      · exact (hb h.1).elim
      · have hz := h.2.1
        have hp0 : g.inputs.get p = a := by
          obtain ⟨i, hi⟩ := p
          simp only at hz
          subst i
          simp [he]
        exact (hr _ _).mpr ⟨t, by simpa only [hp0] using h.2.2⟩

private theorem finish_equiv (gs : List Gate) (d : Nat) :
    ∀ w (r : Reader) (read : Nat → Expr Nat),
    (∀ g ∈ gs, Good g) →
    (∀ i b, path d b (read i) ↔ ∃ hops, r i b hops) →
    ∀ i b, path d b (finish gs w read i) ↔ ∃ hops, finishReader gs w r i b hops := by
  induction gs with
  | nil => intro w r read hg hr; exact hr
  | cons g gs ih =>
    intro w r read hg hr
    apply ih
    · intro a ha; exact hg a (by simp [ha])
    · intro i b
      by_cases he : i=w
      · subst i
        simpa using gate_equiv g w d b r read (hg g (by simp)) hr
      · simpa [he] using hr i b

theorem path_iff_certificate (C : Circuit) (n d : Nat) (s : Bool)
    (hg : ∀ g ∈ C.gates, Good g) :
    path d s (unfoldOutput C n) ↔ ∃ hops, certificate C n d s hops := by
  apply finish_equiv C.gates d n (rawReader n d) _ hg
  intro i b
  by_cases hi : i < n <;> simp [hi, path, rawReader]

/-- The signed paths in the discrepancy theorem can be reported as lists
of actual operand positions, in order from the output back to the donor. -/
theorem trace_with_pins (C : Circuit) (x y : List Bool)
    (hlen : y.length = x.length) (hg : ∀ g ∈ C.gates, Good g)
    (hx : C.eval x = true) (hy : C.eval y = false) :
    ∃ i hops, (certificate C x.length i false hops ∧
      x.getD i false = true ∧ y.getD i false = false) ∨
      (certificate C x.length i true hops ∧
      x.getD i false = false ∧ y.getD i false = true) := by
  obtain ⟨i, hi⟩ := circuit_trace C x y hlen hg hx hy
  rcases hi with ⟨p, xi, yi⟩ | ⟨p, xi, yi⟩
  · obtain ⟨hops, hh⟩ := (path_iff_certificate C x.length i false hg).mp p
    exact ⟨i, hops, Or.inl ⟨hh, xi, yi⟩⟩
  · obtain ⟨hops, hh⟩ := (path_iff_certificate C x.length i true hg).mp p
    exact ⟨i, hops, Or.inr ⟨hh, xi, yi⟩⟩

end SignedTrace.Physical
