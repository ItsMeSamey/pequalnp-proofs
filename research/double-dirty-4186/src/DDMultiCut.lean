import DDFactorCone

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98

def multiCuts (n : ℕ) (C : Circuit) (sources : Finset ℕ) : Cuts :=
  ⟨fun _ => false, fun j b => decide (n ≤ opnd C j b ∧ opnd C j b-n ∈ sources)⟩

/-- A source's projected value depends on strict ancestors, never its own cut. -/
def strictInfluence (n : ℕ) (C : Circuit) (s w : ℕ) : Prop :=
  ∃ j < C.size, w = n+j ∧ ∃ u ∈ (gateAt C j).inputs, Influence n C s u

theorem strict_to_influence {n : ℕ} {C : Circuit} {s w : ℕ} (h : strictInfluence n C s w) :
    Influence n C s w := by
  obtain ⟨j,hj,rfl,u,hu,h⟩ := h
  exact .step h hj hu

theorem multi_safe {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ) (x : Fin n → Bool) :
    Safe C (multiCuts n C sources) x
      (fun w => ∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) := by
  constructor
  · intro j _ _ h
    cases h
  · intro j hj needed _ b
    have mem := opnd_mem ao hj b
    split
    next cut =>
      have c : n ≤ opnd C j b ∧ opnd C j b - n ∈ sources := by simpa [multiCuts] using cut.2
      let s := opnd C j b - n
      have eq : opnd C j b = n+s := by dsimp [s]; omega
      have path : Influence n C s (opnd C j b) := by rw [eq]; exact .source
      rw [eq]
      exact needed s c.2 ⟨j,hj,rfl,opnd C j b,mem,path⟩
    next =>
      intro s hs reach
      exact needed s hs ⟨j,hj,rfl,opnd C j b,mem,strict_to_influence reach⟩

theorem multi_agree {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ)
    {w : ℕ} (hw : w<n+C.size) (x : Fin n → Bool)
    (enabled : ∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) :
    W n C x w = denotation (physicalSlot n C (multiCuts n C sources) C.size w) x :=
  agree C ao _ x _ (multi_safe C ao sources x) C.size le_rfl w hw enabled

theorem multi_restore {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ)
    {w : ℕ} (hw : w<n+C.size) (x : Fin n → Bool)
    (dom : W n C x w = true → ∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) :
    W n C x w = true ↔
      (∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) ∧
      denotation (physicalSlot n C (multiCuts n C sources) C.size w) x = true := by
  constructor
  · intro h
    exact ⟨dom h,(multi_agree C ao sources hw x (dom h)).symm.trans h⟩
  · rintro ⟨enabled,h⟩
    exact (multi_agree C ao sources hw x enabled).trans h

theorem influence_extend {n : ℕ} {C : Circuit} {a b w : ℕ}
    (h : Influence n C a (n+b)) (p : Influence n C b w) : Influence n C a w := by
  induction p with
  | source => exact h
  | step _ len pin ih => exact .step ih len pin

theorem strict_trans {n : ℕ} {C : Circuit} {a b w : ℕ}
    (h : strictInfluence n C a (n+b)) (p : strictInfluence n C b w) :
    strictInfluence n C a w := by
  obtain ⟨j,hj,eq,u,hu,pu⟩ := p
  exact ⟨j,hj,eq,u,hu,influence_extend (strict_to_influence h) pu⟩

theorem source_lt_of_strict {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {s w : ℕ}
    (path : strictInfluence n C s w) : n+s < w := by
  obtain ⟨j,hj,rfl,u,hu,p⟩ := path
  have lower : ∀ {v}, Influence n C s v → n+s ≤ v := by
    intro v walk
    induction walk with
    | source => exact le_rfl
    | step _ hmem pin ih =>
      exact le_of_lt (ih.trans_lt (ao.2.1 _ hmem _ pin))
  exact (lower p).trans_lt (ao.2.1 j hj u hu)

/-- Testing every strictly upstream source is equivalent before and after simultaneous
projection. The reverse implication restores source values in increasing gate order.
This also handles one distinguished source upstream of the other. -/
theorem projected_enabled {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ)
    (valid : ∀ s ∈ sources, s < C.size) (w : ℕ) (x : Fin n → Bool) :
    (∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) ↔
    (∀ s ∈ sources, strictInfluence n C s w →
      denotation (physicalSlot n C (multiCuts n C sources) C.size (n+s)) x = true) := by
  constructor
  · intro orig s hs ps
    have eq := multi_agree C ao sources (by have := valid s hs; omega : n+s < n+C.size) x
      (fun a ha p => orig a ha (strict_trans p ps))
    exact eq.symm.trans (orig s hs ps)
  · intro proj s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs ps
      have eq := multi_agree C ao sources (by have := valid s hs; omega : n+s < n+C.size) x
        (fun a ha p => ih a (by have := source_lt_of_strict ao p; omega) ha (strict_trans p ps))
      exact eq.trans (proj s hs ps)

theorem projected_restore {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ)
    (valid : ∀ s ∈ sources, s < C.size) {w : ℕ} (hw : w<n+C.size) (x : Fin n → Bool)
    (dom : W n C x w = true → ∀ s ∈ sources, strictInfluence n C s w → W n C x (n+s) = true) :
    W n C x w = true ↔
      (∀ s ∈ sources, strictInfluence n C s w →
        denotation (physicalSlot n C (multiCuts n C sources) C.size (n+s)) x = true) ∧
      denotation (physicalSlot n C (multiCuts n C sources) C.size w) x = true := by
  rw [← projected_enabled C ao sources valid w x]
  exact multi_restore C ao sources hw x dom

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
