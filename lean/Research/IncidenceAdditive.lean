import Research.IncidenceIterate

theorem IncidenceAdditive.lower : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → 2 * x2 + x1 ≤ x9) := by
  intro q n I _ hq hn degree unique s o _ X ho inputs tagged pos neg _
  have geometry : IncidenceIterate.Geometry (n+n) q (NatIncidenceRows.Edge I) := {
    enough := by omega
    irrefl := fun a _ => NatIncidenceRows.edge_self I a
    neighbor := fun D _ small a ha _ => NatIncidenceRows.has_neighbor I degree unique
      (by omega) hn D small a ha
    transpose := fun D _ small _ ha _ _ hb _ ne => NatIncidenceRows.distinguish I degree unique
      (by omega) hn D small ha hb ne
  }
  obtain ⟨t,out,code,Y,ht,hout,gates,roots,pairs⟩ :=
    IncidenceInitial.initial I (by omega) hn degree s o X ho inputs (by
      intro k hk
      obtain ⟨a,ha,b,hb,law⟩ := tagged k hk
      exact ⟨a,ha,b,hb,law.imp_right (Or.imp_right (Or.imp_right And.left))⟩) pos neg
  have start : IncidenceIterate.Realizes (n+n) (NatIncidenceRows.Edge I) ∅ t out code Y := {
    bounded := hout
    normal := fun k hk => (gates k hk).1
    gate := fun k hk => (gates k hk).2
    avoids := by simp
    inputs := by intro i hi T; rw [roots i hi]; simp
    pairs := fun a ha _ c hc _ => pairs a ha c hc
  }
  have := IncidenceIterate.lower geometry start
  omega
