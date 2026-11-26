import Research.IncidenceAdditive
import Research.IncidenceAdaptive
import Research.AdaptiveGeometry

namespace AdaptiveIncidence

theorem arithmetic {q N s : ℕ} (hq : 100 < q) (order : N = q^2+q+1)
    (upper : q ≤ 249) (cost : 2*N+(N-3)/2 ≤ s+q) : N*q ≤ 100*s := by
  have product := Nat.mul_le_mul_right q (show 101 ≤ q by omega)
  have bound := Nat.mul_le_mul_left N upper
  rw [pow_two] at order
  omega

theorem moment_cap_general {k : ℕ} {q d b : ℕ} (hq : 0 < q) (hd : (k+1)*d ≤ k*q^2)
    (mom : q^2*b^2 ≤ d*b*(q+b)) : b ≤ k*q := by
  by_cases zero : b=0
  · simp [zero]
  have cc : q^2*b*((k+1)*b) ≤ q^2*b*(k*(q+b)) := calc
    _ = (k+1)*(q^2*b^2) := by ring
    _ ≤ (k+1)*(d*b*(q+b)) := Nat.mul_le_mul_left _ mom
    _ = ((k+1)*d)*b*(q+b) := by ring
    _ ≤ (k*q^2)*b*(q+b) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd)
    _ = _ := by ring
  have h := le_of_mul_le_mul_left cc (Nat.mul_pos (Nat.pow_pos hq) (by omega : 0 < b))
  simp only [Nat.add_mul,Nat.mul_add,one_mul] at h
  omega

theorem arithmetic_moment {q N s : ℕ} (hq : 100 < q) (order : N = q^2+q+1)
    (upper : q ≤ 288) (cost : 2*N+(16*q^2)/17 ≤ s+1+16*q) : N*q ≤ 100*s := by
  by_cases low : q < 140
  · have product := Nat.mul_le_mul_right q (show 101 ≤ q by omega)
    have bound := Nat.mul_le_mul_left N (show q ≤ 139 by omega)
    rw [← Nat.pow_two] at product
    omega
  by_cases mid : q < 279
  · have product := Nat.mul_le_mul_right q (show 140 ≤ q by omega)
    have bound := Nat.mul_le_mul_left N (show q ≤ 278 by omega)
    rw [← Nat.pow_two] at product
    omega
  · have product := Nat.mul_le_mul_right q (show 279 ≤ q by omega)
    have bound := Nat.mul_le_mul_left N upper
    rw [← Nat.pow_two] at product
    omega

theorem fraction {k q d : ℕ} (h : d ≤ k*q^2/(k+1)) : (k+1)*d ≤ k*q^2 := by
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mp h |> fun h => by simpa [Nat.mul_comm] using h

theorem fraction_small (k q : ℕ) : k*q^2/(k+1) ≤ q^2 := by
  have h := fraction (le_rfl : k*q^2/(k+1) ≤ _)
  apply Nat.le_of_mul_le_mul_left (le_trans h (Nat.mul_le_mul_right _ (Nat.le_succ k))) (Nat.succ_pos k)

theorem geometry {n d : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (room : ∀ D : Finset ℕ, D.card ≤ d → D.card+(AdaptiveGeometry.bad I D).card+2 ≤ n+n) :
    IncidenceAdaptive.Geometry (n+n) d (NatIncidenceRows.Edge I) (AdaptiveGeometry.bad I) := {
  enough := fun D _ h => room D h
  irrefl := fun a _ => NatIncidenceRows.edge_self I a
  grows := fun _ _ => AdaptiveGeometry.bad_mono I
  neighbor := fun _ _ _ _ ha _ ok => AdaptiveGeometry.has_neighbor I ha ok
  transpose := fun _ _ _ _ ha _ _ hb _ ne ok =>
    AdaptiveGeometry.distinguish I unique ha hb ne (fun h => ok.elim (fun a => a h.1) (fun b => b h.2))
}

theorem lower : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → (2*x2+(x2-3)/2 ≤ x9+x1) ∧ (∀ k ≤ x1, 2*x2+k*x1^2/(k+1) ≤ x9+1+k*x1) ∧ (x1 ≤ 288 → x2*x1 ≤ 100*x9)) := by
  intro q n I _ hq hn degree unique s o _ X ho inputs tagged pos neg _
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
  have half (D : Finset ℕ) (sm : D.card ≤ (n-3)/2) : (AdaptiveGeometry.bad I D).card < q :=
    AdaptiveGeometry.card_bad I degree unique (by omega) hn D (by omega)
  have halfGeom := geometry (d := (n-3)/2) I unique (by
    intro D sm
    have := half D sm
    omega)
  obtain ⟨D,_,card,cost⟩ := IncidenceAdaptive.lower halfGeom start
  have bad := half D (le_of_eq card)
  have halfCost : 2*n+(n-3)/2 ≤ s+q := by omega
  have par (k : ℕ) (hk : k ≤ q) : 2*n+k*q^2/(k+1) ≤ s+1+k*q := by
    let d := k*q^2/(k+1)
    have bound (U : Finset ℕ) (small : U.card ≤ d) : (AdaptiveGeometry.bad I U).card ≤ k*q :=
      moment_cap_general (by omega) (fraction small)
        (AdaptiveGeometry.moment_bad I degree unique (by omega) hn U)
    have kk : k*q ≤ q^2 := by simpa [pow_two] using Nat.mul_le_mul_right q hk
    have size : d ≤ q^2 := fraction_small k q
    have G := geometry (d:=d) I unique (by intro U small; have := bound U small; omega)
    obtain ⟨U,_,order,c⟩ := IncidenceAdaptive.lower G start
    have := bound U (le_of_eq order)
    change 2*n+d ≤ s+1+k*q
    omega
  refine ⟨halfCost,par,?_⟩
  intro upper
  exact arithmetic_moment hq hn upper (par 16 (by omega))

end AdaptiveIncidence
