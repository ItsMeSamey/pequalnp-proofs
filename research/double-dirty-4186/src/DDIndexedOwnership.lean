import DDIndexedOrigin
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
attribute [local instance] gateOpDecEq
theorem physical_owner {n k u : ℕ} (C : Circuit) (p : Cuts) (hu : u < rank n C p k) :
    ∃ j < k, ∃ g, ins n C p j = some g ∧ rank n C p j = u := by
  induction k with
  | zero => simp [rank,build,initial] at hu
  | succ j ih =>
    by_cases earlier : u < rank n C p j
    · obtain ⟨i,hi,g,hg,eq⟩ := ih earlier
      exact ⟨i,by omega,g,hg,eq⟩
    · change u < (build n C p (j+1)).gates.length at hu
      rw [gates_step,List.length_append] at hu
      cases e : ins n C p j with
      | none => simp [e] at hu; exact (earlier hu).elim
      | some g =>
        simp [e] at hu
        change ¬u < (build n C p j).gates.length at earlier
        exact ⟨j,by omega,g,e,by change (build n C p j).gates.length = u; omega⟩
theorem owner_unique {n i j : ℕ} (C : Circuit) (p : Cuts) {a b : Gate}
    (hi : ins n C p i = some a) (hj : ins n C p j = some b)
    (eq : rank n C p i = rank n C p j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact ((Nat.ne_of_lt (paid_strict C p hi h)) eq).elim
  · exact h
  · exact ((Nat.ne_of_lt (paid_strict C p hj h)) eq.symm).elim
def SourceOK (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) : Origin → Prop
  | .input i => i<n
  | .gate j => j<k ∧ ∃ g, ins n C p j = some g
private def Tags (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) (r : Ref) :=
  ∀ z, r = some z → SourceOK n C p k z.1
private theorem tags_mono {n k : ℕ} {C : Circuit} {p : Cuts} {r : Ref}
    (h : Tags n C p k r) : Tags n C p (k+1) r := by
  rintro ⟨o,v⟩ hv
  have old := h _ hv
  cases o with
  | input i => exact old
  | gate i => exact ⟨Nat.lt_succ_of_lt old.1,old.2⟩
private theorem from_pin {n j : ℕ} {C : Circuit} {p : Cuts} (b : Fin 2)
    (h : ∀ r ∈ (build n C p j).refs, Tags n C p j r) :
    Tags n C p j (pin (build n C p j) n C p j b) := by
  simp only [pin]
  split
  · simp [Tags]
  · unfold ref
    by_cases hw : opnd C j b < (build n C p j).refs.length
    · rw [List.getD_eq_getElem _ _ hw]; exact h _ (List.getElem_mem hw)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [Tags]

private theorem all_tags (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    ∀ r ∈ (build n C p k).refs, Tags n C p k r := by
  induction k with
  | zero =>
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simpa [Tags,SourceOK] using List.mem_range.mp hi
  | succ j ih =>
    intro r hr
    change r ∈ _ ++ [_] at hr
    rcases List.mem_append.mp hr with hold | hnew
    · exact tags_mono (ih r hold)
    · obtain rfl := List.mem_singleton.mp hnew
      have l := tags_mono (from_pin 0 ih)
      have r := tags_mono (from_pin 1 ih)
      cases hl : pin (build n C p j) n C p j 0 <;> cases hr : pin (build n C p j) n C p j 1 <;>
        cases skip : p.omit j <;> by_cases op : (gateAt C j).op = .and <;>
        simp_all [Tags,dest,SourceOK,ins,instruction,Option.orElse]
theorem pin_origin {n j : ℕ} {C : Circuit} {p : Cuts} {b : Fin 2} {z : Origin × ℕ}
    (hz : pin (build n C p j) n C p j b = some z) :
    SourceOK n C p j z.1 := from_pin b (all_tags n C p j) z hz

theorem tag_of_address {n i j : ℕ} {C : Circuit} {p : Cuts} {b : Fin 2} {z : Origin × ℕ} {g : Gate}
    (valid : ins n C p i = some g) (hz : pin (build n C p j) n C p j b = some z)
    (addr : z.2 = n+rank n C p i) : z.1 = .gate i := by
  rcases z with ⟨o,v⟩
  have own := pin_origin hz
  have val := pin_address hz
  cases o with
  | input t =>
    change t<n at own
    change v=t at val
    change v=_ at addr
    omega
  | gate t =>
    obtain ⟨_,g',e⟩ := own
    change v=n+rank n C p t at val
    change v=_ at addr
    have eq := owner_unique C p e valid (by omega)
    simp [eq]
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
