import IncidenceHoistSparse
namespace IncidenceHoistShield
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistSparse

private theorem gate_agree {Z : Type} (g : Gate) (X : ℕ → Set Z) (u v : Z)
    (l : u ∈ X g.left ↔ v ∈ X g.left) (r : u ∈ X g.right ↔ v ∈ X g.right) :
    u ∈ g.eval X ↔ v ∈ g.eval X := by
  cases g with
  | mk op a b =>
    cases op <;> simp [Gate.eval,Op.eval] at * <;> tauto

def owner {n} (line : Bool) (x : Fin n) : ℕ := if line then n+x.val else x.val

private theorem raw_agree {n} (C : Circuit n) (line : Bool) (x : Fin n)
    (u v : Input n) (agr : AgreeOff line x u v) {i : ℕ} (hi : i<n+n)
    (hne : i ≠ owner line x) : u∈C.wire i ↔ v∈C.wire i := by
  by_cases left : i<n
  · let j : Fin n := ⟨i,left⟩
    rw [(C.inputs j).1]
    cases line <;> simp only [AgreeOff,owner,Bool.false_eq_true,if_false,if_true] at agr hne
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.2 j (by intro eq; exact hne (congrArg Fin.val eq))]
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.1]
  · let j : Fin n := ⟨i-n,by omega⟩
    have form : n+j.val=i := by dsimp [j]; omega
    rw [← form,(C.inputs j).2]
    cases line <;> simp only [AgreeOff,owner,Bool.false_eq_true,if_false,if_true] at agr hne
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.1]
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.2 j (by intro eq; have hv := congrArg Fin.val eq; omega)]

/-- Only the designated exit can import a private wire into an outside gate.
The cutoff allows pre-exit sibling independence and post-exit equality to
use the same physical topological induction. -/
private theorem agreeOutside {n} (C : Circuit n) (H : Finset ℕ) (cut lim : ℕ)
    (u v : Input n)
    (raw : ∀ i<n+n, i∉H → (u∈C.wire i ↔ v∈C.wire i))
    (boundary : ∀ j<C.size, j≠cut → n+n+j∉H →
      (C.code j).left∉H ∧ (C.code j).right∉H)
    (exit : n+n+cut<lim → (u∈C.wire (n+n+cut) ↔ v∈C.wire (n+n+cut))) :
    ∀ i<n+n+C.size, i<lim → i∉H → (u∈C.wire i ↔ v∈C.wire i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro live bounded outside
    by_cases input : i<n+n
    · exact raw i input outside
    · let j := i-(n+n)
      have atGate : i=n+n+j := by dsimp [j]; omega
      have js : j<C.size := by omega
      by_cases isCut : j=cut
      · rw [atGate,isCut]
        exact exit (by omega)
      · have ⟨left,right⟩ := boundary j js isCut (atGate ▸ outside)
        have ⟨hl,hr⟩ := C.earlier j js
        rw [atGate,C.law j js]
        exact gate_agree _ _ _ _ (ih _ (by omega) (by omega) (by omega) left)
          (ih _ (by omega) (by omega) (by omega) right)

/-- Each OR on a private path is an exit for the prefix ending just before
that OR. The protected sibling need not have a single reader. -/
theorem shield {n} (C : Circuit n) (line : Bool) (x : Fin n)
    (H : Finset ℕ) (cut sib : ℕ) (hcut : cut<C.size)
    (rawInside : owner line x∈H) (out : C.output∉H) (off : sib∉H)
    (boundary : ∀ j<C.size, j≠cut → n+n+j∉H →
      (C.code j).left∉H ∧ (C.code j).right∉H)
    (joined : (C.code cut).op=.join)
    (port : (C.code cut).left=sib ∨ (C.code cut).right=sib) :
    Shield C line x sib := by
  intro u v agr
  have raw (i : ℕ) (hi : i<n+n) (outside : i∉H) :
      u∈C.wire i ↔ v∈C.wire i :=
    raw_agree C line x u v agr hi (fun eq => outside (eq ▸ rawInside))
  have sb : sib<n+n+cut := by
    obtain ⟨hl,hr⟩ := C.earlier cut hcut
    rcases port with eq|eq <;> omega
  have sEq := agreeOutside C H cut (n+n+cut) u v raw boundary
    (fun h => (Nat.lt_irrefl _ h).elim) sib (by omega) sb off
  refine ⟨sEq,?_⟩
  intro hu
  have hv := sEq.mp hu
  have exit : u∈C.wire (n+n+cut) ↔ v∈C.wire (n+n+cut) := by
    rw [C.law cut hcut]
    simp only [Gate.eval,joined,Op.eval,Set.mem_union]
    rcases port with eq|eq <;> rw [eq] <;> tauto
  exact agreeOutside C H cut (n+n+C.size) u v raw boundary (fun _ => exit)
    C.output C.output_lt C.output_lt out

#print axioms shield
end IncidenceHoistShield
