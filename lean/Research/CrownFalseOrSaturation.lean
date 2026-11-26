import Research.TrueOrCount

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def falseOrAt (g : Gate) (w : List Bool) : Bool :=
  isOrGate g && !(g.op.eval (g.inputs.map fun j => w.getD j false))

/-- Every false OR participates in the selected proof of the false output and
both of its inputs are new at that gate's step of the backward traversal. -/
def fullFalseForks : List Gate → List Bool → ℕ → Prop
  | [], _, _ => True
  | g :: gs, w, o =>
    let t := falseLive gs (advance g w) o
    (falseOrAt g w = true → w.length ∈ t ∧ ((falseParents g w) \ t.erase w.length).card = 2) ∧
      fullFalseForks gs (advance g w) o

private theorem fork_step (g : Gate) (gs : List Gate) (w : List Bool) (o : ℕ)
    (fanin : g.inputs.length ≤ 2) :
    let t := falseLive gs (advance g w) o
    (falseLive (g::gs) w o).card ≤ t.card + (if falseOrAt g w then 1 else 0) ∧
    ((falseLive (g::gs) w o).card = t.card + 1 → w.length ∈ t ∧
      ((falseParents g w) \ t.erase w.length).card = 2) := by
  let t := falseLive gs (advance g w) o
  change (falseLive (g::gs) w o).card ≤ t.card + _ ∧ _
  by_cases hm : w.length ∈ t
  · have hf := falseLive_false gs (advance g w) o w.length hm
    rw [getD_advance_eq] at hf
    have pt := falseParents_card g w fanin
    have he := Finset.card_erase_add_one hm
    have hu := Finset.card_sdiff_add_card (falseParents g w) (t.erase w.length)
    rw [Finset.union_comm] at hu
    have ht : falseLive (g::gs) w o = (t.erase w.length) ∪ falseParents g w := ite_eq_left hm
    have hp := Finset.card_le_card (Finset.sdiff_subset : falseParents g w \ t.erase w.length ⊆ falseParents g w)
    change _ ∧ ((falseLive (g::gs) w o).card = t.card + 1 → w.length ∈ t ∧ _)
    rw [ht]
    constructor
    · simp only [falseOrAt,hf,Bool.not_false,Bool.and_true]
      cases hb : isOrGate g <;> simp only [hb,Bool.false_eq_true,↓reduceIte] at pt ⊢ <;> omega
    · intro eq
      refine ⟨hm,?_⟩
      change (falseParents g w \ t.erase w.length).card = 2
      omega
  · have ht : falseLive (g::gs) w o = t := ite_eq_right hm
    change _ ∧ ((falseLive (g::gs) w o).card = t.card + 1 → _)
    rw [ht]
    constructor <;> omega

theorem fullFalseForks_of_tight (gs : List Gate) (w : List Bool) (o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (tight : (falseLive gs w o).card = falseOrCount gs w + 1) : fullFalseForks gs w o := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    have ht := falseLive_falseOrCount gs (advance g w) o
      (fun a ha => h a (List.mem_cons_of_mem _ ha))
    obtain ⟨step,fork⟩ := fork_step g gs w o (h g (List.mem_cons_self ..))
    change (falseLive (g::gs) w o).card = (if falseOrAt g w then 1 else 0) +
      falseOrCount gs (advance g w) + 1 at tight
    constructor
    · intro hf
      simp only [hf,↓reduceIte] at tight step
      exact fork (by omega)
    · apply ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))
      omega

theorem crown_full_false_forks (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (total : (C.gates.filter isOrGate).length ≤ 23)
    (active : 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true) :
    fullFalseForks C.gates (oneEach i i) C.output := by
  have hbal := trueOrFlags_balance C.gates (oneEach i i)
  have hf := crown_twelve_falseOrCount i C hm rep
  have minc := zeroCell_degree_falseLive (fun u v : Fin 12 => decide (u ≠ v)) i i C hm rep (by simp)
  have hd : ∀ j : Fin 12, (Finset.univ.filter (fun u : Fin 12 => decide (u ≠ j))).card = 11 ∧
      (Finset.univ.filter (fun u : Fin 12 => decide (j ≠ u))).card = 11 := by decide
  rw [(hd i).1,(hd i).2] at minc
  have mx := falseLive_falseOrCount C.gates (oneEach i i) C.output (fun g hg => (hm g hg).2)
  exact fullFalseForks_of_tight _ _ _ (fun g hg => (hm g hg).2) (by omega)

end PEqualNP.Research.MissingCell
