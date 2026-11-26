import FoldedRemote
import Research.CrownSilentInduced
namespace CrownMixed.FoldedNine
open FreeAndNet FreeAndNet.CircuitCompiler PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents PEqualNP.Research.MissingCell

def row (i : Fin 4) : Fin 8 := ([0,1,2,6] : List (Fin 8)).getD i.val 0
def col (i : Fin 4) : Fin 8 := ([3,4,5,6] : List (Fin 8)).getD i.val 0
def names : Naming (Fin 4) (Fin 8) where
  row := row
  col := col
  row_inj := by decide
  col_inj := by decide
  same := by decide

def input (i j : Fin 4) := List.ofFn (names.val i j)
def flagged : Fin 8 → Bool := fun i => decide (i=6 ∨ i=7)
private theorem source (p q : Fin 4) (a : Nat) (h : (input p q).getD a false = true) :
    (input p p).getD a false = true ∨ (input q q).getD a false = true := by
  by_cases ha : a < 8
  · exact (by decide : ∀ p q : Fin 4, ∀ a : Fin 8, (input p q).getD a.val false = true →
      (input p p).getD a.val false = true ∨ (input q q).getD a.val false = true) p q ⟨a,ha⟩ h
  · have e : (input p q)[a]? = none := List.getElem?_eq_none (by simpa [input] using Nat.le_of_not_gt ha)
    simp [List.getD_eq_getElem?_getD,e] at h

theorem tail_size_ge_ten (C : Circuit) (hm : Monotone2 C)
    (rep : ∀ i j, C.eval (input i j) = decide (i≠j))
    (hot : C.eval (List.ofFn flagged) = true) : 10 ≤ C.size := by
  let t := compile 8 C
  have nr : names.Rep t := fun i j => (compile_eval 8 C hm (names.val i j)).trans (rep i j)
  have off : ∀ p q, names.val p q 7 = false := by decide
  have pos : ∃ v : Fin 8 → Bool, v 7 = false ∧ t.eval v = true :=
    ⟨names.val 0 1,off 0 1,(nr 0 1).trans (by decide)⟩
  have essential : ∃ v w : Fin 8 → Bool, (∀ i, i≠7 → v i=w i) ∧ t.eval v ≠ t.eval w := by
    refine ⟨names.val 3 3,flagged,by decide,?_⟩
    have zero : t.eval (names.val 3 3) = false := (nr 3 3).trans (by decide)
    have one : t.eval flagged = true := (compile_eval 8 C hm flagged).trans hot
    rw [zero,one]
    decide
  have orlow := folded_remote_or_lower names t 7 (by decide) nr off pos essential
  have pr : names.pairs = 1 := by decide
  have oc := compile_cost 8 C
  change t.cost ≤ _ at oc
  simp only [Fintype.card_fin,pr] at orlow
  have ac := induced_and_codes C hm (fun i : Fin 4 => input i i) input ∅ (by simp)
    (fun i => (rep i i).trans (by simp)) (fun i j ne => (rep i j).trans (decide_eq_true ne))
    (by simp [input]) (by simp [input]) source
  simp only [Fintype.card_fin] at ac
  have two : 2 ≤ (avoidingAnds C ∅).card := by
    by_contra! h
    have h' := Nat.pow_le_pow_right (by decide : 0<2) (show (avoidingAnds C ∅).card ≤ 1 by omega)
    omega
  have balance := all_and_count_balance C hm
  change (avoidingAnds C ∅).card + (C.gates.filter orFlag).length = C.size at balance
  omega
end CrownMixed.FoldedNine
