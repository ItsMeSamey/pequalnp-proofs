import Research.CrownLabelCap
import Research.CrownSingletonQuarter
import Research.CrownEdgeCharge
import Research.CrownAggregateExcess

namespace PEqualNP.Research.MissingCell.CrownLabels
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators
abbrev L := Fin 12

def sig (C : Circuit) (t : Fin 24) := activeOrIds C.gates (singleInput t)
def A (C : Circuit) (i : L) := sig C (rowPort i)
def B (C : Circuit) (i : L) := sig C (colPort i)

def Early {n : ℕ} (U V : Finset (Fin n)) : Prop :=
  ∃ g h, g < h ∧ U = {g,h} ∧ V = {h}
def Common {n : ℕ} (U V : Finset (Fin n)) : Prop :=
  ∃ (u : U.Nonempty) (v : V.Nonempty), U.min' u = V.min' v

noncomputable def shared (C : Circuit) : Finset L := by
  classical exact Finset.univ.filter fun i => Common (A C i) (B C i)
def silent (C : Circuit) : Finset L :=
  Finset.univ.filter fun i => A C i = ∅ ∨ B C i = ∅
noncomputable def nested (C : Circuit) : Finset L := by
  classical exact Finset.univ.filter fun i => Early (A C i) (B C i) ∨ Early (B C i) (A C i)

noncomputable def cleanPorts (C : Circuit) (bad : Finset L) : Finset (Fin 24) := by
  classical exact Finset.univ.filter fun t =>
    literalLabel t ∉ bad ∧
    (if t.val < 12 then Early (A C (literalLabel t)) (B C (literalLabel t))
                   else Early (B C (literalLabel t)) (A C (literalLabel t)))

noncomputable def adjustedQuarter (C : Circuit) (bad : Finset L) (t : Fin 24) : ℕ :=
  if t ∈ cleanPorts C bad then 2 else singletonQuarter C t

theorem row_label : ∀ i : L, literalLabel (rowPort i) = i := by decide
theorem col_label : ∀ i : L, literalLabel (colPort i) = i := by decide
private theorem row_lt : ∀ i : L, (rowPort i).val < 12 := by decide
private theorem col_ge : ∀ i : L, ¬(colPort i).val < 12 := by decide

@[simp] theorem row_clean (C : Circuit) (bad : Finset L) (i : L) :
    rowPort i ∈ cleanPorts C bad ↔ i ∉ bad ∧ Early (A C i) (B C i) := by
  classical simp only [cleanPorts,Finset.mem_filter,Finset.mem_univ,true_and,row_label,row_lt,ite_true]
@[simp] theorem col_clean (C : Circuit) (bad : Finset L) (i : L) :
    colPort i ∈ cleanPorts C bad ↔ i ∉ bad ∧ Early (B C i) (A C i) := by
  classical simp only [cleanPorts,Finset.mem_filter,Finset.mem_univ,true_and,col_label,col_ge,ite_false]

theorem qsig (C : Circuit) (t : Fin 24) :
    singletonQuarter C t = CrownLabelCap.weight (sig C t).card := by
  simp [singletonQuarter,CrownLabelCap.weight,sig,activeOrIds_card]

theorem union_cap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (i : L) :
    (A C i ∪ B C i).card ≤ 2 := by
  have ha := literal_active_subset C hm (rowPort i)
  have hb := literal_active_subset C hm (colPort i)
  rw [row_label] at ha
  rw [col_label] at hb
  have h := Finset.card_le_card (Finset.union_subset ha hb)
  rw [activeOrIds_card] at h
  have d := crown_trueOrFlags_le i C hm rep
  change (activeOrIds C.gates (singleInput (rowPort i)) ∪
    activeOrIds C.gates (singleInput (colPort i))).card ≤ 2
  omega
end PEqualNP.Research.MissingCell.CrownLabels
