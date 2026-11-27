import RowCover

-- PhysicalRows

namespace Research.Graph9822.FourSaturation

def maskInput (m : Nat) (i : Fin 10) : Bool := m.testBit i.val

def inputMask (x : Fin 10 → Bool) : Fin 1024 :=
  let b := BitVec.ofBoolListLE (List.ofFn x)
  ⟨b.toNat, by simpa [b] using b.isLt⟩

theorem inputMask_roundtrip (x : Fin 10 → Bool) : maskInput (inputMask x).val = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem physical_rows_suffice (F : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → F x = true → F y = true)
    (pos : ∀ e ∈ edges, F (maskInput (edgeMask e)) = true)
    (neg : ∀ w ∈ witnesses, F (maskInput w) = false)
    (x : Fin 10 → Bool) : F x = accepts (inputMask x).val := by
  have hmono : ∀ a b, below a b = true →
      F (maskInput a) = true → F (maskInput b) = true := by
    intro a b h
    apply mono
    intro i hi
    have hab : a &&& b = a := by simpa [below] using h
    have hbit := congrArg (fun k : Nat => k.testBit i.val) hab
    change a.testBit i.val = true at hi
    simpa [Nat.testBit_and, hi, maskInput] using hbit
  have h := checked_rows_suffice (fun k => F (maskInput k)) hmono pos neg (inputMask x)
  simpa [inputMask_roundtrip] using h

end Research.Graph9822.FourSaturation

-- PostedGraph

namespace Research.Graph9822.FourSaturation

/-- The graph predicate in the original full-cube statement of L-meta-9822. -/
def posted (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) ||
  (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)

theorem mask_graph (m : Nat) : accepts m = posted (maskInput m) := by
  simp [posted, maskInput, accepts, edges, Bool.or_assoc] <;> rfl

theorem full_graph_of_rows (F : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → F x = true → F y = true)
    (pos : ∀ e ∈ edges, F (maskInput (edgeMask e)) = true)
    (neg : ∀ w ∈ witnesses, F (maskInput w) = false) :
    ∀ x, F x = posted x := by
  intro x
  rw [physical_rows_suffice F mono pos neg x, mask_graph, inputMask_roundtrip]

end Research.Graph9822.FourSaturation

-- SignedRowControl9822
namespace PEqualNP.Outside.L_meta_9822.SignedRowControl
open Research.Graph9822.FourSaturation

def decoy (row : Nat) : Bool :=
  !([(0,3),(0,8),(2,5),(1,4),(1,3),(2,4),(4,6)] : List (Nat × Nat)).any
    (fun p => row.testBit p.1 && row.testBit p.2)

theorem decoyOnProbes :
    edges.all (fun e => decoy ((1 <<< e.1) ||| (1 <<< e.2))) = true ∧
    witnesses.all (fun m => !decoy m) = true ∧ decoy 0 ≠ accepts 0 := by decide +kernel

end PEqualNP.Outside.L_meta_9822.SignedRowControl

-- ReceiverFacts9822
namespace PEqualNP.Outside.L_meta_9822.Receivers
open Research.Graph9822.FourSaturation

theorem negativeRowsSeparate : ∀ u v : Fin 10, u ≠ v →
    witnesses.any (fun m => !m.testBit u.val && m.testBit v.val) = true := by decide +kernel

theorem negativeRowsOmitTwo : ∀ u v : Fin 10,
    witnesses.any (fun m => !m.testBit u.val && !m.testBit v.val) = true := by decide +kernel

structure ExactReceivers {α : Type} (reaches : Fin 10 → α → Prop) : Prop where
  realize : ∀ m ∈ witnesses, ∃ a, ∀ v : Fin 10, reaches v a ↔ m.testBit v.val = false

theorem indispensable {α : Type} {reaches : Fin 10 → α → Prop} (r : ExactReceivers reaches)
    (u v : Fin 10) (different : u ≠ v) : ∃ a, reaches u a ∧ ¬ reaches v a := by
  obtain ⟨m,hm,e⟩ := List.any_eq_true.mp (negativeRowsSeparate u v different)
  obtain ⟨a,h⟩ := r.realize m hm
  have bits : m.testBit u.val = false ∧ m.testBit v.val = true := by simpa using e
  refine ⟨a,(h u).2 bits.1,?_⟩
  intro hv
  have bad := (h v).mp hv
  simp [bits.2] at bad

theorem overlap {α : Type} {reaches : Fin 10 → α → Prop} (r : ExactReceivers reaches)
    (u v : Fin 10) : ∃ a, reaches u a ∧ reaches v a := by
  obtain ⟨m,hm,e⟩ := List.any_eq_true.mp (negativeRowsOmitTwo u v)
  obtain ⟨a,h⟩ := r.realize m hm
  have bits : m.testBit u.val = false ∧ m.testBit v.val = false := by simpa using e
  exact ⟨a,(h u).2 bits.1,(h v).2 bits.2⟩

theorem distinctDirectAxes {α β : Type} {reaches : Fin 10 → α → Prop}
    (r : ExactReceivers reaches) (active : β → α → Prop) (bit : β → α → Bool)
    {u v : Fin 10} (hne : u ≠ v) {i j : β} {su sv : Bool}
    (hu : ∀ a, reaches u a ↔ active i a ∧ bit i a = su)
    (hv : ∀ a, reaches v a ↔ active j a ∧ bit j a = sv) : i ≠ j := by
  rintro rfl
  obtain ⟨t,ru,rv⟩ := overlap r u v
  have eq := ((hu t).1 ru).2.symm.trans ((hv t).1 rv).2
  obtain ⟨w,wu,wv⟩ := indispensable r u v hne
  exact wv ((hv w).2 ⟨((hu w).1 wu).1,((hu w).1 wu).2.trans eq⟩)

end PEqualNP.Outside.L_meta_9822.Receivers
