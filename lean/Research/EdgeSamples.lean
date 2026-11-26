import Std

/-! The edge and negative samples from L-meta-8032, encoded as eleven-bit masks.
A mask contains an edge when it contains the bits at both listed endpoints. -/
namespace PEqualNP.EdgeSamples8032

def edges : List (Nat × Nat) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),
   (5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def negatives : List Nat :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,
   596,1066,1186,1288,1408,1546]

def edgeMask (e : Nat × Nat) : Nat := (1 <<< e.1) ||| (1 <<< e.2)
def Submask (x y : Nat) : Prop := x &&& y = x
instance (x y : Nat) : Decidable (Submask x y) := inferInstanceAs (Decidable (x &&& y = x))

def independent (x : Nat) : Bool :=
  edges.all fun e => !decide (Submask (edgeMask e) x)

private theorem trans {x y z : Nat} (h : Submask x y) (k : Submask y z) : Submask x z := by
  unfold Submask at *
  calc
    x &&& z = (x &&& y) &&& z := congrArg (· &&& z) h.symm
    _ = x &&& (y &&& z) := Nat.and_assoc ..
    _ = x := (congrArg (x &&& ·) k).trans h

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem coveredTable : (List.range 2048).all (fun x =>
    !independent x || negatives.any (fun y => decide (Submask x y))) = true := by decide

theorem covered {x : Nat} (hx : x < 2048) (hi : independent x = true) :
    ∃ y ∈ negatives, Submask x y := by
  have h := List.all_eq_true.mp coveredTable x (List.mem_range.mpr hx)
  simpa [hi] using h

private theorem checkedNegatives : negatives.all (fun x =>
    decide (x < 2048) && independent x &&
    negatives.all (fun y => !decide (Submask x y) || decide (x = y))) = true := by decide

theorem negative_maximal {x : Nat} (hx : x ∈ negatives) :
    x < 2048 ∧ independent x = true ∧
      ∀ y < 2048, independent y = true → Submask x y → y = x := by
  have t := List.all_eq_true.mp checkedNegatives x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at t
  refine ⟨t.1.1, t.1.2, ?_⟩
  intro y hy hi hxy
  obtain ⟨z, hz, hyz⟩ := covered hy hi
  have hxz := trans hxy hyz
  have eq := t.2 z hz
  simp [hxz] at eq
  subst z
  unfold Submask at *
  exact hyz.symm.trans ((Nat.and_comm y x).trans hxy)

theorem negative_count : negatives.length = 24 ∧ negatives.Nodup := by decide

theorem mem_negatives_iff_maximal {x : Nat} :
    x ∈ negatives ↔ x < 2048 ∧ independent x = true ∧
      ∀ y < 2048, independent y = true → Submask x y → y = x := by
  refine ⟨negative_maximal, ?_⟩
  rintro ⟨hx, hi, maximal⟩
  obtain ⟨y, hy, hxy⟩ := covered hx hi
  have valid := negative_maximal hy
  exact (maximal y valid.1 valid.2.1 hxy) ▸ hy

theorem exact_on_masks (f : Nat → Bool)
    (mono : ∀ {x y : Nat}, Submask x y → f x = true → f y = true)
    (positive : ∀ e ∈ edges, f (edgeMask e) = true)
    (negative : ∀ y ∈ negatives, f y = false)
    {x : Nat} (hx : x < 2048) : f x = !independent x := by
  cases hi : independent x with
  | false =>
    have h : ∃ e ∈ edges, Submask (edgeMask e) x := by
      simp [independent, List.all_eq_false] at hi
      obtain ⟨a, b, hab, hs⟩ := hi
      exact ⟨(a,b), hab, hs⟩
    obtain ⟨e, he, hes⟩ := h
    exact mono hes (positive e he)
  | true =>
    obtain ⟨y, hy, hxy⟩ := covered hx hi
    cases hf : f x with
    | false => rfl
    | true =>
      have ht := mono hxy hf
      simp [negative y hy] at ht

end PEqualNP.EdgeSamples8032

#print axioms PEqualNP.EdgeSamples8032.covered
#print axioms PEqualNP.EdgeSamples8032.negative_maximal
#print axioms PEqualNP.EdgeSamples8032.exact_on_masks
