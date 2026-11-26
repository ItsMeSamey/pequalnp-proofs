import T2PhysicalMaximum
import T2ReaderActivation
import T2CubeAgreement
import Batteries.Tactic.OpenPrivate

namespace T2SoleAndDirty
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2PhysicalMaximum
open T2RawIsolation T2SoleOrSplice T2ReaderActivation
open private read_earlier from GateSurplus

theorem bank_of_get (u v : List Bool) (len : u.length = v.length)
    (h : ∀ i, Imp (u.getD i false) (v.getD i false)) : BankLE u v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => exact .nil
    | cons _ _ => simp at len
  | cons a u ih =>
    cases v with
    | nil => simp at len
    | cons b v =>
      exact .cons (h 0) (ih v (by simpa using len) (fun i => h (i+1)))

theorem vector_le {n : Nat} {s t : Finset (Fin n)} (sub : s ⊆ t) :
    BankLE (vector s) (vector t) := by
  apply bank_of_get _ _ (by simp [vector])
  intro i
  rw [vec_get,vec_get]
  by_cases hi : i<n
  · simpa [hi,Imp] using @sub ⟨i,hi⟩
  · simp [hi,Imp]

def andGate (b : Bool) (x p : Nat) :=
  if b then binary .and x p else binary .and p x

theorem and_singleton (n : Nat) (x y : Fin n) (different : x ≠ y)
    (p out : Nat) (pre post : List Gate) (orient : Bool)
    (distinct : p ≠ x.val) (notOut : out ≠ x.val)
    (computes : Computes n ⟨pre ++ andGate orient x.val p :: post,out⟩)
    (left : ∀ g ∈ pre,x.val ∉ g.inputs) (right : ∀ g ∈ post,x.val ∉ g.inputs) :
    (run pre (vector {y})).getD p false = true := by
  have block := other_not_absorbing pre post .and orient x.val p out (vector {y})
    (vector (insert x {y})) (off_insert {y} x) distinct notOut left right
  have yes : Circuit.eval ⟨pre ++ andGate orient x.val p :: post,out⟩ (vector (insert x {y})) =
      true := (computes _).mpr (by simp [Finset.card_insert_of_notMem,different])
  have noOne := computes {y}
  have changes : Circuit.eval ⟨pre ++ andGate orient x.val p :: post,out⟩ (vector {y}) ≠
      Circuit.eval ⟨pre ++ andGate orient x.val p :: post,out⟩ (vector (insert x {y})) := by
    intro eq
    have impossible := noOne.mp (eq.trans yes)
    simp at impossible
  have no := block changes
  cases h : (run pre (vector {y})).getD p false <;> simp_all [absorbing]

theorem and_nonempty (n : Nat) (x : Fin n) (s : Finset (Fin n)) (nz : s.Nonempty)
    (rawOff : x ∉ s) (p out : Nat) (pre : List Raw) (post : List Gate) (orient : Bool)
    (distinct : p ≠ x.val) (notOut : out ≠ x.val)
    (computes : Computes n ⟨pre.map native ++ andGate orient x.val p :: post,out⟩)
    (left : ∀ g ∈ pre.map native,x.val ∉ g.inputs) (right : ∀ g ∈ post,x.val ∉ g.inputs) :
    (run (pre.map native) (vector s)).getD p false = true := by
  obtain ⟨y,hy⟩ := nz
  have diff : x ≠ y := fun h => rawOff (h.symm ▸ hy)
  have hit := and_singleton n x y diff p out (pre.map native) post orient distinct
    notOut computes left right
  have le := run_mono pre (vector_le (Finset.singleton_subset_iff.mpr hy))
  exact le.get p hit


/-- A signal accepting every singleton away from x is an internal wire as soon
as at least two distinct other inputs exist. -/
theorem other_internal (n : Nat) (hn : 3 ≤ n) (x : Fin n) (p out : Nat)
    (pre post : List Gate) (orient : Bool) (distinct : p ≠ x.val) (notOut : out ≠ x.val)
    (computes : Computes n ⟨pre ++ andGate orient x.val p :: post,out⟩)
    (left : ∀ g ∈ pre,x.val ∉ g.inputs) (right : ∀ g ∈ post,x.val ∉ g.inputs) :
    n ≤ p := by
  classical
  by_contra! raw
  have card : 1 < ((Finset.univ : Finset (Fin n)).erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp
    omega
  obtain ⟨y,hy,z,hz,yz⟩ := Finset.one_lt_card.mp card
  have id (q : Fin n) (hq : q ≠ x) : (⟨p,raw⟩ : Fin n) = q := by
    have hit := and_singleton n x q hq.symm p out pre post orient distinct notOut computes left right
    rw [read_earlier _ _ _ (by simpa [vector] using raw), vec_get] at hit
    simpa [raw] using hit
  have py := id y (Finset.mem_erase.mp hy).1
  have pz := id z (Finset.mem_erase.mp hz).1
  exact yz (py.symm.trans pz)

#print axioms other_internal
#print axioms and_nonempty
end T2SoleAndDirty
