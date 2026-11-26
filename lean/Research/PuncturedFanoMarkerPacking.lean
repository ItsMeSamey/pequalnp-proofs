import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Signatures are natural-number bit masks. The low eighteen bits correspond
to mandatory edges; the next nineteen bits correspond to critical negatives.
Inputs 0 through 6 are points. Columns 0,2,3,4,5,6 use input bits 7 through 12. -/
namespace PuncturedFanoMarkers

def lines : List Nat := [0,2,3,4,5,6]

def positives : List Nat := lines.zipIdx.flatMap fun (column,j) =>
  ([0,1,3] : List Nat).map fun shift => 2^((column+shift)%7) + 2^(7+j)

def negatives : List Nat :=
  [464,676,771,1220,1346,1472,1542,2196,2321,2565,2817,3084,4272,4370,4642,4768,5130,6168,7176]

def accepts (x : Nat) : Bool := positives.any fun e => x &&& e == e

def criticalChecks : Bool :=
  positives.length == 18 && positives.eraseDups.length == 18 &&
  negatives.length == 19 && negatives.eraseDups.length == 19 &&
  negatives.all fun b => !accepts b &&
    ((List.range 13).filter fun v => accepts (b ||| 2^v)).length == 9

theorem critical_inputs_checked : criticalChecks = true := by decide

def positiveMask : Nat := 2^18-1
def allMask : Nat := 2^37-1
def negativeMask : Nat := allMask - positiveMask

def raw (v : Nat) : Nat :=
  (positives ++ negatives).zipIdx.foldl (fun mask (x,j) =>
    if x.testBit v then mask ||| 2^j else mask) 0

def inputs : List Nat := (List.range 13).map raw

/-- An earlier OR with two distinct raw parents. -/
def candidates : List Nat := inputs.zipIdx.flatMap fun (x,i) =>
  (inputs.drop (i+1)).map (fun y => x ||| y)

def compatible (a b : Nat) : Bool := a &&& b &&& negativeMask == 0

def doubles : List (List Nat) := candidates.zipIdx.flatMap fun (a,i) =>
  ((candidates.drop (i+1)).filter (compatible a)).map (fun b => [a,b])

def families : List (List Nat) := [[]] ++ candidates.map (fun a => [a]) ++ doubles

def noThird : Bool := doubles.all fun d =>
  !candidates.any fun c => d.all fun m => compatible m c

def tripleCheck : Bool :=
  candidates.length == 78 && candidates.eraseDups.length == 78 &&
  doubles.length == 15 && noThird

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
theorem compatible_markers_checked : tripleCheck = true := by decide

/-- The common true raw variables of two distinct edge assignments have size
at most one. Thus a conjunction true on both reduces to that one variable
or the empty conjunction. -/
def atMostOneBit (x : Nat) : Bool := x &&& (x-1) == 0

def commonChecks : Bool := positives.all fun a => positives.all fun b =>
  a == b || (atMostOneBit (a &&& b) &&
    negatives.any fun c => (a &&& b) &&& c == a &&& b)

theorem common_positive_inputs_checked : commonChecks = true := by decide

/-- All products of a subset of the markers; the empty subset gives true. -/
def products (f : List Nat) : List Nat :=
  f.foldl (fun ps m => ps ++ ps.map (fun p => p &&& m)) [allMask]

/-- Every truncated AND covering two or more mandatory edges has one of
these signatures after deleting monomial terms that hit no positive edge.
The monomial factor must be true or one raw bit, by commonChecks. -/
def largeCharges (f : List Nat) : List Nat :=
  (((allMask :: inputs).flatMap fun r => (products f).map fun m => r &&& m).filter
    fun z => z &&& negativeMask == 0 && !atMostOneBit (z &&& positiveMask)).eraseDups

def atMostTwoBits (x : Nat) : Bool := atMostOneBit (x &&& (x-1))

def chargeCheck : Bool := families.all fun f =>
  let z := largeCharges f
  z.length ≤ 2 && z.all atMostTwoBits

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
theorem marker_charges_checked : chargeCheck = true := by decide

theorem at_most_two_large_charges (f : List Nat) (hf : f ∈ families) :
    (largeCharges f).length ≤ 2 ∧ ∀ z ∈ largeCharges f, atMostTwoBits z = true := by
  have h := List.all_eq_true.mp marker_charges_checked f hf
  simpa [Bool.and_eq_true,List.all_eq_true] using h

end PuncturedFanoMarkers

namespace PuncturedFanoMarkers

def pairExtensionCheck : Bool := candidates.all fun a => candidates.all fun b =>
  !compatible a b || (families.any (fun f => f.contains a && f.contains b)) &&
    !(candidates.any fun c => compatible a c && compatible b c)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
theorem pair_extension_checked : pairExtensionCheck = true := by decide

theorem admitted_marker_set (S : Finset Nat) (hc : ∀ a ∈ S, a ∈ candidates)
    (hs : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → compatible a b = true) :
    ∃ f ∈ families, ∀ a ∈ S, a ∈ f := by
  classical
  by_cases pair : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · obtain ⟨a,ha,b,hb,hab⟩ := pair
    have h := List.all_eq_true.mp (List.all_eq_true.mp pair_extension_checked a (hc a ha)) b (hc b hb)
    have comp := hs a ha b hb hab
    simp only [comp,Bool.not_true,Bool.false_or,Bool.and_eq_true,List.any_eq_true,
      List.contains_iff_mem,Bool.not_eq_true'] at h
    obtain ⟨⟨f,hf,af,bf⟩,no⟩ := h
    refine ⟨f,hf,?_⟩
    intro c hcs
    by_cases ea : a=c
    · exact ea ▸ af
    by_cases eb : b=c
    · exact eb ▸ bf
    have clash : (candidates.any fun z => compatible a z && compatible b z) = true :=
      List.any_eq_true.mpr ⟨c,hc c hcs,by simp [hs a ha c hcs ea,hs b hb c hcs eb]⟩
    simp_all
  · by_cases ne : S.Nonempty
    · obtain ⟨a,ha⟩ := ne
      refine ⟨[a],by simp [families,hc a ha],?_⟩
      intro b hb
      by_cases eq : a=b
      · simp [eq]
      · exact False.elim (pair ⟨a,ha,b,hb,eq⟩)
    · exact ⟨[],by simp [families],fun a ha => False.elim (ne ⟨a,ha⟩)⟩

end PuncturedFanoMarkers

namespace PuncturedFanoMarkers

/-- Closure under adding or omitting each of the thirteen raw literals.
Deduplication quotients only by equality on the 37 specified tests. -/
def rawConjunctions : List Nat :=
  inputs.foldl (fun ps x => (ps ++ ps.map (fun p => p &&& x)).eraseDups) [allMask]

/-- Direct check permitting every raw conjunction before marker intersections. -/
def allLargeCharges (f : List Nat) : List Nat :=
  ((rawConjunctions.flatMap fun r => (products f).map fun m => r &&& m).filter
    fun z => z &&& negativeMask == 0 && !atMostOneBit (z &&& positiveMask)).eraseDups

def reductionChecks : Bool :=
  rawConjunctions.length == 88 &&
  (rawConjunctions.all fun r => r &&& negativeMask == 0 || r &&& positiveMask == 0 ||
     r == allMask || inputs.contains r) &&
  (families.all fun f => (allLargeCharges f).all fun c => (largeCharges f).contains c)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem conjunction_reductions_checked : reductionChecks = true := by decide

theorem all_large_charges_in_library (f : List Nat) (hf : f ∈ families)
    (c : Nat) (hc : c ∈ allLargeCharges f) : c ∈ largeCharges f := by
  have h := conjunction_reductions_checked
  simp only [reductionChecks,Bool.and_eq_true] at h
  have z := List.all_eq_true.mp (List.all_eq_true.mp h.2 f hf) c hc
  simpa using z

end PuncturedFanoMarkers

namespace PuncturedFanoMarkers
open scoped BigOperators

def edgeSet (x : Nat) : Finset Nat := (Finset.range 18).filter (fun i => x.testBit i = true)

def packing (f : List Nat) : Finset Nat :=
  let removed := (largeCharges f).foldl
    (fun acc x => acc ||| (x - (x &&& (x-1)))) 0
  edgeSet (positiveMask ^^^ removed)

def packingChecks : Bool := families.all fun f =>
  decide (16 ≤ (packing f).card) &&
    (largeCharges f).all (fun c => decide (((packing f) ∩ edgeSet c).card ≤ 1))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem packing_checked : packingChecks = true := by decide

/-- The finite charge library includes single-cell charges and any subset
of one enumerated multi-cell charge. A covering family needs at least
sixteen distinct members, so a sequence making the cover needs sixteen
steps as well. -/
theorem charge_cover_lower_bound (f : List Nat) (hf : f ∈ families)
    (charges : Finset (Finset Nat))
    (allowed : ∀ A ∈ charges, A.card ≤ 1 ∨ ∃ c ∈ largeCharges f, A ⊆ edgeSet c)
    (covers : Finset.range 18 ⊆ charges.biUnion id) : 16 ≤ charges.card := by
  have packed := List.all_eq_true.mp packing_checked f hf
  simp only [Bool.and_eq_true] at packed
  obtain ⟨hsize,hone⟩ := packed
  have lower : 16 ≤ (packing f).card := of_decide_eq_true hsize
  have single (A : Finset Nat) (hA : A ∈ charges) : (packing f ∩ A).card ≤ 1 := by
    rcases allowed A hA with h | ⟨c,hc,ha⟩
    · exact (Finset.card_le_card Finset.inter_subset_right).trans h
    · have limit : (packing f ∩ edgeSet c).card ≤ 1 :=
        of_decide_eq_true (List.all_eq_true.mp hone c hc)
      exact (Finset.card_le_card (Finset.inter_subset_inter_left ha)).trans limit
  have sub : packing f ⊆ charges.biUnion (fun A => packing f ∩ A) := by
    intro i hi
    have hin : i ∈ Finset.range 18 := (Finset.mem_filter.mp hi).1
    obtain ⟨A,hA,ha⟩ := Finset.mem_biUnion.mp (covers hin)
    exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_inter.mpr ⟨hi,ha⟩⟩
  calc
    16 ≤ (packing f).card := lower
    _ ≤ (charges.biUnion (fun A => packing f ∩ A)).card := Finset.card_le_card sub
    _ ≤ ∑ A ∈ charges, (packing f ∩ A).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ charges, 1 := Finset.sum_le_sum single
    _ = charges.card := by simp

end PuncturedFanoMarkers

namespace PuncturedFanoMarkers

/-- Every compatible set of raw-pair markers has an enumerated containing
family. Even granting all 88 raw conjunction signatures and every subset
of that family's markers, sixteen distinct charges are necessary. -/
theorem compatible_set_charge_bound (S : Finset Nat) (hc : ∀ a ∈ S, a ∈ candidates)
    (hs : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → compatible a b = true) :
    ∃ f ∈ families, (∀ a ∈ S, a ∈ f) ∧ ∀ charges : Finset (Finset Nat),
      (∀ A ∈ charges, A.card ≤ 1 ∨ ∃ c ∈ allLargeCharges f, A ⊆ edgeSet c) →
      Finset.range 18 ⊆ charges.biUnion id → 16 ≤ charges.card := by
  obtain ⟨f,hf,hS⟩ := admitted_marker_set S hc hs
  refine ⟨f,hf,hS,?_⟩
  intro charges allowed covers
  apply charge_cover_lower_bound f hf charges _ covers
  intro A ha
  rcases allowed A ha with h | ⟨c,hc',hsub⟩
  · exact Or.inl h
  · exact Or.inr ⟨c,all_large_charges_in_library f hf c hc',hsub⟩

end PuncturedFanoMarkers
