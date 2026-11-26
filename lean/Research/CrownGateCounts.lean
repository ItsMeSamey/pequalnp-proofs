import Research.TrueOrCount

namespace CrownDiagonalCharge
variable {α : Type*} [DecidableEq α]

abbrev Cell (α : Type*) := α × α
abbrev Support (α : Type*) := Set (Cell α)

def conjSupport (rows cols : Finset α) : Support α :=
  {p | (∀ i ∈ rows, i = p.1) ∧ (∀ i ∈ cols, i = p.2)}

def diagFree (A : Support α) : Prop := ∀ i, (i,i) ∉ A

def Charged (S : Finset (Cell α)) (A : Support α) : Prop :=
  (∃ rows cols : Finset α, A = conjSupport rows cols ∧ ¬ diagFree A) ∨
    A ⊆ (S : Set (Cell α))

theorem conj_inter (a b c d : Finset α) :
    conjSupport a b ∩ conjSupport c d = conjSupport (a ∪ c) (b ∪ d) := by
  ext p
  simp only [Set.mem_inter_iff, conjSupport, Set.mem_ofPred_eq, Finset.mem_union]
  grind

theorem diagFree_conj_unique {r c : Finset α} (h : diagFree (conjSupport r c))
    {x y : Cell α} (hx : x ∈ conjSupport r c) (hy : y ∈ conjSupport r c) : x = y := by
  obtain ⟨hr,hc⟩ := hx
  obtain ⟨hr',hc'⟩ := hy
  by_cases h1 : x.1 = y.1
  · by_cases h2 : x.2 = y.2
    · exact Prod.ext h1 h2
    · exfalso
      apply h x.1
      exact ⟨hr, fun i hi => False.elim (h2 ((hc i hi).symm.trans (hc' i hi)))⟩
  · exfalso
    apply h x.2
    exact ⟨fun i hi => False.elim (h1 ((hr i hi).symm.trans (hr' i hi))), hc⟩

omit [DecidableEq α] in
theorem charged_mono {S T : Finset (Cell α)} (hst : S ⊆ T) {A : Support α}
    (ha : Charged S A) : Charged T A := by
  rcases ha with h | h
  · exact Or.inl h
  · exact Or.inr (fun x hx => hst (h hx))

omit [DecidableEq α] in
theorem charge_or {S : Finset (Cell α)} {A B : Support α}
    (ha : Charged S A) (hb : Charged S B) (hz : diagFree (A ∪ B)) :
    Charged S (A ∪ B) := by
  have sub (C : Support α) (hc : Charged S C) (hs : C ⊆ A ∪ B) : C ⊆ ↑S := by
    rcases hc with ⟨_,_,_,hh⟩ | hh
    · exact False.elim (hh (fun i hi => hz i (hs hi)))
    · exact hh
  exact Or.inr (Set.union_subset (sub _ ha Set.subset_union_left) (sub _ hb Set.subset_union_right))

theorem charge_and {S : Finset (Cell α)} {A B : Support α}
    (ha : Charged S A) (hb : Charged S B) :
    ∃ T : Finset (Cell α), S ⊆ T ∧ T.card ≤ S.card + 1 ∧ Charged T (A ∩ B) := by
  classical
  rcases ha with ⟨r,c,rfl,_⟩ | ha
  · rcases hb with ⟨r',c',rfl,_⟩ | hb
    · rw [conj_inter]
      let C := conjSupport (r ∪ r') (c ∪ c')
      by_cases hz : diagFree C
      · by_cases hn : C.Nonempty
        · obtain ⟨x,hx⟩ := hn
          refine ⟨insert x S, Finset.subset_insert .., Finset.card_insert_le .., Or.inr ?_⟩
          intro y hy
          have he := diagFree_conj_unique hz hy hx
          simp [he]
        · exact ⟨S, fun _ h => h, by omega, Or.inr (fun y hy => False.elim (hn ⟨y,hy⟩))⟩
      · exact ⟨S, fun _ h => h, by omega, Or.inl ⟨_,_,rfl,hz⟩⟩
    · exact ⟨S, fun _ h => h, by omega, Or.inr (fun _ hp => hb hp.2)⟩
  · exact ⟨S, fun _ h => h, by omega, Or.inr (fun _ hp => ha hp.1)⟩

end CrownDiagonalCharge

namespace CrownDiagonalCharge
variable {α : Type*} [DecidableEq α]

/-- Every raw one-hot wire and both constants are present in the initial set.
The enlarged basis also permits arbitrary diagonal-live pure conjunctions. -/
inductive Trace (α : Type*) [DecidableEq α] : Set (Support α) → ℕ → Prop
  | initial : Trace α {A | Charged ∅ A} 0
  | orGate {K m A B} (prev : Trace α K m) (ha : A ∈ K) (hb : B ∈ K)
      (hf : diagFree (A ∪ B)) : Trace α (insert (A ∪ B) K) m
  | andGate {K m A B} (prev : Trace α K m) (ha : A ∈ K) (hb : B ∈ K) :
      Trace α (insert (A ∩ B) K) (m + 1)

theorem trace_charged {K : Set (Support α)} {m : ℕ} (h : Trace α K m) :
    ∃ S : Finset (Cell α), S.card ≤ m ∧ ∀ A ∈ K, Charged S A := by
  induction h with
  | initial => exact ⟨∅, by simp, fun _ h => h⟩
  | orGate prev ha hb hf ih =>
    obtain ⟨S,hc,hK⟩ := ih
    refine ⟨S,hc,?_⟩
    intro X hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact charge_or (hK _ ha) (hK _ hb) hf
    · exact hK X hx
  | andGate prev ha hb ih =>
    obtain ⟨S,hc,hK⟩ := ih
    obtain ⟨T,hs,hc',ht⟩ := charge_and (hK _ ha) (hK _ hb)
    refine ⟨T,by omega,?_⟩
    intro X hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ht
    · exact charged_mono hs (hK X hx)

theorem trace_crown_and_count {n m : ℕ} {K : Set (Support (Fin n))}
    (trace : Trace (Fin n) K m)
    (out : {p : Cell (Fin n) | p.1 ≠ p.2} ∈ K) : n * (n-1) ≤ m := by
  obtain ⟨S,hc,hK⟩ := trace_charged trace
  rcases hK _ out with ⟨_,_,_,hd⟩ | hs
  · exact False.elim (hd (fun i hi => hi rfl))
  · have sub : (Finset.univ : Finset (Fin n)).offDiag ⊆ S := by
      intro p hp
      exact hs (Finset.mem_offDiag.mp hp).2.2
    have hc' := Finset.card_le_card sub
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc'
    simpa [Nat.mul_sub] using hc'.trans hc

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

abbrev Env (n : ℕ) := Cell (Fin n) → List Bool

def wire {n : ℕ} (w : Env n) (i : ℕ) : Support (Fin n) := {p | (w p).getD i false = true}

def gateSupport {n : ℕ} (g : Gate) (w : Env n) : Support (Fin n) :=
  {p | g.op.eval (g.inputs.map fun i => (w p).getD i false) = true}

def push {n : ℕ} (g : Gate) (w : Env n) : Env n :=
  fun p => w p ++ [g.op.eval (g.inputs.map fun i => (w p).getD i false)]

def orQuiet {n : ℕ} : List Gate → Env n → Prop
  | [], _ => True
  | g :: gs, w => (g.op = .or → diagFree (gateSupport g w)) ∧ orQuiet gs (push g w)

def isAndGate (g : Gate) : Bool := match g.op with | .and => true | _ => false

theorem initial_false {n : ℕ} : Charged (∅ : Finset (Cell (Fin n))) ∅ :=
  Or.inr (by simp)

theorem initial_true {n : ℕ} : Charged (∅ : Finset (Cell (Fin n))) Set.univ := by
  by_cases hn : n = 0
  · subst n
    exact Or.inr (fun p _ => Fin.elim0 p.1)
  · refine Or.inl ⟨∅,∅,?_,?_⟩
    · ext p
      simp [conjSupport]
    · intro h
      exact h ⟨0,by omega⟩ (Set.mem_univ _)

theorem initial_wire {n : ℕ} (i : ℕ) :
    Charged ∅ (wire (fun p : Cell (Fin n) => oneEach p.1 p.2) i) := by
  by_cases hi : i < n
  · let u : Fin n := ⟨i,hi⟩
    have eq : wire (fun p : Cell (Fin n) => oneEach p.1 p.2) i =
        conjSupport {u} ∅ := by
      ext p
      simp [wire, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left,
        hi, conjSupport, u]
    rw [eq]
    exact Or.inl ⟨_,_,rfl,fun h => h u (by simp [conjSupport])⟩
  · by_cases hj : i-n < n
    · let v : Fin n := ⟨i-n,hj⟩
      have eq : wire (fun p : Cell (Fin n) => oneEach p.1 p.2) i =
          conjSupport ∅ {v} := by
        ext p
        simp [wire, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
          Nat.le_of_not_gt hi, hj, conjSupport, v]
      rw [eq]
      exact Or.inl ⟨_,_,rfl,fun h => h v (by simp [conjSupport])⟩
    · have eq : wire (fun p : Cell (Fin n) => oneEach p.1 p.2) i = ∅ := by
        ext p
        simp [wire, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
          Nat.le_of_not_gt hi, hj]
      rw [eq]
      exact initial_false

theorem push_known {n k : ℕ} {w : Env n} {K : Set (Support (Fin n))} (g : Gate)
    (hl : ∀ p, (w p).length = k) (hw : ∀ i, wire w i ∈ K)
    (hg : gateSupport g w ∈ K) : ∀ i, wire (push g w) i ∈ K := by
  intro i
  by_cases h : i=k
  · subst i
    convert hg using 1
    ext p
    simp [wire, push, gateSupport, List.getD_eq_getElem?_getD, ← hl p]
  · convert hw i using 1
    ext p
    by_cases ha : i<k
    · have hb : i < (w p).length := by rw [hl]; exact ha
      simp [wire, push, List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
    · have hb : (w p).length ≤ i := by rw [hl]; omega
      have hc : (w p ++ [g.op.eval (g.inputs.map fun j => (w p).getD j false)]).length ≤ i := by
        simp [hl]; omega
      have missing (z : List Bool) (hz : z.length ≤ i) : z.getD i false = false := by
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hz]
      change ((push g w p).getD i false = true) ↔ ((w p).getD i false = true)
      rw [missing (push g w p) hc, missing (w p) hb]

theorem gate_args {n : ℕ} (w : Env n) (g : Gate) {K : Set (Support (Fin n))}
    (hw : ∀ i, wire w i ∈ K) (h0 : ∅ ∈ K) (h1 : Set.univ ∈ K)
    (len : g.inputs.length ≤ 2) (hop : g.op = .and ∨ g.op = .or) :
    ∃ A ∈ K, ∃ B ∈ K, (g.op = .and → gateSupport g w = A ∩ B) ∧
      (g.op = .or → gateSupport g w = A ∪ B) := by
  cases h : g.inputs with
  | nil =>
    rcases hop with ha | ho
    · refine ⟨_,h1,_,h1,fun _ => ?_, by simp [ha]⟩
      ext p; simp [gateSupport,ha,h,GateOp.eval]
    · refine ⟨_,h0,_,h0,by simp [ho], fun _ => ?_⟩
      ext p; simp [gateSupport,ho,h,GateOp.eval]
  | cons a l =>
    cases hl : l with
    | nil =>
      refine ⟨_,hw a,_,hw a,?_,?_⟩
      all_goals intro hh; ext p; simp [gateSupport,wire,hh,h,hl,GateOp.eval]
    | cons b tail =>
      have ht : tail = [] := by simpa [h,hl] using len
      refine ⟨_,hw a,_,hw b,?_,?_⟩
      all_goals intro hh; ext p; simp [gateSupport,wire,hh,h,hl,ht,GateOp.eval]

theorem trace_eval {n : ℕ} (gs : List Gate) (w : Env n) (k m : ℕ)
    (K : Set (Support (Fin n))) (trace : Trace (Fin n) K m)
    (h0 : ∅ ∈ K) (h1 : Set.univ ∈ K) (hw : ∀ i, wire w i ∈ K)
    (hl : ∀ p, (w p).length = k)
    (ha : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hq : orQuiet gs w) :
    ∃ J : Set (Support (Fin n)), Trace (Fin n) J (m + (gs.filter isAndGate).length) ∧
    ∀ i, wire (fun p => (Circuit.mk gs i).wires (w p)) i ∈ J := by
  induction gs generalizing w k m K with
  | nil => exact ⟨K,by simpa using trace,hw⟩
  | cons g gs ih =>
    obtain ⟨hop,len⟩ := ha g (by simp)
    obtain ⟨A,hA,B,hB,an,orr⟩ := gate_args w g hw h0 h1 len hop
    obtain ⟨quiet,hq⟩ := hq
    let K' := insert (gateSupport g w) K
    have sub : K ⊆ K' := Set.subset_insert ..
    have hw' := push_known g hl (fun i => sub (hw i)) (Set.mem_insert .. : gateSupport g w ∈ K')
    have hl' : ∀ p, (push g w p).length = k+1 := by intro p; simp [push,hl]
    have ha' := fun a (h : a ∈ gs) => ha a (List.mem_cons_of_mem _ h)
    rcases hop with h | h
    · have tr : Trace (Fin n) K' (m+1) := by
        simpa only [K',an h] using Trace.andGate trace hA hB
      obtain ⟨J,th,wires⟩ := ih (push g w) (k+1) (m+1) K' tr (sub h0) (sub h1) hw' hl' ha' hq
      refine ⟨J,?_,wires⟩
      simpa [isAndGate,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using th
    · have tr : Trace (Fin n) K' m := by
        have hh : diagFree (A ∪ B) := (orr h) ▸ quiet h
        simpa only [K',orr h] using Trace.orGate trace hA hB hh
      obtain ⟨J,th,wires⟩ := ih (push g w) (k+1) m K' tr (sub h0) (sub h1) hw' hl' ha' hq
      refine ⟨J,?_,wires⟩
      simpa [isAndGate,h] using th

theorem circuit_crown_and_count (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin n => decide (u ≠ v)) C)
    (hq : orQuiet C.gates (fun p : Cell (Fin n) => oneEach p.1 p.2)) :
    n * (n-1) ≤ (C.gates.filter isAndGate).length := by
  let w := fun p : Cell (Fin n) => oneEach p.1 p.2
  obtain ⟨J,tr,hJ⟩ := trace_eval C.gates w (n+n) 0 _ Trace.initial initial_false initial_true
    initial_wire (fun p => by simp [w,oneEach]) hm hq
  have eq : wire (fun p : Cell (Fin n) => C.wires (w p)) C.output =
      {p : Cell (Fin n) | p.1 ≠ p.2} := by
    ext p
    change (C.eval (oneEach p.1 p.2) = true) ↔ _
    rw [rep p.1 p.2]
    simp
  have hout := hJ C.output
  change wire (fun p : Cell (Fin n) => C.wires (w p)) C.output ∈ J at hout
  rw [eq] at hout
  simpa using trace_crown_and_count tr hout

end CrownDiagonalCharge

open scoped Classical BigOperators
namespace CrownDiagonalCharge

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev RawTerm (α : Type*) := Finset α × Finset α

noncomputable def termCells (t : RawTerm α) : Finset (Cell α) :=
  Finset.univ.filter (fun p => p ∈ conjSupport t.1 t.2)

noncomputable def dnfCells (T : Finset (RawTerm α)) : Finset (Cell α) :=
  T.biUnion termCells

theorem term_inter_card_le_one (a b : RawTerm α)
    (hd : diagFree ((termCells a ∩ termCells b : Finset (Cell α)) : Support α)) :
    (termCells a ∩ termCells b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have mem (p : Cell α) : p ∈ termCells a ∩ termCells b ↔
      p ∈ conjSupport (a.1 ∪ b.1) (a.2 ∪ b.2) := by
    rw [← conj_inter]
    simp [termCells]
  apply diagFree_conj_unique (fun i hi => hd i ((mem _).mpr hi)) ((mem _).mp hx) ((mem _).mp hy)

theorem dnf_inter_card_le (A B : Finset (RawTerm α))
    (hd : diagFree ((dnfCells A ∩ dnfCells B : Finset (Cell α)) : Support α)) :
    (dnfCells A ∩ dnfCells B).card ≤ A.card * B.card := by
  let pieces (q : RawTerm α × RawTerm α) := termCells q.1 ∩ termCells q.2
  have sub (q : RawTerm α × RawTerm α) (hq : q ∈ A ×ˢ B) :
      pieces q ⊆ dnfCells A ∩ dnfCells B := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hq
    intro p hp
    obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨_,ha,h1⟩, Finset.mem_biUnion.mpr ⟨_,hb,h2⟩⟩
  have cover : dnfCells A ∩ dnfCells B ⊆ (A ×ˢ B).biUnion pieces := by
    intro p hp
    obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hp
    obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp h1
    obtain ⟨b,hb,hy⟩ := Finset.mem_biUnion.mp h2
    exact Finset.mem_biUnion.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,Finset.mem_inter.mpr ⟨hx,hy⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ q ∈ A ×ˢ B, (pieces q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ A ×ˢ B, 1 := Finset.sum_le_sum fun q hq =>
      term_inter_card_le_one _ _ (fun i hi => hd i (sub q hq hi))
    _ = _ := by simp

theorem two_term_empty_and_charge (A B : Finset (RawTerm α)) (S : Finset (Cell α))
    (ha : A.card ≤ 2) (hb : B.card ≤ 2)
    (hd : diagFree ((dnfCells A ∩ dnfCells B : Finset (Cell α)) : Support α)) :
    (S ∪ (dnfCells A ∩ dnfCells B)).card ≤ S.card + 4 := by
  have h := (dnf_inter_card_le A B hd).trans (Nat.mul_le_mul ha hb)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left h _)

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.Research.MissingCell

theorem orQuiet_of_diagonal_false {n : ℕ} (gs : List Gate) (w : Env n)
    (h : ∀ i : Fin n, allOrFalse gs (w (i,i))) : orQuiet gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · intro ho i hi
      have hz := (h i).1 (by simp [isOrGate, ho])
      change g.op.eval (g.inputs.map fun j => (w (i,i)).getD j false) = true at hi
      rw [hz] at hi
      contradiction
    · exact ih (push g w) (fun i => (h i).2)

theorem crown_orQuiet_of_budget (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (hc : (C.gates.filter isOrGate).length ≤ 21) :
    orQuiet C.gates (fun p : Cell (Fin 12) => oneEach p.1 p.2) :=
  orQuiet_of_diagonal_false _ _ (fun i => crown_all_ors_false i C hm hr hc)

theorem crown_and_count_of_or_budget (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (hc : (C.gates.filter isOrGate).length ≤ 21) :
    132 ≤ (C.gates.filter isAndGate).length := by
  exact circuit_crown_and_count 12 C hm hr (crown_orQuiet_of_budget C hm hr hc)

theorem crown_ors_of_size_forty (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (hc : C.size ≤ 40) : 22 ≤ (C.gates.filter isOrGate).length := by
  by_contra! small
  have lower := crown_and_count_of_or_budget C hm hr (by omega)
  have upper := List.length_filter_le isAndGate C.gates
  change C.gates.length ≤ 40 at hc
  omega

end CrownDiagonalCharge
