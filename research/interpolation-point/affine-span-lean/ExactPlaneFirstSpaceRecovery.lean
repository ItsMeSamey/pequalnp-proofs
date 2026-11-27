import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.FinRange

namespace ExactPlaneFirstSpaceRecovery
open Module Submodule
abbrev F := ZMod 2
abbrev V (N : ℕ) := Fin N→F
abbrev Space (N : ℕ) := Submodule F (V N)
abbrev Probe (N : ℕ) := Module.Dual F (V N)
variable {N : ℕ} {W : Type*}

structure Contract (L : Space N) (row : W→V N) (query : Probe N→Option W) : Prop where
  safe : ∀ f,query f=none → f∈L.dualAnnihilator
  violating : ∀ f w,query f=some w → row w∈L ∧ f (row w)≠0

/-- The generator can be replaced by any supplied list meeting the three certificate obligations. -/
structure Probes (N : ℕ) where
  list : Space N → List (Probe N)
  vanish : ∀ R f,f∈list R → f∈R.dualAnnihilator
  complete : ∀ R L : Space N,R≤L → (∀ f∈list R,f∈L.dualAnnihilator) → R=L
  length_le : ∀ R,(list R).length≤N

private theorem hasBasisList (E : Type*) [Field E] (N : ℕ) :
    ∀ R : Submodule E (Fin N → E), ∃ ls : List (Module.Dual E (Fin N → E)),
      (∀ f∈ls,f∈R.dualAnnihilator) ∧
      (∀ L : Submodule E (Fin N → E), R≤L → (∀ f∈ls,f∈L.dualAnnihilator) → R=L) ∧
      ls.length≤N := by
  classical
  intro R
  letI : Module.Free E R.dualAnnihilator := Module.Free.of_divisionRing E R.dualAnnihilator
  let B := Module.finBasis E R.dualAnnihilator
  let ls := List.ofFn fun i => (B i).val
  refine ⟨ls,?_,?_,?_⟩
  · intro f mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact (B i).property
  · intro L incl all
    refine le_antisymm incl (Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp ?_)
    intro f hf
    let C := L.dualAnnihilator.comap R.dualAnnihilator.subtype
    have full : (⊤ : Submodule E R.dualAnnihilator) ≤ C := by
      rw [←B.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact all _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact full (show (⟨f,hf⟩ : R.dualAnnihilator)∈(⊤ : Submodule E R.dualAnnihilator) from trivial)
  · have h := Subspace.finrank_add_finrank_dualAnnihilator_eq R
    have size : finrank E (Fin N → E)=N := by simp
    simp only [ls,List.length_ofFn]
    rw [size] at h
    omega

noncomputable def dualBasis : Probes N where
  list R := Classical.choose (hasBasisList F N R)
  vanish R := (Classical.choose_spec (hasBasisList F N R)).1
  complete R := (Classical.choose_spec (hasBasisList F N R)).2.1
  length_le R := (Classical.choose_spec (hasBasisList F N R)).2.2

def first (query : Probe N→Option W) : List (Probe N)→Option W × ℕ
  | [] => (none,0)
  | f::fs => match query f with
    | some w => (some w,1)
    | none => let t := first query fs; (t.1,t.2+1)

theorem first_spec (q : Probe N→Option W) (fs : List (Probe N)) :
    (first q fs).2≤fs.length ∧
    ((first q fs).1=none → ∀ f∈fs,q f=none) ∧
    (∀ w,(first q fs).1=some w → ∃ f∈fs,q f=some w) := by
  induction fs with
  | nil => simp [first]
  | cons f fs ih =>
    cases eq : q f with
    | some w => simp [first,eq]
    | none =>
      simp only [first,eq,List.length_cons,List.mem_cons]
      refine ⟨Nat.succ_le_succ ih.1,?_,?_⟩
      · rintro h g (rfl|mem)
        · exact eq
        · exact ih.2.1 h g mem
      · intro w ret
        obtain ⟨g,mem,res⟩ := ih.2.2 w ret
        exact ⟨g,Or.inr mem,res⟩

def grow (R : Space N) (x : V N) := R ⊔ span F {x}
theorem grows {L R : Space N} {row : W→V N} {q : Probe N→Option W} (h : Contract L row q)
    (inc : R≤L) {f : Probe N} (ann : f∈R.dualAnnihilator) {w : W} (yes : q f=some w) :
    R < grow R (row w) ∧ grow R (row w)≤L := by
  obtain ⟨ok,nz⟩ := h.violating f w yes
  have fresh : row w∉R := fun mem=>nz ((R.mem_dualAnnihilator f).mp ann _ mem)
  refine ⟨lt_of_le_of_ne le_sup_left (fun eq=>fresh (eq ▸ ?_)),sup_le inc ?_⟩
  · exact (show span F {row w} ≤ grow R (row w) from le_sup_right) (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    simpa using ok

structure Result (W : Type*) where
  witnesses : List W
  calls : ℕ

def loop (p : Probes N) (q : Probe N→Option W) (row : W→V N) :
    ℕ→Space N→Result W
  | 0,_ => ⟨[],0⟩
  | k+1,R =>
    let round := first q (p.list R)
    match round.1 with
    | none => ⟨[],round.2⟩
    | some w =>
      let next := loop p q row k (grow R (row w))
      ⟨w::next.witnesses,round.2+next.calls⟩

def collected (row : W→V N) (R : Space N) (ws : List W) :=
  ws.foldl (fun A w=>grow A (row w)) R

/-- Every emitted row is new relative to all rows accepted before it. -/
def Fresh (row : W→V N) (R : Space N) : List W→Prop
  | [] => True
  | w::ws => row w∉R ∧ Fresh row (grow R (row w)) ws

theorem loop_spec (p : Probes N) (L : Space N) (row : W→V N) (q : Probe N→Option W)
    (h : Contract L row q) (fuel : ℕ) (R : Space N) (inc : R≤L)
    (room : N ≤ finrank F R + fuel) :
    let t := loop p q row fuel R
    collected row R t.witnesses=L ∧ Fresh row R t.witnesses ∧
      t.witnesses.length≤fuel ∧ t.calls≤fuel*N := by
  induction fuel generalizing R with
  | zero =>
    have dim : finrank F (V N)=N := by simp [V]
    have hi := L.finrank_le
    rw [dim] at hi
    have equal : R=L := by
      by_contra ne
      have strict := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inc ne)
      omega
    simpa [loop,collected,Fresh] using equal
  | succ k ih =>
    obtain ⟨count,miss,hit⟩ := first_spec q (p.list R)
    have ct := count.trans (p.length_le R)
    cases res : (first q (p.list R)).1 with
    | none =>
      have equal := p.complete R L inc (fun f hf=>h.safe f (miss res f hf))
      simp only [loop,res,collected,List.foldl_nil,Fresh,List.length_nil]
      exact ⟨equal,trivial,Nat.zero_le _,ct.trans (by rw [Nat.succ_mul]; omega)⟩
    | some w =>
      obtain ⟨f,hf,out⟩ := hit w res
      have ann := p.vanish R f hf
      obtain ⟨strict,nextIncl⟩ := grows h inc ann out
      have bump := Submodule.finrank_lt_finrank_of_lt strict
      have nextRoom : N ≤ finrank F (grow R (row w))+k := by omega
      obtain ⟨answer,chain,updates,budget⟩ := ih _ nextIncl nextRoom
      have newRow : row w∉R := fun mem=>(h.violating f w out).2 ((R.mem_dualAnnihilator f).mp ann _ mem)
      simp only [loop,res,Fresh,List.length_cons,collected,List.foldl_cons]
      refine ⟨answer,⟨newRow,chain⟩,Nat.succ_le_succ updates,?_⟩
      rw [Nat.succ_mul]
      omega

theorem recover (L : Space N) (row : W→V N) (q : Probe N→Option W)
    (h : Contract L row q) (R : Space N) (inc : R≤L) :
    let t := loop dualBasis q row (N-finrank F R) R
    collected row R t.witnesses=L ∧ Fresh row R t.witnesses ∧
      t.witnesses.length≤N ∧ t.calls≤N*N := by
  obtain ⟨answer,chain,count,budget⟩ := loop_spec dualBasis L row q h
    (N-finrank F R) R inc (by omega)
  exact ⟨answer,chain,count.trans (Nat.sub_le _ _),
    budget.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))⟩

#print axioms recover
end ExactPlaneFirstSpaceRecovery
