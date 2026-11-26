import TightPhysicalSupport
import Mathlib.Data.List.Nodup

namespace OnePerShore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

inductive Formula where
  | atom (i : ℕ)
  | node (isAnd : Bool) (left right : Formula)

def Formula.leaves : Formula → List ℕ
  | .atom i => [i]
  | .node _ l r => l.leaves ++ r.leaves

def Formula.eval (x : ℕ → Bool) : Formula → Bool
  | .atom i => x i
  | .node op l r => if op then l.eval x && r.eval x else l.eval x || r.eval x

def Formula.bind (k : ℕ → Formula) : Formula → Formula
  | .atom i => k i
  | .node op l r => .node op (l.bind k) (r.bind k)

theorem Formula.bind_leaves (t : Formula) (k : ℕ → Formula) :
    (t.bind k).leaves = t.leaves.flatMap (fun i => (k i).leaves) := by
  induction t <;> simp_all [Formula.bind, Formula.leaves, List.flatMap_append]

theorem Formula.bind_eval (t : Formula) (k : ℕ → Formula) (x : ℕ → Bool) :
    (t.bind k).eval x = t.eval (fun i => (k i).eval x) := by
  induction t <;> simp_all [Formula.bind, Formula.eval]

private theorem two_inputs {l : List ℕ} (h : l.length = 2) : ∃ a b, l = [a,b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t =>
      cases t with
      | nil => exact ⟨_,_,rfl⟩
      | cons c t => simp at h

theorem formula_of_sweep (gs : List Gate) (n o : ℕ)
    (legal : Monotone2 ⟨gs,o⟩) (sweep : freshBinarySweep gs n o) :
    ∃ t : Formula, t.leaves.Nodup ∧ t.leaves.toFinset = live gs n o ∧
      ∀ x : List Bool, x.length = n →
        t.eval (fun i => x.getD i false) = (Circuit.mk gs o).eval x := by
  induction gs generalizing n with
  | nil =>
    change o < n at sweep
    exact ⟨.atom o, by simp [Formula.leaves], by simp [Formula.leaves, live, sweep],
      fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨used, len, distinct, earlier, fresh, tail⟩ := sweep
    obtain ⟨a,b,hargs⟩ := two_inputs len
    have hab : a ≠ b := by simpa [hargs] using distinct
    obtain ⟨t, nd, support, semantics⟩ :=
      ih (n+1) (fun k hk => legal k (List.mem_cons_of_mem _ hk)) tail
    let op := match g.op with | .and => true | _ => false
    let k (i : ℕ) : Formula := if i=n then .node op (.atom a) (.atom b) else .atom i
    have lk (i : ℕ) : (k i).leaves = if i=n then [a,b] else [i] := by
      by_cases h : i=n <;> simp [k,h,Formula.leaves]
    have away (i : ℕ) (hi : i ∈ t.leaves) (hn : i ≠ n) : i ≠ a ∧ i ≠ b := by
      have hs : i ∈ (live gs (n+1) o).erase n :=
        Finset.mem_erase.mpr ⟨hn, support ▸ List.mem_toFinset.mpr hi⟩
      have no := Finset.disjoint_left.mp fresh hs
      constructor <;> rintro rfl <;> exact no (by simp [hargs])
    refine ⟨t.bind k, ?_, ?_, ?_⟩
    · rw [Formula.bind_leaves, List.nodup_flatMap]
      refine ⟨fun i _ => ?_, nd.imp_of_mem ?_⟩
      · by_cases h : i=n <;> simp [lk,h,hab]
      · intro i j hi hj hij
        change List.Disjoint (k i).leaves (k j).leaves
        rw [lk,lk]
        by_cases hin : i=n <;> by_cases hjn : j=n
        · exact (hij (hin.trans hjn.symm)).elim
        · obtain ⟨na,nb⟩ := away j hj hjn
          simp [hin,hjn, na, nb]
        · obtain ⟨na,nb⟩ := away i hi hin
          simp [hin,hjn, na, nb]
        · simp [hin,hjn,Ne.symm hij]
    · have na := earlier a (by simp [hargs])
      have nb := earlier b (by simp [hargs])
      ext z
      simp only [Formula.bind_leaves, List.mem_toFinset, List.mem_flatMap]
      rw [live, ite_eq_left used]
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, hargs, List.mem_toFinset,
        List.mem_cons, List.not_mem_nil, or_false]
      have hmem (i : ℕ) : i ∈ t.leaves ↔ i ∈ live gs (n+1) o := by
        rw [←support, List.mem_toFinset]
      constructor
      · rintro ⟨i,hi,hz⟩
        by_cases e : i=n
        · subst i; simp [lk] at hz; exact Or.inr ⟨hz, by rcases hz with rfl|rfl <;> assumption⟩
        · simp [lk,e] at hz; subst z; exact Or.inl ⟨e,(hmem _).mp hi⟩
      · rintro (⟨hn,hz⟩|⟨hz,_⟩)
        · exact ⟨z,(hmem _).mpr hz,by simp [lk,hn]⟩
        · exact ⟨n,(hmem _).mpr used,by simpa [lk] using hz⟩
    · intro x hx
      rw [Formula.bind_eval]
      change _ = (Circuit.mk gs o).eval (advance g x)
      rw [←semantics (advance g x) (by simp [advance,hx])]
      congr 1
      funext i
      by_cases eq : i=n
      · subst i
        rw [show (advance g x).getD n false = _ by simpa only [hx] using getD_advance_eq g x]
        have hop : g.op = .and ∨ g.op = .or := (legal g (List.mem_cons_self ..)).1
        rcases hop with e|e <;>
          simp [k, op, e, hargs, Formula.eval, GateOp.eval]
      · by_cases small : i<n
        · simp only [k, if_neg eq, Formula.eval]
          exact (getD_advance_lt g x i (by omega)).symm
        · have big : (advance g x).length ≤ i := by simp [advance,hx]; omega
          simp only [k, if_neg eq, Formula.eval]
          rw [getD_missing big, getD_missing (by omega : x.length ≤ i)]

theorem formula_of_tight_circuit {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C)
    (positive : 0 < charged A) (cost : C.size ≤ charged A - 1) :
    ∃ t : Formula, t.leaves.Nodup ∧ t.leaves.toFinset = live C.gates (n+m) C.output ∧
      ∀ x : List Bool, x.length = n+m →
        t.eval (fun i => x.getD i false) = C.eval x := by
  exact formula_of_sweep C.gates (n+m) C.output legal
    (tight_physical_sweep legal rep positive cost).2.2

end OnePerShore
