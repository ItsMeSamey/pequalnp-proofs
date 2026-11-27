import IncidencePinnedCube

namespace IncidenceZeroRestriction
open CircuitRewire
/-- Evaluate the physical rows in order. Only predecessor values are read. -/
def execute {Z : Type*} (n : Nat) (code : Nat→Gate) (base : Nat→Set Z) : Nat→Nat→Set Z
  | 0 => base
  | k+1 =>
    let old := execute n code base k
    put old (n+k) ((code k).eval old)

theorem execute_unique {Z : Type*} (n s : Nat) (code : Nat→Gate) (base Y : Nat→Set Z)
    (ord : ∀ i<s,(code i).left<n+i ∧ (code i).right<n+i)
    (src : ∀ i<n,Y i=base i) (sem : ∀ i<s,Y (n+i)=(code i).eval Y) :
    ∀ j<n+s,execute n code base s j=Y j := by
  induction s with
  | zero => intro j hj; exact (src j (by omega)).symm
  | succ a ih =>
    have prev := ih (fun i hi=>ord i (by omega)) (fun i hi=>sem i (by omega))
    intro j hj
    by_cases e : j=n+a
    · subst j
      obtain ⟨l,r⟩ := ord a (by omega)
      simp only [execute,put,if_true,Gate.eval,prev _ l,prev _ r,sem a (by omega)]
    · simpa [execute,put,e] using prev j (by omega)

theorem execute_old {Z : Type*} (n s : Nat) (code : Nat→Gate) (base : Nat→Set Z)
    (a : Nat) (ha : a≤s) (j : Nat) (hj : j<n+a) :
    execute n code base s j=execute n code base a j := by
  induction s,ha using Nat.le_induction with
  | base => rfl
  | succ k hk ih => simp [execute,put,show j≠n+k by omega,ih]

theorem run_inputs {Z : Type*} (n s : Nat) (code : Nat→Gate) (base : Nat→Set Z)
    (j : Nat) (hj : j<n) : execute n code base s j=base j :=
  execute_old n s code base 0 (Nat.zero_le _) j (by omega)

theorem run_gate {Z : Type*} (n s : Nat) (code : Nat→Gate) (base : Nat→Set Z)
    (j : Nat) (hj : j<s) (l : (code j).left<n+j) (r : (code j).right<n+j) :
    execute n code base s (n+j)=(code j).eval (execute n code base s) := by
  rw [execute_old n s code base (j+1) (by omega) (n+j) (by omega)]
  simp only [execute,put,if_true,Gate.eval,
    execute_old n s code base j (by omega) _ l,execute_old n s code base j (by omega) _ r]

theorem native (m n s o : Nat) (raw : Nat→Gate) (init : Nat→Option Nat)
    (bound : ∀ i<m,Below n (init i)) (order : ∀ i<s,OrderedBinary (raw i) (m+i))
    (out : o<m+s) (yes : ∃ z,liftInputs init z∈execute m raw coordinate s o) :
    let p := compileLiteral m n raw init s
    let X := execute m raw coordinate s
    let low := fun i=>liftInputs init ⁻¹' X i
    p.size+charged raw (zeroAt low (fun _=>true)) s=s ∧
    ∃ j<n+p.size,p.refs o=some j ∧ ∀ z,
      z∈execute n p.code coordinate p.size j ↔ liftInputs init z∈X o := by
  let X := execute m raw coordinate s
  let p := compileLiteral m n raw init s
  obtain ⟨count,ord,j,hj,ref,Y,base,ev,eq⟩ := all_masks m n s o raw init X bound
    (fun i hi=>run_inputs m s raw coordinate i hi) order (fun i hi=>run_gate m s raw coordinate i hi (order i hi).1
      (order i hi).2.1) out yes
  have actual := execute_unique n p.size p.code coordinate Y (fun i hi=>
    ⟨(ord i hi).1,(ord i hi).2.1⟩) base ev j hj
  exact ⟨count,j,hj,ref,fun z=>by rw [actual]; exact eq z⟩
#print axioms native
end IncidenceZeroRestriction
