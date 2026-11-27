import IncidenceHoistPrune
import IncidenceHoistReaders
namespace IncidencePinCompact
open CircuitRewire SparseIncidence IncidenceStartNormalization IncidenceHoistPrune

def addr (base m : Nat) (raw : Nat→Fin m) (w : Nat) : Nat :=
  if w<base then (raw w).val else m+(w-base)

def gates {n m} (C : Circuit n) (raw : Nat→Fin m) (j : Nat) : Gate :=
  ⟨(C.code j).op,addr (n+n) m raw (C.code j).left,addr (n+n) m raw (C.code j).right⟩

def masks {n m : Nat} (raw : Nat→Fin m) (A : Finset (Fin m)) : Input n :=
  (fun p=>decide (raw p.val∈A),fun l=>decide (raw (n+l.val)∈A))

def X {n m} (C : Circuit n) (raw : Nat→Fin m) (w : Nat) : Set (Finset (Fin m)) :=
  if h : w<m then {A | ⟨w,h⟩∈A}
  else (masks raw) ⁻¹' (C.wire (n+n+(w-m)))

theorem raw_wire {n m} (C : Circuit n) (raw : Nat→Fin m) (i : Fin m) :
    X C raw i.val={A | i∈A} := by simp [X,i.isLt]

theorem address_gate (base m : Nat) (raw : Nat→Fin m) (j : Nat) :
    addr base m raw (base+j)=m+j := by simp [addr]

theorem address_lt (base m : Nat) (raw : Nat→Fin m) (j i : Nat) (h : i<base+j) :
    addr base m raw i<m+j := by
  unfold addr
  split
  · have := (raw i).isLt; omega
  · omega

theorem transferred {n m} (C : Circuit n) (raw : Nat→Fin m) (w : Nat) :
    X C raw (addr (n+n) m raw w)=(masks raw) ⁻¹' (C.wire w) := by
  by_cases oldRaw : w<n+n
  · rw [addr,if_pos oldRaw,raw_wire]
    by_cases left : w<n
    · rw [(C.inputs ⟨w,left⟩).1]
      ext A
      simp [masks]
    · let l : Fin n := ⟨w-n,by omega⟩
      have eq : n+l.val=w := by dsimp [l]; omega
      rw [←eq,(C.inputs l).2]
      ext A
      simp [masks]
  · have eq : n+n+(w-(n+n))=w := by omega
    simp [addr,X,oldRaw,eq]

theorem ordered {n m} (C : Circuit n) (raw : Nat→Fin m) (j : Nat) (h : j<C.size) :
    (gates C raw j).left<m+j ∧ (gates C raw j).right<m+j := by
  exact ⟨address_lt _ _ _ _ _ (C.earlier j h).1,address_lt _ _ _ _ _ (C.earlier j h).2⟩

theorem law {n m} (C : Circuit n) (raw : Nat→Fin m) (j : Nat) (h : j<C.size) :
    X C raw (m+j)=(gates C raw j).eval (X C raw) := by
  rw [←address_gate (n+n) m raw j, transferred,C.law j h]
  change _=(C.code j).op.eval (X C raw (addr (n+n) m raw (C.code j).left))
    (X C raw (addr (n+n) m raw (C.code j).right))
  rw [transferred,transferred]
  cases o : (C.code j).op <;> simp [Gate.eval,o,Op.eval]

theorem output {n m} (C : Circuit n) (raw : Nat→Fin m) :
    X C raw (addr (n+n) m raw C.output)=(masks raw) ⁻¹' (C.wire C.output) :=
  transferred C raw _

theorem physical_gate_reader {n m} (C : Circuit n) (raw : Nat→Fin m) (live : Live C)
    (j : Nat) (hj : j<C.size) :
    m+j=addr (n+n) m raw C.output ∨ ∃k<C.size,
      (gates C raw k).left=m+j ∨ (gates C raw k).right=m+j := by
  have h := live j hj
  generalize index : n+n+j=w at h
  cases h with
  | output =>
    exact Or.inl ((address_gate (n+n) m raw j).symm.trans (congrArg (addr (n+n) m raw) index))
  | left k hk _ =>
    exact Or.inr ⟨k,hk,Or.inl ((congrArg (addr (n+n) m raw) index.symm).trans (address_gate ..))⟩
  | right k hk _ =>
    exact Or.inr ⟨k,hk,Or.inr ((congrArg (addr (n+n) m raw) index.symm).trans (address_gate ..))⟩

#print axioms law
#print axioms physical_gate_reader
end IncidencePinCompact
