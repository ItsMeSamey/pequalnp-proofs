import T2AuxChain
import T2CubeDeletion
import T2RawTopology
import T2NamedProducer
import T2SoleAndDirty

namespace T2SoleAndMinor
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2PhysicalMaximum
open T2SoleOrSplice T2CubeDeletion T2RawTopology T2NamedProducer T2SoleAndDirty

theorem source_eq (gs : List Raw) (out : Nat) : source gs out = ⟨gs.map native,out⟩ := by
  unfold source
  congr 1 <;> apply List.map_congr_left <;> intro r _ <;> obtain ⟨o,x,y⟩ := r <;> rfl

theorem named_minor {m : Nat} (two : 2≤m) (i : Fin (m+1)) (out : Nat)
    (a b c d : List Raw) (p : Raw) (x y u v : Nat) (oh : Op)
    (raw : x=i.val ∨ y=i.val)
    (edge : u=(m+1)+(a ++ p::b).length ∨ v=(m+1)+(a ++ p::b).length)
    (ok : RawValid (m+1) (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))))
    (obs : out<(m+1)+(a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))).length)
    (hc : Computes (m+1) (source (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))) out))
    (maximum : ∀ s : Finset (Fin m), s ≠ ∅ →
      computed a p (vector (embedded i s)) = true) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧
      D.size+3 ≤ (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))).length := by
  classical
  let post := b ++ (.and,x,y)::(c ++ (oh,u,v)::d)
  let orig := a ++ p::post
  let prog := rawEdited a post p.1
  let input := fun s : Finset (Fin m) => vector (embedded i s)
  let one : Finset (Fin m) := {⟨0,by omega⟩}
  have no (s : Finset (Fin m)) (tiny : s.card<2) :
      Circuit.eval ⟨orig.map native,out⟩ (input s)=false := by
    have hh := hc (embedded i s)
    rw [source_eq] at hh
    cases e : Circuit.eval ⟨orig.map native,out⟩ (input s) with
    | false => rfl
    | true => have h := hh.mp e; rw [embedded_card] at h; omega
  have same (s : Finset (Fin m)) : (source prog (out+1)).eval (true::input s) =
      (source orig out).eval (input s) := by
    rw [source_eq,source_eq]
    apply maximum_override input ∅ one a post p out
      (vector_le (by simp [embedded])) (by simp [one]) maximum
        (no ∅ (by simp)) (no one (by simp [one]))
  have on := correct_on_override i (source orig out) prog (out+1) hc same
  have len : (tags true i).length = (m+1)+1 := by rw [tags_len]; simp; omega
  have sz : prog.length = orig.length := by simp [prog,orig,rawEdited]
  have valid : Valid (tags true i).length (annotate prog (tags true i)) := by
    rw [annotate_valid_iff,len]
    exact rawEdited_valid a post p _ ok
  have bound : out+1 < (tags true i).length + (annotate prog (tags true i)).length := by
    change out < (m+1)+orig.length at obs
    rw [len,annotate_len,sz]; omega
  have charge : 3≤closedCount prog (tags true i) := by
    apply T2AuxChain.debit (m+1) i.val _ a b c d p x y u v oh len
    · rfl
    · exact i.isLt
    · simpa [pinnedIndex,Nat.add_comm] using closed true i
    · exact raw
    · exact edge
  obtain ⟨D,mono,rep,price⟩ := closed_deletion true i prog (out+1) 3 two on valid bound charge
  exact ⟨D,mono,rep,sz ▸ price⟩

#print axioms named_minor
end T2SoleAndMinor
