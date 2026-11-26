import ThresholdOrIncidence
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction

def batchVertices (bs : List Block) := bs.filter (fun b => b.batch==1)

theorem batches_card (bs : List Block) : batchCount bs = (batchVertices bs).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have small : b.batch=0 ∨ b.batch=1 := by
      cases b with
      | meet => exact Or.inl rfl
      | group _ t => by_cases h : t.raws = [] <;> simp [Block.batch,h]
    rcases small with hz|ho
    · simp [batchCount,batchVertices,hz] at * <;> omega
    · simp [batchCount,batchVertices,ho] at * <;> omega

private theorem retained (bs : List Block) (seen : List Nat) (w : Nat) :
    w ∈ outputs bs seen ↔ w∈seen ∨ ∃ b∈bs, b.out=w := by
  induction bs generalizing seen with
  | nil => simp [outputs]
  | cons b bs ih =>
    rw [outputs,ih]
    constructor
    · rintro (h|⟨d,hd,eq⟩)
      · rcases List.mem_cons.mp h with eq|old
        · exact Or.inr ⟨b,by simp,eq.symm⟩
        · exact Or.inl old
      · exact Or.inr ⟨d,by simp [hd],eq⟩
    · rintro (old|⟨d,hd,eq⟩)
      · exact Or.inl (by simp [old])
      · rcases List.mem_cons.mp hd with same|other
        · subst d; exact Or.inl (by simp [eq])
        · exact Or.inr ⟨d,other,eq⟩

theorem observed_root {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) (obs : C.output=n+i.val) :
    C.output ∈ outputs (forest layout pin) [] := by
  have stop : T2OrPartition.next C n i=none := by
    unfold T2OrPartition.next
    split <;> simp [obs]
  have mem := mem_roots layout pin i stop
  exact (retained _ _ _).mpr (Or.inr ⟨_,mem,(makeBlock_out layout pin i).trans obs.symm⟩)

theorem physical_book {C : Circuit} {n : Nat} (layout : Layout C n)
    (reg : MeetsInternal layout) (pin : T2OrPartition.Id C → Nat)
    (twice : ∀ w<n, (T2OrPartition.readers C w).length=2)
    (obs : ∃ i : T2OrPartition.Id C, C.output=n+i.val) :
    let bs := forest layout pin
    Book C n [] bs ∧ (allGates bs).Nodup ∧ rawCount bs=2*n ∧
      batchCount bs=(batchVertices bs).length ∧ C.output ∈ outputs bs [] := by
  obtain ⟨i,hi⟩ := obs
  exact ⟨extracted_book layout reg pin,forest_nodup layout pin,raw_count_two layout reg pin twice,
    batches_card _,observed_root layout pin i hi⟩

theorem regular_pool {α : Type} {C : Circuit} {n m : Nat} (layout : Layout C n)
    (reg : MeetsInternal layout) (pin : T2OrPartition.Id C → Nat)
    (twice : ∀ w<n, (T2OrPartition.readers C w).length=2)
    (obs : ∃ i : T2OrPartition.Id C, C.output=n+i.val)
    (raw formal : α → List Bool) (src : ∀ a,(raw a).length=n) (dst : ∀ a,(formal a).length=m)
    (pins : ∀ b∈forest layout pin, b.RealPin C raw formal m) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (formal a) = C.eval (raw a)) ∧
      ors D.gates + 2*n ≤ ors C.gates + (batchVertices (forest layout pin)).length := by
  obtain ⟨book,nd,number,batches,observed⟩ := physical_book layout reg pin twice obs
  obtain ⟨D,mono,same,_,cost⟩ := abstract_groups raw formal n m src dst _ book pins observed nd
  exact ⟨D,mono,same,by simpa only [number,batches] using cost⟩

#print axioms regular_pool
#print axioms physical_book
end ThresholdOrExtraction
