import DDRawPins
import Q1DoubleOccurrenceSemantics
import Q0FactorSemantics

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable def andRegion (n : ℕ) (C : Circuit) (root : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = .and ∧ AndPath n C j (n+root)

theorem in_region {r j : ℕ} : j ∈ andRegion n C r ↔
    j < C.gates.length ∧ (gateAt C j).op = .and ∧ AndPath n C j (n+r) := by
  classical
  simp only [andRegion,Finset.mem_filter,Finset.mem_range]

theorem extend_and_path {i j w : ℕ} (left : AndPath n C i (n+j)) (right : AndPath n C j w) :
    AndPath n C i w := by
  induction right with
  | source => exact left
  | step _ b op pin ih => exact .step ih b op pin

theorem first_and_reader {g w : ℕ} (path : AndPath n C g w) :
    w = n+g ∨ ∃ k < C.gates.length, (gateAt C k).op = .and ∧ n+g ∈ (gateAt C k).inputs ∧
      AndPath n C k w := by
  induction path with
  | source => exact Or.inl rfl
  | @step v j prev hj op pin ih =>
    rcases ih with eq | ⟨k,hk,andk,rd,tail⟩
    · exact Or.inr ⟨j,hj,op,eq ▸ pin,.source⟩
    · exact Or.inr ⟨k,hk,andk,rd,.step tail hj op pin⟩

theorem root_mem_region {r : ℕ} (hr : r<C.gates.length) (hand : (gateAt C r).op=.and) :
    r ∈ andRegion n C r := in_region.mpr ⟨hr,hand,.source⟩

theorem region_used (ao : IsAO2 n C) (r : ℕ) :
    ∀ j ∈ (andRegion n C r).erase r, ∃ p ∈ pins (andRegion n C r), opnd C p.1 p.2 = n+j := by
  intro j hj
  obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
  rcases first_and_reader (in_region.mp mem).2.2 with eq | ⟨k,hk,op,pin,path⟩
  · exact (ne (by omega)).elim
  · have reg : k ∈ andRegion n C r := in_region.mpr ⟨hk,op,path⟩
    rcases Q0.reader_pin ao hk pin with e | e
    · exact ⟨(k,0),Finset.mem_product.mpr ⟨reg,Finset.mem_univ _⟩,e⟩
    · exact ⟨(k,1),Finset.mem_product.mpr ⟨reg,Finset.mem_univ _⟩,e⟩

theorem region_pin_mem (ao : IsAO2 n C) {r : ℕ} {p : ℕ × Fin 2}
    (hp : p ∈ occurrences n C (andRegion n C r)) :
    p.1 ∈ andRegion n C r ∧ opnd C p.1 p.2 ∈ (gateAt C p.1).inputs := by
  have mem := (Finset.mem_product.mp (Finset.mem_sdiff.mp hp).1).1
  have b := (in_region.mp mem).1
  obtain ⟨a,z,haz⟩ := List.length_eq_two.mp (ao.2.2 _ (S4183.S90.gateAt_mem b))
  refine ⟨mem,?_⟩
  rcases p with ⟨j,k⟩
  fin_cases k <;> simp_all [opnd]

theorem region_boundary_kind (ao : IsAO2 n C) {m r : ℕ} {p : ℕ × Fin 2}
    (hp : p ∈ occurrences n C (andRegion n C r)) :
    opnd C p.1 p.2 = n+m ∨ PlainWire n C m (opnd C p.1 p.2) := by
  let w := opnd C p.1 p.2
  have info := region_pin_mem ao hp
  obtain ⟨b,hand,path⟩ := in_region.mp info.1
  have lt := ao.2.1 _ b _ info.2
  by_cases hw : w<n
  · exact Or.inr (.inl hw)
  let k := w-n
  have eq : w=n+k := by dsimp [k]; omega
  have bk : k<C.gates.length := by dsimp [w] at eq; omega
  by_cases km : k=m
  · exact Or.inl (by simpa [km] using eq)
  rcases ao.1 _ (S4183.S90.gateAt_mem bk) with ak | ok
  · exfalso
    have parent : AndPath n C k (n+p.1) := .step .source b hand (eq ▸ info.2)
    have reg : k ∈ andRegion n C r := in_region.mpr ⟨bk,ak,extend_and_path parent path⟩
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,k,reg,eq⟩)
  · exact Or.inr (.inr ⟨k,bk,km,eq,ok⟩)

theorem region_wire_le {r j : ℕ} (ao : IsAO2 n C) (hj : j ∈ andRegion n C r) : j ≤ r := by
  have grow {i w : ℕ} (pth : AndPath n C i w) : n+i ≤ w := by
    induction pth with
    | source => omega
    | step _ b _ pin ih => exact ih.trans (Nat.le_of_lt (ao.2.1 _ b _ pin))
  have := grow (in_region.mp hj).2.2
  omega

theorem region_boundary_before {m r : ℕ} (ao : IsAO2 n C) (rm : r ≤ m) {p : ℕ × Fin 2}
    (hp : p ∈ occurrences n C (andRegion n C r)) : PlainWire n C m (opnd C p.1 p.2) := by
  rcases region_boundary_kind (m := m) ao hp with eq | yes
  · obtain ⟨jm,pin⟩ := region_pin_mem ao hp
    have := region_wire_le ao jm
    have := ao.2.1 _ (in_region.mp jm).1 _ pin
    omega
  · exact yes

theorem region_eval {r : ℕ} (ao : IsAO2 n C) (hr : r<C.gates.length) (hand : (gateAt C r).op=.and)
    (x : Fin n → Bool) : gateVal n C r x = true ↔
      ∀ p ∈ occurrences n C (andRegion n C r), W n C x (opnd C p.1 p.2) = true :=
  occurrence_semantics n C ao _ r (root_mem_region hr hand)
    (fun j h => ⟨(in_region.mp h).1,(in_region.mp h).2.1⟩) (region_used ao r) x

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
