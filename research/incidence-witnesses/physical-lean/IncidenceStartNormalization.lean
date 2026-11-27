import IncidenceOfficial401
namespace IncidenceStartNormalization
open SparseIncidence CircuitRewire

structure Circuit (n : ℕ) where
  size : ℕ
  output : ℕ
  code : ℕ → Gate
  wire : ℕ → Set (Input n)
  output_lt : output<n+n+size
  earlier : ∀ j<size, (code j).left<n+n+j ∧ (code j).right<n+n+j
  law : ∀ j<size, wire (n+n+j)=(code j).eval wire
  inputs : ∀ i : Fin n, wire i.val={z | z.1 i=true} ∧ wire (n+i.val)={z | z.2 i=true}

def flags {n} (C : Circuit n) (I : Fin n→Fin n→Prop) :=
  ∀ p l, I p l → (single p,single l)∈C.wire C.output

def negatives {n} (C : Circuit n) (I : Fin n→Fin n→Prop) (pCap lCap : ℕ) :=
  ∀ a b : Fin n→Bool, Fintype.card {p // a p=true} ≤ pCap →
    Fintype.card {l // b l=true} ≤ lCap → (∀ p l, a p=true → b l=true → ¬I p l) →
    (a,b) ∉ C.wire C.output

def binary {n} (C : Circuit n) := ∀ g<C.size, (C.code g).op=.join ∨ (C.code g).op=.meet

/-- Ports are literal operands of the binary normalization. Duplicate inputs count twice. -/
def uses {n} (C : Circuit n) (i : ℕ) : ℕ :=
  ((List.range C.size).map fun g =>
    (if (C.code g).left=i then 1 else 0) + (if (C.code g).right=i then 1 else 0)).sum

def soleCount {n} (C : Circuit n) (offset : ℕ) :=
  ((Finset.range n).filter (fun i => uses C (offset+i)=1)).card

def soleAnd {n} (C : Circuit n) (offset : ℕ) :=
  ∀ i<n, uses C (offset+i)=1 →
    ∀ g<C.size, (C.code g).left=offset+i ∨ (C.code g).right=offset+i → (C.code g).op=.meet

/-- Result needed from binary preprocessing followed by the line-only hoist. -/
structure LineStage {n} (I : Fin n→Fin n→Prop) (input line : Circuit n) : Prop where
  budget : line.size≤input.size
  ops : binary line
  one : flags line I
  sparse : negatives line I n 401
  and_first : soleAnd line n

/-- Execute the point-only hoist on this very line-normalized circuit. -/
structure BilateralStage {n} (I : Fin n→Fin n→Prop) (line both : Circuit n) : Prop where
  budget : both.size≤line.size
  ops : binary both
  one : flags both I
  sparse : negatives both I 401 400
  and_point : soleAnd both 0
  and_line : soleAnd both n
  preserve : ∀ i<n, uses both (n+i)=uses line (n+i)

theorem unchanged_line_count {n} {I : Fin n→Fin n→Prop} {line both : Circuit n}
    (h : BilateralStage I line both) : soleCount both n=soleCount line n := by
  unfold soleCount
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_range]
  constructor <;> rintro ⟨hi,hits⟩
  · exact ⟨hi,by simpa only [← h.preserve i hi] using hits⟩
  · exact ⟨hi,by simpa only [h.preserve i hi] using hits⟩

theorem round_start {n} {I : Fin n→Fin n→Prop} {input line both : Circuit n}
    (h₁ : LineStage I input line) (h₂ : BilateralStage I line both)
    (lineCensus : soleCount line n≤3382) (pointCensus : soleCount both 0≤6461) :
    both.size≤input.size ∧ flags both I ∧ negatives both I 3 3 ∧
      binary both ∧ soleAnd both 0 ∧ soleAnd both n ∧ soleCount both 0+soleCount both n≤9843 := by
  refine ⟨h₂.budget.trans h₁.budget,h₂.one,?_,h₂.ops,h₂.and_point,h₂.and_line,?_⟩
  · intro a b ha hb hi
    exact h₂.sparse a b (by omega) (by omega) hi
  · rw [unchanged_line_count h₂]
    omega
/-- The input-domain hypothesis is obtained from the posted circuit itself. -/
theorem posted_negative {n} (I : Fin n→Fin n→Prop) [DecidableRel I] (C : Circuit n)
    (marked : Finset ℕ) (steps : IncidenceOfficialScalar.PostedSteps C.size marked C.wire)
    (pos : flags C I) (neg : ∀ b : Fin n→Bool, Fintype.card {l // b l=true}≤401 →
      (outside I b,b) ∉ C.wire C.output) : negatives C I n 401 := by
  obtain ⟨_,_,_,slices⟩ := IncidenceOfficialScalar.translate I marked C.wire C.output_lt C.inputs steps pos neg
  intro a b _ hb hi hit
  obtain ⟨p,l,hp,hl,flag⟩ := (slices a b hb).mp hit
  exact hi p l hp hl flag

/-- Numerical end of the line experiment. The products include the 3106
eligible pairs per charged owner. Hypotheses express failure of either pin schedule. -/
theorem line_census {H edited charged : ℕ} (split : H=edited+charged)
    (pin52 : 64803606*edited+64766312*charged≤3382*64803606)
    (pin53 : 64803606*edited+66011818*charged≤3386*64803606) : H≤3382 := by
  by_cases small : charged≤1737 <;> omega

/-- Component slots and the edited-owner budget are charged in separate
hypothetical experiments on the point-stage circuit. -/
theorem point_census {H edited charged : ℕ} (split : H=edited+charged)
    (slots : 199*charged≤646424) (edit : edited≤3213) : H≤6461 := by omega

/-- These are explicit proof obligations for the initial normalization, not axioms. -/
def InitialConstruction {n} (I : Fin n→Fin n→Prop) : Prop :=
  ∀ C : Circuit n, C.size≤646424 → flags C I → negatives C I n 401 →
    ∃ line both : Circuit n, LineStage I C line ∧ BilateralStage I line both ∧
      soleCount line n≤3382 ∧ soleCount both 0≤6461

#print axioms line_census
#print axioms point_census
#print axioms round_start
#print axioms posted_negative
end IncidenceStartNormalization
