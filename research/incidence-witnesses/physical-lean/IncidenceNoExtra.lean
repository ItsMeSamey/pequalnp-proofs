import IncidencePhysicalZeroFlow
import IncidenceDenseSignature

namespace IncidenceNoExtra
open CircuitRewire IncidenceOperandLedger
open scoped BigOperators

/-- A reserved gate index may depend on the deleted owner; injectivity prevents
two owners from consuming the same unit. Every deleted nonowner has two uses. -/
theorem raw_floor (D S : Finset ℕ) (owner : ℕ → ℕ) (f : ℕ → ℤ)
    (sub : S ⊆ D) (inj : Set.InjOn owner (↑S : Set ℕ))
    (sole : ∀ i∈S,1≤f i) (other : ∀ i∈D\S,2≤f i) :
    2*(D.card : ℤ)-((S.image owner).card : ℤ) ≤ ∑ i∈D,f i := by
  classical
  have size := Finset.card_sdiff_add_card_eq_card sub
  have equal := Finset.card_image_of_injOn inj
  have first := Finset.sum_le_sum sole
  have rest := Finset.sum_le_sum other
  have part := Finset.sum_sdiff (f:=f) sub
  simp at first rest
  omega

/-- Dense flag on each raw is exactly deletion-set membership. -/
theorem raw_sum (D : Finset ℕ) (m : ℕ) (z : ℕ → Bool) (f : ℕ → ℤ)
    (sub : D ⊆ Finset.range m) (flag : ∀ i<m, z i=true ↔ i∈D) :
    (∑ i∈Finset.range m,f i * bit (z i)) = ∑ i∈D,f i := by
  classical
  calc
    _ = ∑ i∈Finset.range m, if i∈D then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have e := flag i (Finset.mem_range.mp hi)
      cases hz : z i <;> simp_all [bit]
    _ = _ := by
      rw [← Finset.sum_filter]
      have eq : (Finset.range m).filter (·∈D) = D := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨And.right,fun h=>⟨sub h,h⟩⟩
      rw [eq]

/-- Reserve one distinct one-zero AND per deficient deleted input. The raw-floor
hypothesis permits extra reads elsewhere. A dead output with no reader must
have zero flag false, as required by the internal nonnegativity hypothesis. -/
theorem vanish (m s : ℕ) (g : ℕ → Gate) (z : ℕ → Bool) (P : Finset ℕ)
    (b loss : ℤ) (inside : P ⊆ Finset.range s)
    (reserved : ∀ j ∈ P, oneAnd z (g j)=1)
    (rawFloor : b-(P.card : ℤ) ≤ ∑ i∈Finset.range m,fan g s i * bit (z i))
    (nonneg : ∀ j<s, 0 ≤ (fan g s (m+j)-1)*bit (z (m+j)))
    (ledger : loss=(∑ i∈Finset.range m,fan g s i * bit (z i)) +
      (∑ j∈Finset.range s,(fan g s (m+j)-1)*bit (z (m+j))) +
      ∑ j∈Finset.range s,oneAnd z (g j))
    (cap : loss≤b) :
    (∀ j<s, j∉P → oneAnd z (g j)=0) ∧
    (∀ j<s, 2≤fan g s (m+j) → z (m+j)=false) := by
  classical
  let W := Finset.range s
  let h := fun j => (fan g s (m+j)-1)*bit (z (m+j))
  have hn : ∀ j∈W, 0≤h j := fun j hj => nonneg j (Finset.mem_range.mp hj)
  have an (j : ℕ) : 0≤oneAnd z (g j) := by unfold oneAnd; split <;> omega
  have rep : (∑ j∈P,oneAnd z (g j))=(P.card : ℤ) := by
    rw [Finset.sum_congr rfl reserved]; simp
  have partition := Finset.sum_sdiff (f:=fun j=>oneAnd z (g j)) inside
  have ih0 : 0 ≤ ∑ j∈W,h j := Finset.sum_nonneg hn
  have ah0 : 0 ≤ ∑ j∈W\P,oneAnd z (g j) := Finset.sum_nonneg (fun j _=>an j)
  change loss=_+(∑ j∈W,h j)+_ at ledger
  change (∑ j∈W\P,oneAnd z (g j)) + _ = _ at partition
  constructor
  · intro j js np
    have one := Finset.single_le_sum (f:=fun i=>oneAnd z (g i)) (fun i _=>an i)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr js,np⟩ : j∈W\P)
    have := an j
    omega
  · intro j js shared
    have one := Finset.single_le_sum hn (Finset.mem_range.mpr js : j∈W)
    cases e : z (m+j) with
    | false => rfl
    | true =>
      have pos : 1≤h j := by simpa [h,e,bit] using (show 1≤fan g s (m+j)-1 by omega)
      omega

/-- Direct literal-compiler specialization. The only payback witnesses refer to
input uses, assigned physical row indices, and the flags of that actual run. -/
theorem literal (m n s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (z : ℕ→Bool)
    (input : ∀ i<m,(init i).isNone=z i)
    (order : ∀ j<s,IncidenceZeroRestriction.OrderedBinary (g j) (m+j))
    (step : ∀ j<s,z (m+j)=IncidenceZeroRestriction.deadOut (g j).op (z (g j).left) (z (g j).right))
    (D S : Finset ℕ) (owner : ℕ→ℕ) (sub : S⊆D) (rangeD : D⊆Finset.range m)
    (flag : ∀ i<m,z i=true ↔ i∈D) (unique : Set.InjOn owner (↑S : Set ℕ))
    (sole : ∀ i∈S,1≤fan g s i) (other : ∀ i∈D\S,2≤fan g s i)
    (valid : S.image owner ⊆ Finset.range s)
    (book : ∀ j∈S.image owner,oneAnd z (g j)=1)
    (live : ∀ j<s,0≤(fan g s (m+j)-1)*bit (z (m+j)))
    (cap : (s : ℤ)-(IncidenceZeroRestriction.compileLiteral m n g init s).size≤2*(D.card : ℤ)) :
    (∀ j<s,j∉S.image owner → oneAnd z (g j)=0) ∧
    (∀ j<s,2≤fan g s (m+j) → z (m+j)=false) := by
  apply vanish m s g z (S.image owner) (2*(D.card : ℤ)) _ valid book _ live
    (IncidenceZeroRestriction.savings m n s g init z input order step) cap
  rw [raw_sum D m z (fan g s) rangeD flag]
  exact raw_floor D S owner (fan g s) sub unique sole other

/-- A non-designated AND may copy either operand on every tested mask. -/
theorem equal_flags (g : Gate) (z : ℕ→Bool) (meet : g.op=.meet)
    (zero : oneAnd z g=0) : z g.left=z g.right := by
  by_contra ne
  simp [oneAnd,meet,ne] at zero

/-- At a fixed physical AND the selected copy wire is independent of the deletion
mask. A designated owner is normalized to the left or right pin once. -/
theorem copy_wire {α : Type*} [DecidableEq α] (t : ℕ) (g : Gate)
    (z : Finset α → ℕ → Bool) (w : ℕ)
    (eval : ∀ D, D.card≤t → z D w = (z D g.left || z D g.right))
    (mode : (∀ D, D.card≤t → z D g.left=z D g.right) ∨
       (∀ D,D.card≤t → z D g.right=false) ∨
       (∀ D,D.card≤t → z D g.left=false)) :
    ∃ u, (u=g.left ∨ u=g.right) ∧ ∀ D,D.card≤t → z D w=z D u := by
  rcases mode with eq | right | left
  · refine ⟨g.left,Or.inl rfl,fun D hd=>?_⟩
    rw [eval D hd,eq D hd]
    cases z D g.right <;> rfl
  · exact ⟨g.left,Or.inl rfl,fun D hd=>by simp [eval D hd,right D hd]⟩
  · exact ⟨g.right,Or.inr rfl,fun D hd=>by simp [eval D hd,left D hd]⟩

/-- The distinguishing dense mask for a finite signature excludes branching.
The assertion also covers an empty signature when admitted. -/
theorem no_small_branch {α : Type*} [DecidableEq α] (t : ℕ) (A : Finset α)
    (small : A.card≤t) (z : Finset α → Bool)
    (meaning : ∀ D,D.card≤t → (z D=false ↔ IncidenceDenseSignature.high (some A) D))
    (shared : ∀ D,D.card≤t → z D=false) : False :=
  (meaning A small).mp (shared A small) (fun _ h=>h)

end IncidenceNoExtra
