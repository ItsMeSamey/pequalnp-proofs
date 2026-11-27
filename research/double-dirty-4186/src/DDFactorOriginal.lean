import DDFactorCone
import Q0FactorJoin
import Q0Aggregation
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
private theorem factorPriceBound {n : ℕ} (s : Layout n) (r : Row) : price s r ≤ 1 := by
  unfold price
  split
  · decide
  · cases readPin s r.left <;> cases readPin s r.right <;> simp [andCost]

theorem factorPaidFree {n : ℕ} (C : Circuit) (cuts : Cuts) (free : Finset ℕ)
    (isFree : ∀ i ∈ free, price (layout n C cuts i) (projectedRow n C cuts i) = 0)
    (k : ℕ) :
    expense (seed n) (rows n C cuts k) + ((Finset.range k).filter (· ∈ free)).card ≤ k := by
  induction k with
  | zero => simp [rows,expense]
  | succ k ih =>
    rw [expense_succ,Finset.range_add_one,Finset.filter_insert]
    by_cases hf : k ∈ free
    · simp [hf,isFree _ hf]; omega
    · have := factorPriceBound (layout n C cuts k) (projectedRow n C cuts k)
      simp [hf]; omega

theorem original_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (ao : IsAO2 n C) (dirty : ¬ BelowF G C g) :
    expense (seed n) (rows n C (factorCuts n C (orT G C) g) C.size) +
      (readers n C g).card + (orT G C).card ≤ C.size := by
  classical
  let R := readers n C g
  let T := orT G C
  let p := factorCuts n C T g
  have dis : Disjoint R T := Finset.disjoint_left.mpr (by
    intro r hr ht
    obtain ⟨bound,pin⟩ := Finset.mem_filter.mp hr
    obtain ⟨_,hop,below⟩ := Finset.mem_filter.mp ht
    have hlt := Finset.mem_range.mp bound
    apply dirty
    intro x hx
    exact below x (Q0ReaderDeps.S90.orStep_up (x:=List.ofFn x) (by simp)
      (.single ⟨r,hlt,rfl,hop,pin,ao.2.1 r hlt _ pin⟩) hx))
  have free (j : ℕ) (hj : j ∈ R ∪ T) : price (layout n C p j) (projectedRow n C p j) = 0 := by
    rcases Finset.mem_union.mp hj with rd | clean
    · obtain ⟨bound,pin⟩ := Finset.mem_filter.mp rd
      have lt := ao.2.1 j (Finset.mem_range.mp bound) _ pin
      rcases Q0.reader_pin ao (Finset.mem_range.mp bound) pin with a | b
      · apply price_zero_of_bypass C p (by omega : g < j) 0 _ a
        simp [p,factorCuts,a]
      · apply price_zero_of_bypass C p (by omega : g < j) 1 _ b
        simp [p,factorCuts,b]
    · simp [p,factorCuts,price,projectedRow,clean]
  have sub : R ∪ T ⊆ Finset.range C.size := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have whole : (Finset.range C.size).filter (· ∈ R ∪ T) = R ∪ T := by
    ext j
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨sub h,h⟩⟩
  have h := factorPaidFree C p (R ∪ T) free C.size
  rw [whole,Finset.card_union_of_disjoint dis] at h
  simpa only [Nat.add_assoc] using h

theorem dominated_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (bound : g < C.size) (dirty : ¬ BelowF G C g)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (live : ∃ t ∈ tops G C, Influence n C g (n+t))
    (dom : ∀ t ∈ tops G C, Influence n C g (n+t) → ∀ x, gateVal n C t x = true → gateVal n C g x = true) :
    (readers n C g).card ≤ 1 := by
  classical
  let cuts := factorCuts n C (orT G C) g
  let slot := fun t => physicalSlot n C cuts C.size (n+t)
  let flag := fun t => decide (Influence n C g (n+t))
  have keepG : Kept G C (n+g) := by
    intro i hi eq
    have same : i = g := by omega
    subst i
    exact dirty (Finset.mem_filter.mp hi).2.2
  have sem (t : ℕ) (ht : t ∈ tops G C) (x : Fin n → Bool) :
      gateVal n C t x = (if flag t then gateVal n C g x && denotation (slot t) x else denotation (slot t) x) := by
    obtain ⟨r,op,below⟩ := Finset.mem_filter.mp ht
    have len : t < C.size := Finset.mem_range.mp r
    have keep : Kept G C (n+t) := by
      intro i hi eq
      have same : i = t := by omega
      subst i
      have other := (Finset.mem_filter.mp hi).2.1
      exact GateOp.noConfusion (op.symm.trans other)
    have enabled : (Influence n C g (n+t) → gateVal n C g x = true) →
        gateVal n C t x = denotation (slot t) x := root_cofactor G C g edge least form false (w:=n+t) (by omega) keep x
    by_cases path : Influence n C g (n+t)
    · simp only [flag,decide_eq_true path,if_true]
      cases hg : gateVal n C g x with
      | false =>
        cases hv : gateVal n C t x <;> simp_all [dom t ht path x]
      | true => simpa only [Bool.true_and] using enabled (fun _ => hg)
    · simpa [flag,path] using enabled (fun h => (path h).elim)
  obtain ⟨B,tr,slots⟩ := compiled_rows n C cuts C.size
  have source := source_in_bank G C g bound keepG edge least form slots
  have live' : ∃ t ∈ tops G C, flag t = true := by simpa [flag] using live
  obtain ⟨a,l,r,hg,ha,hl,hr,eq,card⟩ := join_from_top_slots G C g edge least form dirty flag slot B
    source live' (fun t _ => slots _) sem
  obtain ⟨D,ao,comp,size⟩ := circuit tr (gateVal n C g) a l r hg ha hl hr
  have min := least.2.2 D ao (comp.trans eq)
  have budget := original_budget G C g least.1 dirty
  change expense (seed n) (rows n C cuts C.size) + (readers n C g).card + (orT G C).card ≤ C.size at budget
  omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
