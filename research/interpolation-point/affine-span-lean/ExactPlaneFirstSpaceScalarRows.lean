import ExactPlaneFirstSpaceQueries
namespace ExactPlaneFirstSpaceQueries
open ExactPlaneFirstRelation ExactPlanePhysicalConverse
open scoped BigOperators
variable {N : ℕ} {K B : Type*} [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]

theorem extracted (k : Fin N→K) (b : Fin N→B) (s : Fin N→F) (A : Finset (Fin N))
    (ok : ExactTrace k b s A) :
    ∃ U, U⊆A ∧ ∃ g,Match g k b U ∧ (∑ i∈U,k i)=0 ∧ (∑ i∈U,s i)=1 := by
  obtain ⟨g,U,sub,m,key,one⟩ := extract k b s A ok
  exact ⟨U,sub,g,fun i hi=>m i (sub hi),key,one⟩

noncomputable def relationOracle (k : Fin N→K) (b : Fin N→B)
    (q : (Fin N→F)→Option (Finset (Fin N)))
    (valid : ∀ s A,q s=some A → ExactTrace k b s A) (s : Fin N→F) : Option (Finset (Fin N)) :=
  match ret : q s with
  | none => none
  | some A => some (Classical.choose (extracted k b s A (valid s A ret)))

theorem from_scalar (k : Fin N→K) (b : Fin N→B) {q}
    (safe : ∀ s,q s=none → ¬∃ A,ExactTrace k b s A)
    (valid : ∀ s A,q s=some A → ExactTrace k b s A) :
    ScalarContract k b (relationOracle k b q valid) := by
  constructor
  · intro s no
    unfold relationOracle at no
    split at no
    · exact safe s (by assumption)
    · contradiction
  · intro s U yes
    unfold relationOracle at yes
    split at yes
    · contradiction
    · rename_i A ret
      cases Option.some.inj yes
      exact (Classical.choose_spec (extracted k b s A (valid s A ret))).2

theorem recover_physical (k : Fin N→K) (b : Fin N→B) {q}
    (safe : ∀ s,q s=none → ¬∃ A,ExactTrace k b s A)
    (valid : ∀ s A,q s=some A → ExactTrace k b s A)
    (R : ExactPlaneFirstSpaceRecovery.Space N) (inc : R≤first k b) :
    let oracle := fun f => relationOracle k b q valid (weights f)
    let t := ExactPlaneFirstSpaceRecovery.loop ExactPlaneFirstSpaceRecovery.dualBasis oracle mask
      (N-Module.finrank F R) R
    ExactPlaneFirstSpaceRecovery.collected mask R t.witnesses=first k b ∧
      ExactPlaneFirstSpaceRecovery.Fresh mask R t.witnesses ∧
      t.witnesses.length≤N ∧ t.calls≤N*N :=
  ExactPlaneFirstSpaceRecovery.recover _ _ _ (contract (from_scalar k b safe valid)) R inc

#print axioms recover_physical
end ExactPlaneFirstSpaceQueries
