import ThreeNameChain

namespace ThreeNameProjectionStep
open scoped BigOperators
open ThreeNameChain
variable {ι V K : Type*} [DecidableEq ι] [AddCommGroup V] [AddCommGroup K]

/-- The row map F fixes the retained side and factors on the discarded side
through the interface encoder E. Thus every common sum has a fresh copy. -/
def build (R X : Finset ι) (p q : Carrier ι V) (F : V →+ V) (E : K →+ V)
    (coeff : ι → K) (fresh : K → ι)
    (roots : R ⊆ X) (keep : X ⊆ q.ground)
    (same : ∀ i ∈ X, q.col i = p.col i)
    (fixes : ∀ i ∈ X, F (p.col i) = p.col i)
    (factor : ∀ i ∈ p.ground \ X, F (p.col i) = E (coeff i))
    (covers : ∀ c, E c ≠ 0 → fresh c ∈ q.ground ∧ fresh c ∉ p.ground ∧ q.col (fresh c) = E c) :
    Step R p q := by
  refine ⟨X,roots,keep,same,?_⟩
  intro A ha B hb nz eq
  have fixed : F (∑ i ∈ A, p.col i) = ∑ i ∈ A, p.col i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i hi => fixes i (ha hi))
  have factored : F (∑ i ∈ B, p.col i) = E (∑ i ∈ B, coeff i) := by
    rw [map_sum,map_sum]
    exact Finset.sum_congr rfl (fun i hi => factor i (hb hi))
  have enc : (∑ i ∈ A, p.col i) = E (∑ i ∈ B, coeff i) :=
    fixed.symm.trans ((congrArg F eq).trans factored)
  obtain ⟨hq,hp,hval⟩ := covers _ (fun z => nz (enc.trans z))
  exact ⟨_,hq,hp,hval.trans enc.symm⟩

/-- Bounded interface table variant, requiring only checks on printed entries.
The table has at most four vectors for vertical orders at most two. -/
def tableStep [DecidableEq V] (R X : Finset ι) (p q : Carrier ι V)
    (F : V →+ V) (S : Finset V) (roots : R ⊆ X) (keep : X ⊆ q.ground)
    (same : ∀ i ∈ X, q.col i = p.col i)
    (fixes : ∀ i ∈ X, F (p.col i) = p.col i)
    (factor : ∀ i ∈ p.ground \ X, F (p.col i) ∈ S)
    (z : (0 : V) ∈ S) (closed : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
    (copies : ∀ a ∈ S, a ≠ 0 → ∃ f ∈ q.ground, f ∉ p.ground ∧ q.col f = a) :
    Step R p q := by
  refine ⟨X,roots,keep,same,?_⟩
  intro A ha B hb nz eq
  have fixed : F (∑ i ∈ A, p.col i) = ∑ i ∈ A, p.col i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i hi => fixes i (ha hi))
  have member (D : Finset ι) (hd : D ⊆ p.ground \ X) : (∑ i ∈ D, F (p.col i)) ∈ S := by
    induction D using Finset.induction_on with
    | empty => simpa using z
    | insert i D hi ih =>
      rw [Finset.sum_insert hi]
      exact closed _ (factor i (hd (Finset.mem_insert_self _ _))) _
        (ih (fun j hj => hd (Finset.mem_insert_of_mem hj)))
  have m := member B hb
  rw [← map_sum,← eq,fixed] at m
  exact copies _ m nz

/-- Total finite table checker. All quantifiers range over printed site
or interface lists, including the existential witness for a fresh copy. -/
def checkTable [DecidableEq V] (R X : Finset ι) (p q : Carrier ι V)
    (F : V →+ V) (S : Finset V) : Bool :=
  decide (R ⊆ X ∧ X ⊆ q.ground ∧
    (∀ i ∈ X, q.col i = p.col i) ∧ (∀ i ∈ X, F (p.col i) = p.col i) ∧
    (∀ i ∈ p.ground \ X, F (p.col i) ∈ S) ∧ (0 : V) ∈ S ∧
    (∀ a ∈ S, ∀ b ∈ S, a+b ∈ S) ∧
    (∀ a ∈ S, a ≠ 0 → ∃ f ∈ q.ground, f ∉ p.ground ∧ q.col f = a))

def checkedStep [DecidableEq V] (R X : Finset ι) (p q : Carrier ι V)
    (F : V →+ V) (S : Finset V) (ok : checkTable R X p q F S = true) :
    Step R p q := by
  unfold checkTable at ok
  obtain ⟨hr,hk,hs,hf,hy,hz,ha,hc⟩ := of_decide_eq_true ok
  exact tableStep R X p q F S hr hk hs hf hy hz ha hc

#print axioms checkedStep
#print axioms tableStep
#print axioms build
end ThreeNameProjectionStep
