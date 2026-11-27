import Q1DoubleStarPool

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private
open scoped BigOperators

structure Projected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  a : ℕ
  w : ℕ
  count : ℕ
  left : Fin a → Clause n
  right : Fin w → Clause n
  batch : Batch G C left right count

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def Projected.exclusive (P Q : Projected G C) : Prop :=
  ∀ i j b c, s(P.batch.pt i b,P.batch.pt i (!b)) ≠ s(Q.batch.pt j c,Q.batch.pt j (!c))

def Projected.inside (P : Projected G C) (v : Fin n) : Prop :=
  ∀ i b, G.Adj v (P.batch.pt i b)

theorem Projected.exclusive_symm {P Q : Projected G C} (h : P.exclusive Q) : Q.exclusive P :=
  fun i j b c h' => h j i c b h'.symm

/-- The physical palette consists of the common base slots plus one fresh
private label per external private pin. Distinct roots can name a base slot
repeatedly without increasing this bound. -/
theorem pooled_star_layout {B I Base : Type*} [Fintype B] [Fintype I] [Fintype Base]
    (four : NoFourCycle G) (v : Fin n) (central : B → Projected G C)
    (external : I → Projected G C) (phys : Base → Clause n)
    (cID : ∀ b, Fin (central b).a ⊕ Fin (central b).w → Base)
    (eID : ∀ i, Fin (external i).a → Base)
    (cOK : ∀ b c, phys (cID b c) = literals (central b).left (central b).right c)
    (eOK : ∀ i c, phys (eID i c) = (external i).left c)
    (hc : ∀ b, 0 < (central b).count) (he : ∀ i, 0 < (external i).count)
    (nearC : ∀ b, (central b).inside v) (nearE : ∀ i, (external i).inside v)
    (cc : ∀ b d, b≠d → (central b).exclusive (central d))
    (ee : ∀ i j, i≠j → (external i).exclusive (external j))
    (ce : ∀ b i, (central b).exclusive (external i)) :
    (∑ b, 2^(central b).count) + ∑ i, 2^(external i).count ≤
      Fintype.card Base + ∑ i, (external i).w := by
  classical
  let R := B ⊕ I
  let L := Base ⊕ Σ i, Fin (external i).w
  let d : R → Projected G C := Sum.elim central external
  let support : L → Clause n := Sum.elim phys (fun p => (external p.1).right p.2)
  let locate : ∀ j : R, Fin (d j).a ⊕ Fin (d j).w → L := fun j => by
    cases j with
    | inl b => exact fun c => Sum.inl (cID b c)
    | inr i => exact Sum.elim (fun c => Sum.inl (eID i c)) (fun p => Sum.inr ⟨i,p⟩)
  have ok (j : R) (c) : support (locate j c) = literals (d j).left (d j).right c := by
    cases j with
    | inl b => exact cOK b c
    | inr i => cases c with
      | inl k => exact eOK i k
      | inr k => rfl
  have sep (j k : R) (ne : j≠k) : (d j).exclusive (d k) := by
    cases j with
    | inl b =>
      cases k with
      | inl d => exact cc b d (fun eq => ne (congrArg Sum.inl eq))
      | inr i => exact ce b i
    | inr i =>
      cases k with
      | inl b => exact Projected.exclusive_symm (ce b i)
      | inr j => exact ee i j (fun eq => ne (congrArg Sum.inr eq))
  have near (j : R) : (d j).inside v := by cases j with
    | inl b => exact nearC b
    | inr i => exact nearE i
  have pos (j : R) : 0 < (d j).count := by cases j with
    | inl b => exact hc b
    | inr i => exact he i
  have bound := weighted_batch_pool four (fun j => (d j).a) (fun j => (d j).w)
    (fun j => (d j).count) (fun j => (d j).left) (fun j => (d j).right)
    (fun j => (d j).batch) pos locate support ok v near sep
  simpa [L,R,d,Fintype.sum_sum_type,Fintype.card_sigma] using bound
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
