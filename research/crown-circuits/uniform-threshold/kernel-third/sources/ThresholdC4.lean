import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ThresholdC4
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def common (p : V × V) := G.neighborFinset p.1 ∩ G.neighborFinset p.2
def pairs (V : Type*) [Fintype V] := (Finset.univ : Finset V).offDiag
def tuples := (pairs V).sigma (fun p => (common G p).offDiag)
def ordered := (tuples G).card
def wedges := ∑ p ∈ pairs V, (common G p).card

theorem mem_tuples (x y a b : V) :
    (⟨(x,y),(a,b)⟩ : Σ _ : V×V, V×V) ∈ tuples G ↔
      x≠y ∧ a≠b ∧ G.Adj x a ∧ G.Adj y a ∧ G.Adj x b ∧ G.Adj y b := by
  simp [tuples,pairs,common,Finset.mem_offDiag,and_assoc,and_left_comm,and_comm]

theorem wedge_identity : wedges G = ∑ v, (G.neighborFinset v).offDiag.card := by
  let R := fun (p : V×V) (v : V) => G.Adj p.1 v ∧ G.Adj p.2 v
  have above (p : V×V) : (Finset.univ.bipartiteAbove R p) = common G p := by
    ext; simp [R,common]
  have below (v : V) : (pairs V).bipartiteBelow R v = (G.neighborFinset v).offDiag := by
    ext p
    simp only [Finset.mem_bipartiteBelow,pairs,Finset.mem_offDiag,Finset.mem_univ,
      true_and,SimpleGraph.mem_neighborFinset,R]
    constructor
    · rintro ⟨ne,h₁,h₂⟩
      exact ⟨h₁.symm,h₂.symm,ne⟩
    · rintro ⟨h₁,h₂,ne⟩
      exact ⟨ne,h₁.symm,h₂.symm⟩
  simpa only [above,below,wedges] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s:=pairs V) (t:=Finset.univ) R)

private theorem offdiag_add {α : Type*} (s : Finset α) :
    s.offDiag.card + s.card = s.card^2 := by
  rw [Finset.offDiag_card,sq]
  cases h : s.card with
  | zero => simp
  | succ k =>
    apply Nat.sub_add_cancel
    nlinarith [Nat.zero_le (k*k)]

theorem first_moment :
    (2*G.edgeFinset.card)^2 ≤ Fintype.card V*(wedges G + 2*G.edgeFinset.card) := by
  have h := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun v : V => G.degree v)
  have split (v : V) : G.degree v^2 = (G.neighborFinset v).offDiag.card + G.degree v :=
    (offdiag_add (G.neighborFinset v)).symm
  simpa only [Finset.card_univ, Nat.cast_id,split, Finset.sum_add_distrib,
    ← wedge_identity, G.sum_degrees_eq_twice_card_edges] using h

theorem second_moment : (wedges G)^2 ≤ (Fintype.card V)^2*(ordered G + wedges G) := by
  have split (p : V×V) : (common G p).card^2 =
      (common G p).offDiag.card + (common G p).card := (offdiag_add _).symm
  have h := sq_sum_le_card_mul_sum_sq (s:=pairs V) (f:=fun p => (common G p).card)
  have eq : ordered G = ∑ p ∈ pairs V, (common G p).offDiag.card := Finset.card_sigma _ _
  have le : (pairs V).card ≤ (Fintype.card V)^2 := by
    simp [pairs,Finset.offDiag_card,sq]
  calc
    (wedges G)^2 ≤ (pairs V).card*(ordered G + wedges G) := by
      simpa only [wedges,split,eq,Finset.sum_add_distrib,Nat.cast_id] using h
    _ ≤ _ := Nat.mul_le_mul_right _ le

theorem moment_arithmetic {w g T Q : Nat} (hw : 0<w) (wg : w≤g) (dense : w^3≤g^2)
    (h₁ : (2*g)^2 ≤ w*(T+2*g)) (h₂ : T^2 ≤ w^2*(Q+T)) :
    2*g^4 ≤ w^4*Q := by
  have first : 2*g^2 ≤ w*T := by nlinarith [Nat.mul_le_mul_right g wg]
  have many : 2*w^2 ≤ T := by
    apply Nat.le_of_mul_le_mul_left _ hw
    nlinarith
  have second : T^2 ≤ 2*w^2*Q := by nlinarith [Nat.mul_le_mul_right T many]
  have a := Nat.mul_le_mul first first
  have b := Nat.mul_le_mul_left (w^2) second
  nlinarith

theorem supersaturation (hw : 0<Fintype.card V) (wg : Fintype.card V≤G.edgeFinset.card)
    (dense : (Fintype.card V)^3≤G.edgeFinset.card^2) :
    2*G.edgeFinset.card^4 ≤ (Fintype.card V)^4*ordered G :=
  moment_arithmetic hw wg dense (first_moment G) (second_moment G)

theorem with_missing {M : Nat} (hw : 0<Fintype.card V) (wg : Fintype.card V≤G.edgeFinset.card)
    (dense : (Fintype.card V)^3≤G.edgeFinset.card^2) (charge : ordered G≤12*M) :
    G.edgeFinset.card^4 ≤ 6*M*(Fintype.card V)^4 := by
  have h := supersaturation G hw wg dense
  have b := Nat.mul_le_mul_left ((Fintype.card V)^4) charge
  nlinarith

theorem with_missing24 {M : Nat} (hw : 0<Fintype.card V) (wg : Fintype.card V≤G.edgeFinset.card)
    (dense : (Fintype.card V)^3≤G.edgeFinset.card^2) (charge : ordered G≤24*M) :
    G.edgeFinset.card^4 ≤ 12*M*(Fintype.card V)^4 := by
  have h := supersaturation G hw wg dense
  have b := Nat.mul_le_mul_left ((Fintype.card V)^4) charge
  nlinarith

#print axioms supersaturation
end ThresholdC4
