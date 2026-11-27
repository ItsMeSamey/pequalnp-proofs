import Init

/-! This module works in the edge-position representation of a simple
multigraph cycle, including a one-edge loop and a two-edge parallel pair.
To apply it to a minimal nonzero binary incidence-kernel support, one needs
the graph-theoretic characterization of such supports as simple cycles with
distinct edge labels. That characterization is external to this module. -/

namespace ThreeNameStar

/-- Positions in a vertex-simple cycle carry injective vertex labels. The
successor map is injective for any cyclic ordering, including lengths one
and two. The edge at position i joins vertex i to its successor. -/
structure CyclePositions (I V : Type) where
  vertex : I → V
  next : I → I
  vertex_inj : ∀ {i j}, vertex i = vertex j → i = j
  next_inj : ∀ {i j}, next i = next j → i = j

def Incident {I V} (c : CyclePositions I V) (x : V) (i : I) : Prop :=
  c.vertex i = x ∨ c.vertex (c.next i) = x

/-- Three different edge positions of a vertex-simple cycle cannot be
incident to a common vertex. Connectedness is unnecessary for this bound. -/
theorem excludes_three {I V} (c : CyclePositions I V) (x : V) (a b d : I)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : Incident c x a) (hb : Incident c x b) (hd : Incident c x d) : False := by
  have tailEq {i j : I} (hi : c.vertex i = x) (hj : c.vertex j = x) : i = j :=
    c.vertex_inj (hi.trans hj.symm)
  have headEq {i j : I} (hi : c.vertex (c.next i) = x)
      (hj : c.vertex (c.next j) = x) : i = j :=
    c.next_inj (tailEq hi hj)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hd with hd | hd
  all_goals first
    | exact hab (tailEq ha hb)
    | exact had (tailEq ha hd)
    | exact hbd (tailEq hb hd)
    | exact hab (headEq ha hb)
    | exact had (headEq ha hd)
    | exact hbd (headEq hb hd)

/-- Numerical terminal contradiction. The incidence bridge must supply:
edges ≤ used vertices from circuit rank and the row-sum dependence, the
handshake identity for the chosen multigraph, and strict degree excess
from even positive degrees with at least three spokes at the center. -/
theorem excludes_degree_excess (edges vertices degreeSum : Nat)
    (rank_bound : edges ≤ vertices) (handshake : degreeSum = 2 * edges)
    (degree_excess : 2 * vertices < degreeSum) : False := by
  rw [handshake] at degree_excess
  exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 rank_bound) degree_excess

#print axioms excludes_degree_excess
#print axioms excludes_three

end ThreeNameStar
