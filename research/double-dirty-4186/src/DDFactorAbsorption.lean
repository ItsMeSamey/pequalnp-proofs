import Q0FactorActual

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open S4183.S98 Q0.Factor

theorem erase_alias {n : ℕ} (C : Circuit) (ao : IsAO2 n C) {j i : ℕ}
    (hj : j < C.gates.length) (hi : i < n+j) (same : ∀ x, W n C x i = W n C x (n+j)) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      D.size + 1 = C.size := by
  refine ⟨eraseC n C j i, IsAO2_of_AO n _ (erase_AO n C j i (AO_of_IsAO2 n C ao) hj hi), ?_, ?_⟩
  · intro x
    exact erase_wires n C j i hj hi x (Or.inl (same x)) C.output (fun _ => same x)
  · exact erase_length n C j i hj

theorem path_implies_source {n : ℕ} {C : Circuit} {g w : ℕ} (ao : IsAO2 n C)
    (path : AndPath n C g w) (x : Fin n → Bool) :
    W n C x w = true → W n C x (n+g) = true := by
  induction path with
  | source => exact id
  | step prev hj op pin ih =>
    obtain ⟨_, a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C ao _ hj
    rw [W_and n C x _ hj op a b pins ha hb, Bool.and_eq_true]
    intro bits
    rw [pins] at pin
    rcases List.mem_cons.mp pin with eq | rest
    · exact ih (by simpa only [eq] using bits.1)
    · obtain eq := List.mem_singleton.mp rest
      exact ih (by simpa only [eq] using bits.2)

theorem no_comparable_or_arms {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) {g w j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .or)
    (pins : (gateAt C j).inputs = [n+g,w] ∨ (gateAt C j).inputs = [w,n+g]) :
    ¬ AndPath n C g w := by
  intro path
  have ha : n+g < n+j := least.1.2.1 j hj _ (by rcases pins with h|h <;> simp [h])
  have hb : w < n+j := least.1.2.1 j hj _ (by rcases pins with h|h <;> simp [h])
  have same (x : Fin n → Bool) : W n C x (n+g) = W n C x (n+j) := by
    have dep := path_implies_source least.1 path x
    rcases pins with h | h
    · rw [W_or n C x j hj hop _ _ h ha hb]
      cases h1 : W n C x (n+g) <;> cases h2 : W n C x w <;> simp_all
    · rw [W_or n C x j hj hop _ _ h hb ha]
      cases h1 : W n C x (n+g) <;> cases h2 : W n C x w <;> simp_all
  obtain ⟨D,hD,agree,bound⟩ := erase_alias C least.1 hj ha same
  have hd := least.2.2 D hD (funext fun x => (agree x).trans (congrFun least.2.1 x))
  omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
