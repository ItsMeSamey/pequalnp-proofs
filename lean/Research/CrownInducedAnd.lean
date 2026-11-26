import Research.CrownEdgeCharge

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- Physical AND gates that avoid a given set of raw or internal wires. -/
def avoidingAnds (C : Circuit) (D : Finset ℕ) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun k => isAndGate C.gates[k] && C.gates[k].inputs.all (fun a => a ∉ D))

/-- Every pair of separated assignments differs on the left input of a
physical AND that avoids all uniformly false wires. -/
theorem induced_and_codes {I : Type} [Fintype I] (C : Circuit) (hm : Monotone2 C)
    (single : I → List Bool) (pair : I → I → List Bool) (D : Finset ℕ)
    (dead : ∀ i, ∀ a ∈ D, (C.wires (single i)).getD a false = false)
    (off : ∀ i, C.eval (single i) = false)
    (on : ∀ i j, i ≠ j → C.eval (pair i j) = true)
    (ll : ∀ i j, (single i).length = (pair i j).length)
    (lr : ∀ i j, (single j).length = (pair i j).length)
    (reads : ∀ i j a, (pair i j).getD a false = true →
      (single i).getD a false = true ∨ (single j).getD a false = true) :
    Fintype.card I ≤ 2 ^ (avoidingAnds C D).card := by
  classical
  let code (i : I) (k : avoidingAnds C D) : Bool :=
    (C.wires (single i)).getD (C.gates[k.val].inputs.getD 0 0) false
  have inj : Function.Injective code := by
    intro i j e
    by_contra ne
    obtain ⟨k,_,a,b,op,hp,_,_,opp⟩ := first_mixed_and C (pair i j) (single i) (single j)
      hm (ll i j) (lr i j) (reads i j) (on i j ne) (off i) (off j)
    obtain ⟨na,nb,diff⟩ : a ∉ D ∧ b ∉ D ∧
        (C.wires (single i)).getD a false ≠ (C.wires (single j)).getD a false := by
      rcases opp with ⟨ia,ja,ib,jb⟩ | ⟨ib,jb,ia,ja⟩
      · exact ⟨fun h => Bool.noConfusion (ia.symm.trans (dead i a h)),
          fun h => Bool.noConfusion (jb.symm.trans (dead j b h)),by rw [ia,ja]; decide⟩
      · exact ⟨fun h => Bool.noConfusion (ja.symm.trans (dead j a h)),
          fun h => Bool.noConfusion (ib.symm.trans (dead i b h)),by rw [ia,ja]; decide⟩
    have hk : k ∈ avoidingAnds C D  := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change (isAndGate C.gates[k] && C.gates[k].inputs.all _) = true
      unfold isAndGate
      rw [op,hp]
      simp [na,nb]
    apply diff
    have eh := congrFun e (⟨k,hk⟩ : avoidingAnds C D)
    change (C.wires (single i)).getD (C.gates[k].inputs.getD 0 0) false =
      (C.wires (single j)).getD (C.gates[k].inputs.getD 0 0) false at eh
    rw [hp] at eh
    exact eh
  simpa using Fintype.card_le_of_injective code inj

theorem induced_crown_and_lower (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (S : Finset (Fin 12)) (D : Finset ℕ)
    (dead : ∀ i ∈ S, ∀ a ∈ D, (C.wires (oneEach i i)).getD a false = false) :
    S.card ≤ 2 ^ (avoidingAnds C D).card := by
  classical
  let single (i : S) := oneEach i.val i.val
  let pair (i j : S) := oneEach i.val j.val
  have bound := induced_and_codes C hm single pair D (fun i => dead i i.property)
    (fun i => (rep i i).trans (by simp))
    (fun i j h => (rep i j).trans (decide_eq_true (fun e => h (Subtype.ext e))))
    (fun i j => by simp [single,pair,oneEach]) (fun i j => by simp [single,pair,oneEach])
    (by
      intro i j a ha
      simp only [pair,pair_reads,Bool.or_eq_true_iff] at ha
      simp only [single,pair_reads,Bool.or_eq_true_iff]
      tauto)
  simpa using bound

end PEqualNP.Research.MissingCell
