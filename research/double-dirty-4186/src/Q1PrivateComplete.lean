import Q1PrivateJoint

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {a b w r s : ℕ} {A : Fin a → Clause n} {B : Fin b → Clause n} {W : Fin w → Clause n}

private theorem joint_rich (four : NoFourCycle G) (hw : 1 ≤ w)
    (P : Batch G C A W 3) (Q : Batch G C B W 3)
    (p : ℕ → Bool → Fin n) (hp : ∀ (i : Fin 3) k, p i.val k = P.pt i k)
    (hq : ∀ (j : Fin 3) k, p (3+j.val) k = Q.pt j k)
    (exclusive : ∀ i < 6, ∀ j < 6, ∀ x y,
      p i x=p j y → p i (!x)=p j (!y) → i=j) : JointInd G p 6 := by
  let c : Fin w := ⟨0,by omega⟩
  have H {d k : ℕ} {D : Fin d → Clause n} (R : Batch G C D W k) (i : Fin k) :
      ∃ t, R.pt i t ∈ W c := by
    rcases R.hits (.inr c) i with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨x,hx⟩ := H P 0
  obtain ⟨y,hy⟩ := H P 1
  obtain ⟨d,hd⟩ := P.anchor (.inr c) _ hx _ hy (P.sep 0 1 (by decide) _ _)
  have cd (z) (hz : z ∈ W c) := (hd z hz).1
  have center {k : ℕ} {D : Fin k → Clause n} (R : Batch G C D W 3) :
      ∀ i b, G.Adj d (R.pt i b) := by
    obtain ⟨e,he⟩ := R.global_center four
    have eq := guard_center four R.pt (W c) e d he cd R.sep (H R)
    exact eq ▸ he
  have localFacts (i : ℕ) (hi : i < 6) (t : Bool) :
      G.Adj d (p i t) ∧ G.Adj (p i t) (p i (!t)) := by
    by_cases h : i < 3
    · let j : Fin 3 := ⟨i,h⟩
      rw [hp j t,hp j (!t)]
      exact ⟨center P j t,P.edges j t⟩
    · let j : Fin 3 := ⟨i-3,by omega⟩
      have eq : 3+j.val=i := by dsimp [j]; omega
      rw [← eq,hq j t,hq j (!t)]
      exact ⟨center Q j t,Q.edges j t⟩
  intro i hi j hj ij x y adj
  have h1 := nbhd_matching four (localFacts i hi x).1 (localFacts i hi (!x)).1
    (localFacts j hj y).1 (localFacts i hi x).2 adj
  have h2 := nbhd_matching four (localFacts j hj y).1 (localFacts j hj (!y)).1
    (localFacts i hi x).1 (localFacts j hj y).2 adj.symm
  exact ij (exclusive i hi j hj x (!y) h2.symm (by simpa using h1))

/-- The cover of all unassigned edges may be chosen before this extension. -/
theorem zeroLeak (four : NoFourCycle G) (ha : 2 ≤ a) (hb : 2 ≤ b) (hw : 1 ≤ w)
    (P : Batch G C A W r) (Q : Batch G C B W s)
    (p : ℕ → Bool → Fin n) (hp : ∀ (i : Fin r) k, p i.val k = P.pt i k)
    (hq : ∀ (j : Fin s) k, p (r+j.val) k = Q.pt j k)
    (T : Finset (Fin n))
    (exclusive : ∀ i < r+s, ∀ j < r+s, ∀ x y,
      p i x=p j y → p i (!x)=p j (!y) → i=j)
    (external : ∀ x y, G.Adj x y → x∈T ∨ y∈T ∨
      ∃ i < r+s, ∃ z, x=p i z ∧ y=p i (!z)) :
    ∃ S : Finset (Fin n), CoversOwned p (r+s) (T ∪ S) ∧
      (T ∪ S).card + (r+s) ≤ T.card + (a+b+w) := by
  classical
  rcases classify ha hb hw P.power Q.power with paid | bad
  · obtain ⟨S,hS,card⟩ := covers_baseline p (r+s) T
    exact ⟨S,hS,by omega⟩
  rcases bad with ⟨rfl,rfl,small⟩ | ⟨rfl,rfl,large⟩
  · by_cases size : w=3
    · have ab : a=2 ∧ b=2 := by rcases small with h | h | h <;> omega
      rcases saves_or_induced (G:=G) p 4 T external with ⟨S,cov,card⟩ | ind
      · exact ⟨S,cov,by omega⟩
      · have pow := joint_bound P Q p hp hq ind
        rw [size,ab.1,ab.2] at pow
        norm_num at pow
    · let c : Fin w := ⟨0,by omega⟩
      have tight : a+w=4 ∨ b+w=4 := by rcases small with h | h | h <;> omega
      have gpair : ∃ u v, W c={u,v} := tight.elim (fun h => P.small_guard four h c) (fun h => Q.small_guard four h c)
      obtain ⟨u,v,eq⟩ := gpair
      have hit : CoversOwned p 4 (W c) := by
        intro i hi
        by_cases h : i < 2
        · let j : Fin 2 := ⟨i,h⟩
          rw [hp j false,hp j true]; exact P.hits (.inr c) j
        · let j : Fin 2 := ⟨i-2,by omega⟩
          have e : 2+j.val=i := by dsimp [j]; omega
          rw [← e,hq j false,hq j true]; exact Q.hits (.inr c) j
      obtain ⟨S,cov,count⟩ := covers_guard_pair p T (W c) eq hit
      exact ⟨S,cov,by rcases small with h | h | h <;> omega⟩
  · have ind := joint_rich four hw P Q p hp hq exclusive
    exact False.elim (no_large_defect ha hb (Or.inr ⟨rfl,rfl,large⟩)
      (joint_bound P Q p hp hq ind))

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
