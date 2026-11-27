import Q1PrivateBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {a b w r s : ℕ} {A : Fin a → Clause n} {B : Fin b → Clause n} {W : Fin w → Clause n}

def JointInd (G : SimpleGraph (Fin n)) (p : ℕ → Bool → Fin n) (k : ℕ) :=
  ∀ i < k, ∀ j < k, i ≠ j → ∀ x y, ¬ G.Adj (p i x) (p j y)

theorem joint_bound (P : Batch G C A W r) (Q : Batch G C B W s)
    (p : ℕ → Bool → Fin n) (hp : ∀ (i : Fin r) k, p i.val k = P.pt i k)
    (hq : ∀ (j : Fin s) k, p (r+j.val) k = Q.pt j k) (noCross : JointInd G p (r+s)) :
    2^(r+s) ≤ w+a*b := by
  classical
  apply union_pow (fun i k => p i.val k)
    (fun c z => z ∈ A c) (fun c z => z ∈ B c) (fun c z => z ∈ W c)
  · intro c i
    by_cases hi : i.val < r
    · rw [hp ⟨i.val,hi⟩ false,hp ⟨i.val,hi⟩ true]; exact P.hits (.inr c) _
    · let j : Fin s := ⟨i.val-r,by have := i.isLt; omega⟩
      have e : r+j.val=i.val := by dsimp [j]; omega
      rw [← e,hq j false,hq j true]; exact Q.hits (.inr c) _
  · intro c i hi
    rw [hp ⟨i.val,hi⟩ false,hp ⟨i.val,hi⟩ true]; exact P.hits (.inl c) _
  · intro c i hi
    let j : Fin s := ⟨i.val-r,by have := i.isLt; omega⟩
    have e : r+j.val=i.val := by dsimp [j]; omega
    rw [← e,hq j false,hq j true]; exact Q.hits (.inl c) _
  · intro t
    let S := Finset.univ.image (fun i : Fin (r+s) => p i.val (t i))
    have indep : ¬ ∃ x ∈ S, ∃ y ∈ S, G.Adj x y := by
      rintro ⟨x,hx,y,hy,adj⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      by_cases e : i=j
      · subst j; exact G.irrefl adj
      · exact noCross i.val i.isLt j.val j.isLt (fun h => e (Fin.ext h)) _ _ adj
    have missing {m k : ℕ} {D : Fin m → Clause n} (R : Batch G C D W k) :
        ∃ d, ∀ i, p (i : Fin (r+s)).val (t i) ∉ literals D W d := by
      by_contra! h
      apply indep
      apply R.clean S
      intro d
      obtain ⟨i,hi⟩ := h d
      exact ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ i),hi⟩
    obtain ⟨d,hd⟩ := missing P
    obtain ⟨e,he⟩ := missing Q
    cases d with
    | inr d => exact Or.inl ⟨d,hd⟩
    | inl d =>
      cases e with
      | inr e => exact Or.inl ⟨e,he⟩
      | inl e => exact Or.inr ⟨⟨d,hd⟩,⟨e,he⟩⟩

theorem saves_or_induced (p : ℕ → Bool → Fin n) (k : ℕ) (T : Finset (Fin n))
    (external : ∀ x y, G.Adj x y → x ∈ T ∨ y ∈ T ∨
      ∃ i < k, ∃ z, x=p i z ∧ y=p i (!z)) :
    Saves p k T ∨ JointInd G p k := by
  classical
  by_cases save : Saves p k T
  · exact Or.inl save
  right
  intro i hi j hj ij x y adj
  rcases external _ _ adj with m | m | ⟨l,hl,z,e1,e2⟩
  · exact save (saves_precovered p T hi x m)
  · exact save (saves_precovered p T hj y m)
  · by_cases il : i=l
    · subst l
      exact save (saves_shared p T hj hi ij.symm y (!z) e2)
    · exact save (saves_shared p T hi hl il x z e1)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
