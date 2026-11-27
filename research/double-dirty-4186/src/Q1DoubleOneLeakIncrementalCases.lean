import Q1DoubleOneLeakCover

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

private theorem cheapEndpoints {V : Type*} [DecidableEq V] (E : Finset (Sym2 V)) :
    ∃ S : Finset V, covers S E ∧ S.card ≤ E.card := by
  classical
  let S := E.image (fun e : Sym2 V => e.out.1)
  refine ⟨S, ?_, Finset.card_image_le⟩
  intro u v he
  have h : (s(u,v)).out.1 ∈ S := Finset.mem_image.mpr ⟨_,he,rfl⟩
  rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v)) with eq | eq
  · exact Or.inl (eq ▸ h)
  · exact Or.inr (eq ▸ h)

theorem two_incremental {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (a b w y : ℕ) (R S H : Finset (Sym2 (Fin n))) (ha : 2 ≤ a)
    (hy : 3 ≤ y) (exp : 0 < H.card → 2^H.card ≤ y) (opp : 2*S.card ≤ b+w)
    (base : ∀ x z, G.Adj x z → s(x,z) ∉ (R ∪ S ∪ H) → x ∈ T ∨ z ∈ T)
    (privateCover : ∀ X : Finset (Fin n),
      (∀ x z, G.Adj x z → s(x,z) ∉ (R ∪ S) → x ∈ X ∨ z ∈ X) →
      ∃ Z, covers (X ∪ Z) R ∧ covers (X ∪ Z) S ∧
        (X ∪ Z).card + R.card + S.card ≤ X.card + (a+b+w))
    (tight : H.card=2 → y=4 →
      R.card ≤ 1 ∧ ∃ F, covers F R ∧ covers F H ∧ F.card ≤ 2) :
    ∃ K, covers (T ∪ K) R ∧ covers (T ∪ K) S ∧ covers (T ∪ K) H ∧
      (T ∪ K).card+R.card+S.card+H.card ≤ T.card+(a+b+w+y-1) := by
  classical
  rcases two_slack hy exp with slack | ⟨sz,sy⟩
  · obtain ⟨F,hF,cF⟩ := cheapEndpoints H
    have hX : ∀ x z, G.Adj x z → s(x,z) ∉ R ∪ S → x ∈ T ∪ F ∨ z ∈ T ∪ F := by
      intro x z adj out
      by_cases he : s(x,z) ∈ H
      · exact (hF _ _ he).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
      · exact (base _ _ adj (fun bad => (Finset.mem_union.mp bad).elim out he)).imp
          (Finset.mem_union_left F) (Finset.mem_union_left F)
    obtain ⟨Z,cr,cs,cost⟩ := privateCover (T ∪ F) hX
    refine ⟨F ∪ Z,?_,?_,?_,?_⟩
    · simpa only [Finset.union_assoc] using cr
    · simpa only [Finset.union_assoc] using cs
    · intro x z he
      exact (hF _ _ he).imp
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Z h))
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Z h))
    · rw [← Finset.union_assoc]
      have bound := Finset.card_union_le T F
      omega
  · obtain ⟨r,F,cr,ch,cf⟩ := tight sz sy
    obtain ⟨Y,cs,cy⟩ := cheapEndpoints S
    refine ⟨F ∪ Y,?_,?_,?_,?_⟩
    · intro x z he
      exact (cr _ _ he).imp
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Y h))
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Y h))
    · intro x z he
      exact (cs _ _ he).imp
        (fun h => Finset.mem_union_right T (Finset.mem_union_right F h))
        (fun h => Finset.mem_union_right T (Finset.mem_union_right F h))
    · intro x z he
      exact (ch _ _ he).imp
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Y h))
        (fun h => Finset.mem_union_right T (Finset.mem_union_left Y h))
    · have u := Finset.card_union_le T (F ∪ Y)
      have v := Finset.card_union_le F Y
      omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
