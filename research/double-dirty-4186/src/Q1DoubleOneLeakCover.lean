import Q1DoubleOneLeakProfiles

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

variable {V : Type*} [DecidableEq V]

def covers (S : Finset V) (R : Finset (Sym2 V)) : Prop :=
  ∀ a b, s(a,b) ∈ R → a ∈ S ∨ b ∈ S

private theorem endpointCover (R : Finset (Sym2 V)) :
    ∃ S : Finset V, covers S R ∧ S.card ≤ R.card := by
  classical
  let S := R.image (fun e => e.out.1)
  refine ⟨S, ?_, Finset.card_image_le⟩
  intro u v he
  have hp : (s(u,v)).out.1 ∈ S := Finset.mem_image.mpr ⟨_,he,rfl⟩
  rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v)) with h | h
  · exact Or.inl (h ▸ hp)
  · exact Or.inr (h ▸ hp)

private theorem extendCover (R T P : Finset (Sym2 V)) (S : Finset V)
    (hR : covers S R) (hT : covers S T) :
    ∃ F, covers F R ∧ covers F T ∧ covers F P ∧ F.card ≤ S.card + P.card := by
  classical
  obtain ⟨D,hD,sz⟩ := endpointCover P
  have left {E} (h : covers S E) : covers (S ∪ D) E := by
    intro a b ab
    exact (h a b ab).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
  refine ⟨S ∪ D,left hR,left hT,?_,(Finset.card_union_le _ _).trans (by omega)⟩
  intro a b ab
  exact (hD a b ab).imp (Finset.mem_union_right _) (Finset.mem_union_right _)

/-- The two pairs need not attain their savings with the same cover. Pick one
of their covers and add endpoints only for the third batch. -/
theorem large_cover (p : Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z) (hb : 2 ≤ p.b)
    (hw : 1 ≤ p.w) (ar : 2^p.r ≤ p.k+p.x+p.w) (bs : 2^p.s ≤ p.b+p.w)
    (yh : 2^p.h ≤ p.k+p.z) (R S H : Finset (Sym2 V))
    (rc : R.card=p.r) (sc : S.card=p.s) (hc : H.card=p.h)
    (armExt : ∃ i ∈ pairOptions (p.k+p.x+p.w) (p.k+p.z) p.k p.r p.h,
       ∃ F, covers F R ∧ covers F H ∧ F.card+i ≤ p.r+p.h)
    (armArm : ∃ j ∈ pairOptions (p.k+p.x+p.w) (p.b+p.w) p.w p.r p.s,
       ∃ F, covers F R ∧ covers F S ∧ F.card+j ≤ p.r+p.s)
    (exactFour : p.k=3 → p.k+p.z=4 → p.h=2 → p.r=0) :
    ∃ F, covers F R ∧ covers F S ∧ covers F H ∧ F.card+p.r+p.s+p.h ≤ p.budget := by
  obtain ⟨i,hi,F,hr,hh,cf⟩ := armExt
  obtain ⟨j,hj,D,dr,ds,cd⟩ := armArm
  have paid := pay_large p hk hz hb hw (max i j) ar bs yh
    ⟨i,hi,Nat.le_max_left _ _⟩ ⟨j,hj,Nat.le_max_right _ _⟩ exactFour
  by_cases ord : j ≤ i
  · rw [max_eq_left ord] at paid
    obtain ⟨K,kr,kh,ks,ck⟩ := extendCover R H S F hr hh
    exact ⟨K,kr,ks,kh,by omega⟩
  · rw [max_eq_right (by omega)] at paid
    obtain ⟨K,kr,ks,kh,ck⟩ := extendCover R S H D dr ds
    exact ⟨K,kr,ks,kh,by omega⟩

/-- Two shared slots. The only external batch without one spare slot has
two edges and four slots. Its common labeled hub supplies the joint cover. -/
theorem two_cover (a b w y : ℕ) (R S H : Finset (Sym2 V)) (ha : 2 ≤ a)
    (hy : 3 ≤ y) (exp : 0 < H.card → 2^H.card ≤ y) (opp : 2*S.card ≤ b+w)
    (privateCover : ∃ F, covers F R ∧ covers F S ∧ F.card+R.card+S.card ≤ a+b+w)
    (tight : H.card=2 → y=4 →
      R.card ≤ 1 ∧ ∃ F, covers F R ∧ covers F H ∧ F.card ≤ 2) :
    ∃ K, covers K R ∧ covers K S ∧ covers K H ∧
      K.card+R.card+S.card+H.card ≤ a+b+w+y-1 := by
  rcases two_slack hy exp with slack | ⟨he,ys⟩
  · obtain ⟨F,fr,fs,cost⟩ := privateCover
    obtain ⟨K,kr,ks,kh,ck⟩ := extendCover R S H F fr fs
    exact ⟨K,kr,ks,kh,by omega⟩
  · obtain ⟨r,F,fr,fh,cost⟩ := tight he ys
    obtain ⟨K,kr,kh,ks,ck⟩ := extendCover R H S F fr fh
    exact ⟨K,kr,ks,kh,by omega⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
