import DDCap
import DDFactorAbsorption
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

theorem reader_lt {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {a b : ℕ}
    (h : b ∈ readers n C a) : a < b := by
  obtain ⟨len,pin⟩ := Finset.mem_filter.mp h
  have := ao.2.1 b (Finset.mem_range.mp len) _ pin
  omega

theorem reader_reach {n : ℕ} {C : Circuit} {a b : ℕ} (h : b ∈ readers n C a) :
    strictInfluence n C a (n+b) := by
  obtain ⟨len,pin⟩ := Finset.mem_filter.mp h
  exact ⟨b,Finset.mem_range.mp len,rfl,n+a,pin,.source⟩

theorem common_value {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {a b j : ℕ} (ne : a ≠ b)
    (ja : j ∈ readers n C a) (jb : j ∈ readers n C b) (op : (gateAt C j).op = .and) :
    ∀ x, gateVal n C j x = (gateVal n C a x && gateVal n C b x) := by
  obtain ⟨len,pa⟩ := Finset.mem_filter.mp ja
  have pb := (Finset.mem_filter.mp jb).2
  have bound := Finset.mem_range.mp len
  obtain ⟨_,p,q,pins,hp,hq⟩ := AO_of_IsAO2 n C ao j bound
  intro x
  change W n C x (n+j) = (W n C x (n+a) && W n C x (n+b))
  rw [W_and n C x j bound op _ _ pins hp hq]
  rw [pins] at pa pb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pa pb
  rcases pa with pa|pa <;> rcases pb with pb|pb
  · omega
  · rw [←pa,←pb]
  · rw [←pa,←pb,Bool.and_comm]
  · omega

theorem first_reader {n : ℕ} {C : Circuit} {g w : ℕ} (h : strictInfluence n C g w) :
    (readers n C g).Nonempty := by
  obtain ⟨j,hj,rfl,v,pin,path⟩ := h
  have start : ∀ {u}, Influence n C g u → u=n+g ∨ (readers n C g).Nonempty := by
    intro u p
    induction p with
    | source => exact .inl rfl
    | step prev hj hp ih =>
      rcases ih with rfl | h
      · exact .inr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hp⟩⟩
      · exact .inr h
  rcases start path with rfl | found
  · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩⟩
  · exact found

theorem reader_of_live_alias {n b j : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {roots : Finset ℕ} (dirty : ¬ BelowF G C b)
    (clean : ∀ r ∈ roots, BelowF G C r)
    (live : ∃ r ∈ roots, j=r ∨ strictInfluence n C j (n+r))
    (aliasEq : gateVal n C j = gateVal n C b) : (readers n C j).Nonempty := by
  obtain ⟨r,hr,eq|step⟩ := live
  · subst j
    exact (dirty (fun x hx => clean r hr x ((congrFun aliasEq x).trans hx))).elim
  · exact first_reader step

private theorem three_ids {A : Finset ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) : 3 ≤ A.card := by
  have sub : ({a,b,c} : Finset ℕ) ⊆ A := by simpa [Finset.insert_subset_iff,ha,hb,hc]
  have := Finset.card_le_card sub
  simpa [ab,ac,bc] using this

/-- A live shared reader of comparable sources cannot coexist with a second live
reader of the later source. Every auxiliary cut gate is a semantic alias of that
source; the contradiction uses the actual union of distinct gate-reader IDs. -/
theorem no_comparable_common {n : ℕ} (C : Circuit) (ao : IsAO2 n C) {a b z v : ℕ}
    (ab : a ≠ b) (zv : z ≠ v) (za : z ∈ readers n C a)
    (zb : z ∈ readers n C b) (vb : v ∈ readers n C b)
    (zAnd : (gateAt C z).op = .and) (vAnd : (gateAt C v).op = .and)
    (dominates : ∀ x, gateVal n C b x = true → gateVal n C a x = true)
    (zNext : gateVal n C z = gateVal n C b → (readers n C z).Nonempty)
    (vNext : gateVal n C v = gateVal n C b → (readers n C v).Nonempty)
    (quota : ∀ S : Finset ℕ, b ∈ S → (∀ i ∈ S, i≠b →
      strictInfluence n C b (n+i) ∧ gateVal n C i = gateVal n C b) →
      (S.biUnion (readers n C)).card ≤ 2) : False := by
  classical
  have zval := common_value ao ab za zb zAnd
  have zEq : gateVal n C z = gateVal n C b := by
    funext x
    rw [zval]
    cases h : gateVal n C b x with
    | false => simp
    | true => simp [dominates x h]
  have zReach := reader_reach zb
  have zr := reader_lt ao zb
  obtain ⟨w,wr⟩ := zNext zEq
  have zw := reader_lt ao wr
  have wv : w=v := by
    by_contra neq
    let S : Finset ℕ := {b,z}
    have hasB : b ∈ S := by simp [S]
    have hasZ : z ∈ S := by simp [S]
    have bound := quota S hasB (by
      intro i hi hn
      have eq : i=z := by simpa [S,hn] using hi
      subst i
      exact ⟨zReach,zEq⟩)
    have enough := three_ids (Finset.mem_biUnion.mpr ⟨b,hasB,zb⟩ : z ∈ S.biUnion (readers n C))
      (Finset.mem_biUnion.mpr ⟨b,hasB,vb⟩) (Finset.mem_biUnion.mpr ⟨z,hasZ,wr⟩)
      zv (by omega) (fun h => neq h.symm)
    omega
  subst w
  have vval := common_value ao (by omega : b≠z) vb wr vAnd
  have vEq : gateVal n C v = gateVal n C b := by
    funext x
    rw [vval,zEq]
    simp
  let S : Finset ℕ := {b,z,v}
  have hasB : b ∈ S := by simp [S]
  have hasZ : z ∈ S := by simp [S]
  have hasV : v ∈ S := by simp [S]
  have bound := quota S hasB (by
    intro i hi hn
    have eq : i=z ∨ i=v := by simpa [S,hn] using hi
    rcases eq with rfl|rfl
    · exact ⟨zReach,zEq⟩
    · exact ⟨reader_reach vb,vEq⟩)
  obtain ⟨k,hk⟩ := vNext vEq
  have vk := reader_lt ao hk
  have enough := three_ids (Finset.mem_biUnion.mpr ⟨b,hasB,zb⟩ : z ∈ S.biUnion (readers n C))
    (Finset.mem_biUnion.mpr ⟨b,hasB,vb⟩) (Finset.mem_biUnion.mpr ⟨v,hasV,hk⟩)
    zv (by omega) (by omega)
  omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
