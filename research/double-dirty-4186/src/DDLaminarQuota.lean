import DDGroup
import DDMultiCost
import DoubleIncidence
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q0.Factor S4183.S98 Laminar Laminar.Group

private theorem normal_false (a b x y z : Prop) :
    ((a ∧ x) ∨ (b ∧ y)) ∨ z ↔ (a ∧ True ∧ x) ∨ (b ∧ y) ∨ z := by tauto
private theorem normal_true (a b x y z : Prop) :
    (b ∧ ((a ∧ x) ∨ y)) ∨ z ↔ (a ∧ b ∧ x) ∨ (b ∧ y) ∨ z := by tauto

/-- At most three distinct readers in the union when the sets of influenced roots
are disjoint or nested. The physical prefix ends immediately before aggregating its roots. -/
theorem laminar_quota {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (orig C : Circuit) (least : IsLeastAO G orig) (ao : IsAO2 n C) (roots : Finset ℕ)
    (valid : ∀ t ∈ roots, t < C.size) (cover : ∀ x, graphFun G ∅ x = true ↔
      ∃ t ∈ roots, gateVal n C t x = true) (edge : G.edgeFinset.Nonempty)
    (near : C.size + roots.card ≤ orig.size + 2) (a b : ℕ) (ha : a<C.size) (hb : b<C.size)
    (nested : Bool) (shape : ∀ t ∈ roots, strictInfluence n C a (n+t) →
      (strictInfluence n C b (n+t) ↔ nested = true))
    (S : Finset ℕ)
    (wireSem : ∀ t ∈ roots, ∀ x, gateVal n C t x = true ↔
      ((strictInfluence n C a (n+t) →
        denotation (physicalSlot n C (multiCuts n C S) C.size (n+a)) x = true) ∧
       (strictInfluence n C b (n+t) →
        denotation (physicalSlot n C (multiCuts n C S) C.size (n+b)) x = true)) ∧
      denotation (physicalSlot n C (multiCuts n C S) C.size (n+t)) x = true) :
    (S.biUnion (readers n C)).card ≤ 3 := by
  classical
  let cuts := multiCuts n C S
  let slot := fun i => physicalSlot n C cuts C.size (n+i)
  obtain ⟨bank,tr,wires⟩ := compiled_rows n C cuts C.size
  obtain ⟨p,sz,avail⟩ := tr.realize
  have ss (i : ℕ) : physically (Available p) (slot i) := by
    have h := wires (n+i)
    change physically bank (slot i) at h
    cases eq : slot i with
    | none => trivial
    | some f => exact avail _ (by simpa [eq,physically] using h)
  let A := roots.filter fun t => strictInfluence n C a (n+t)
  let R := roots \ A
  let B := R.filter fun t => strictInfluence n C b (n+t)
  let U := R \ B
  let g := fun (I : Finset ℕ) => ofList slot I.toList
  let I := restore (slot a) (g A)
  let T := if nested then restore (slot b) (merge I (g B)) else merge I (restore (slot b) (g B))
  let E := merge T (g U)
  have m (J : Finset ℕ) : mass (g J) = J.card := by simp [g,mass_list]
  have Ac : A ⊆ roots := Finset.filter_subset _ _
  have Bc : B ⊆ R := Finset.filter_subset _ _
  have c1 := Finset.card_sdiff_add_card_eq_card Ac
  have c2 := Finset.card_sdiff_add_card_eq_card Bc
  change R.card + A.card = roots.card at c1
  change U.card + B.card = R.card at c2
  have cnt : A.card+B.card+U.card=roots.card := by omega
  have bound : mass E ≤ roots.card+2 := by
    have left := mass_restore (slot a) (g A)
    rw [m] at left
    cases h : nested <;> simp only [E,T,I,h,Bool.false_eq_true,if_false,if_true,mass_merge,m] <;>
      first | (have r := mass_restore (slot b) (g B); rw [m] at r; omega) |
        (have r := mass_restore (slot b) (merge I (g B)); simp only [mass_merge,m] at r; dsimp [I] at r; omega)
  have goodg (J : Finset ℕ) : ok p (g J) := ok_list p _ _ (fun j _ => ss j)
  have goodI := ok_restore p (slot a) (g A) (ss a) (goodg A)
  have good : ok p E := by
    apply ok_merge p _ _ _ (goodg U)
    cases h : nested
    · simpa only [T,h,Bool.false_eq_true,if_false] using ok_merge p I _ goodI (ok_restore p _ _ (ss b) (goodg B))
    · simpa only [T,h,if_true] using ok_restore p _ _ (ss b) (ok_merge p _ _ goodI (goodg B))
  have represent (x : Fin n → Bool) : eval x E ↔ graphFun G ∅ x = true := by
    let val := fun i => denotation (slot i) x = true
    let hit := fun s t => strictInfluence n C s (n+t)
    have wire (t) (ht : t ∈ roots) : gateVal n C t x = true ↔
        ((hit a t → val a) ∧ (hit b t → val b)) ∧ val t := wireSem t ht x
    have vg (J : Finset ℕ) : eval x (g J) ↔ ∃ i ∈ J, val i := by
      simp only [g,eval_list,Finset.mem_toList,val]
    have am (t) : t ∈ A ↔ t ∈ roots ∧ hit a t := Finset.mem_filter
    have bm (t) : t ∈ B ↔ t ∈ roots ∧ ¬ hit a t ∧ hit b t := by
      simp only [B,R,A,Finset.mem_filter,Finset.mem_sdiff,hit]; tauto
    have um (t) : t ∈ U ↔ t ∈ roots ∧ ¬ hit a t ∧ ¬ hit b t := by
      simp only [U,B,R,A,Finset.mem_filter,Finset.mem_sdiff,hit]; tauto
    have modes := shape
    change ∀ t ∈ roots, hit a t → (hit b t ↔ nested = true) at modes
    have normal : eval x E ↔
        (val a ∧ (nested = true → val b) ∧ ∃ t ∈ A, val t) ∨
        (val b ∧ ∃ t ∈ B, val t) ∨ (∃ t ∈ U, val t) := by
      cases hn : nested <;>
        simp only [E,T,I,hn,Bool.false_eq_true,if_false,if_true,eval_merge,eval_restore,vg,
          true_implies,false_implies]
      · exact normal_false (val a) (val b) _ _ _
      · exact normal_true (val a) (val b) _ _ _
    rw [normal,cover]
    constructor
    · rintro (⟨va, whenB,t,ht,vt⟩ | ⟨vb,t,ht,vt⟩ | ⟨t,ht,vt⟩)
      · obtain ⟨ht,at'⟩ := (am t).mp ht
        exact ⟨t,ht,(wire t ht).mpr ⟨⟨fun _ => va, fun q => whenB ((modes t ht at').mp q)⟩,vt⟩⟩
      · obtain ⟨ht,at',_⟩ := (bm t).mp ht
        exact ⟨t,ht,(wire t ht).mpr ⟨⟨fun q => (at' q).elim, fun _ => vb⟩,vt⟩⟩
      · obtain ⟨ht,at',bt'⟩ := (um t).mp ht
        exact ⟨t,ht,(wire t ht).mpr ⟨⟨fun q => (at' q).elim,fun q => (bt' q).elim⟩,vt⟩⟩
    · rintro ⟨t,ht,act⟩
      obtain ⟨⟨aa,bb⟩,vt⟩ := (wire t ht).mp act
      by_cases ah : hit a t
      · exact Or.inl ⟨aa ah,fun ntrue => bb ((modes t ht ah).mpr ntrue),t,(am t).mpr ⟨ht,ah⟩,vt⟩
      · by_cases bh : hit b t
        · exact Or.inr (Or.inl ⟨bb bh,t,(bm t).mpr ⟨ht,ah,bh⟩,vt⟩)
        · exact Or.inr (Or.inr ⟨t,(um t).mpr ⟨ht,ah,bh⟩,vt⟩)
  obtain ⟨x,hx⟩ := gf_true n G edge
  have live := (represent x).mpr hx
  cases he : E with
  | none => simp [he,eval] at live
  | some e =>
    have r : ∀ x : Fin n → Bool, e.val x = graphFun G ∅ x := fun x =>
      Bool.eq_iff_iff.mpr (by simpa [he,eval] using represent x)
    have nontrue : ∃ x, e.val x = false := by
      refine ⟨fun _ => false, ?_⟩
      simp [r,graphFun]
    obtain ⟨D,aoD,fD,cD⟩ := Expr.finish p e (by simpa [he,ok] using good) nontrue
    have min := least.2.2 D aoD (fD.trans (funext r))
    have cost := multi_cut_cost C ao S
    change expense (seed n) (rows n C cuts C.size) + (S.biUnion (readers n C)).card ≤ C.size at cost
    rw [he] at bound
    change e.size+1 ≤ roots.card+2 at bound
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
