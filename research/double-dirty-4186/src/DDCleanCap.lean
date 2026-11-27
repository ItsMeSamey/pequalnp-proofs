import DDGroup
import DDMultiCost
import DoubleIncidence
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q0.Factor S4183.S98 Laminar Laminar.Group

/-- A clean common product absorbs all other roots in its class. -/
theorem clean_cap_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (orig C : Circuit) (least : IsLeastAO G orig) (ao : IsAO2 n C) (roots : Finset ℕ)
    (valid : ∀ t ∈ roots, t < C.size) (cover : ∀ x, graphFun G ∅ x = true ↔
      ∃ t ∈ roots, gateVal n C t x = true) (edge : G.edgeFinset.Nonempty)
    (near : C.size + roots.card ≤ orig.size + 2) (a : ℕ) (ha : a<C.size)
    (A : Finset ℕ) (sub : A ⊆ roots) (many : A.Nonempty)
    (cleanProduct : BelowF G C a)
    (absorb : ∀ x, (∃ t ∈ A, gateVal n C t x = true) → gateVal n C a x = true)
    (unaffected : ∀ t ∈ roots \ A, ¬strictInfluence n C a (n+t)) :
    (readers n C a).card ≤ 1 := by
  classical
  let S : Finset ℕ := {a}
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
  let U := roots \ A
  have cnt : U.card+A.card=roots.card := Finset.card_sdiff_add_card_eq_card sub
  let P : Expr n := .leaf (slot a)
  let E := merge (some P) (ofList slot U.toList)
  have good : ok p E := ok_merge p _ _ (ss a) (ok_list p slot _ (fun i _ => ss i))
  have bound : mass E = U.card+1 := by
    rw [show E = merge (some P) (ofList slot U.toList) from rfl,mass_merge,mass_list]
    simp [mass,P,Expr.size,Nat.add_comm]
  have unchanged {t : ℕ} (lt : t<C.size)
      (free : ¬strictInfluence n C a (n+t)) (x : Fin n → Bool) :
      gateVal n C t x = denotation (slot t) x := by
    apply multi_agree C ao S (by omega)
    intro i hi h
    have eq : i=a := by simpa [S] using hi
    subst i
    exact (free h).elim
  have represent (x : Fin n → Bool) : eval x E ↔ graphFun G ∅ x = true := by
    have ar := unchanged ha (fun h => Nat.lt_irrefl _ (source_lt_of_strict ao h)) x
    rw [show E = merge (some P) (ofList slot U.toList) from rfl,eval_merge,eval_list]
    simp only [eval,P,Expr.val,join,ite_true,Bool.and_eq_true,Finset.mem_toList]
    rw [←ar]
    constructor
    · rintro (aye|⟨t,ht,yes⟩)
      · exact cleanProduct x aye
      · have hr := (Finset.mem_sdiff.mp ht).1
        exact (cover x).mpr ⟨t,hr,(unchanged (valid t hr) (unaffected t ht) x).trans yes⟩
    · intro on
      obtain ⟨t,ht,yes⟩ := (cover x).mp on
      by_cases member : t∈A
      · exact Or.inl (absorb x ⟨t,member,yes⟩)
      · have hu : t∈U := Finset.mem_sdiff.mpr ⟨ht,member⟩
        exact Or.inr ⟨t,hu,(unchanged (valid t ht) (unaffected t hu) x).symm.trans yes⟩
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
    change e.size+1 = U.card+1 at bound
    simp [S] at cost
    have positive := Finset.card_pos.mpr many
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
