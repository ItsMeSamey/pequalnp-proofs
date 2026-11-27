import DDIndexedSem
import DDIndexedTail
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q0.Factor Q1Double S4183.S98

private theorem take_slot {n k w : ℕ} {C : Circuit} {cuts : Cuts} (ao : IsAO2 n C)
    (hk : k ≤ C.gates.length) (valid : w < n+k) {f : Signal n}
    (slot : physicalSlot n C cuts k w = some f)
    (pack : Pack n) (hg : pack.gates = (build n C cuts k).gates) :
    ∃ (o : Origin) (v : pack.Wire), ref (build n C cuts k) w = some (o,v.val) ∧ ∀ x, pack.val v x = f x := by
  have present := shape C cuts ao k hk w valid
  rw [slot] at present
  cases e : ref (build n C cuts k) w with
  | none => simp [e] at present
  | some a =>
    rcases a with ⟨o,i⟩
    let v : pack.Wire := ⟨i,by rw [hg];exact ref_bound e⟩
    refine ⟨o,v,rfl,?_⟩
    intro x
    have h := slot_value C cuts ao hk x k le_rfl w valid
    rw [e,slot] at h
    change (Circuit.wires ⟨pack.gates,0⟩ (List.ofFn x)).getD i false = f x
    rw [hg]
    exact h

/-- The emitted circuit literally contains the indexed original prefix followed by
two conjunctions using the caller's original wire refs, including bypass aliases. -/
theorem actual_split {n k : ℕ} (C : Circuit) (cuts : Cuts) (ao : IsAO2 n C)
    (hk : k ≤ C.gates.length) (wa wb ww : Fin (n+k))
    (a b g : Signal n) (other : List (Signal n))
    (ha : physicalSlot n C cuts k wa = some a)
    (hb : physicalSlot n C cuts k wb = some b)
    (hg : physicalSlot n C cuts k ww = some g)
    (others : ∀ f ∈ other, ∃ u : Fin (n+k), physicalSlot n C cuts k u = some f)
    (cost : expense (seed n) (rows n C cuts k) + 2 + other.length ≤ C.size)
    (agree : other.foldl (join false) (join true (join false a b) g) = circuitFun n C) :
    ∃ (D : Circuit) (A B G : Origin × ℕ) (suffix : List Gate),
      ref (build n C cuts k) wa = some A ∧ ref (build n C cuts k) wb = some B ∧
      ref (build n C cuts k) ww = some G ∧
      D.gates = (build n C cuts k).gates ++ (⟨.and,[A.2,G.2]⟩ :: ⟨.and,[B.2,G.2]⟩ :: suffix) ∧
      IsAO2 n D ∧ D.size ≤ C.size+1 ∧
      wireVal n D (n+rank n C cuts k) = join true a g ∧
      wireVal n D (n+(rank n C cuts k+1)) = join true b g ∧ circuitFun n D = circuitFun n C := by
  obtain ⟨p,he⟩ := pack_exists C cuts ao k hk
  obtain ⟨oa,va,ra,sa⟩ := take_slot ao hk wa.isLt ha p he
  obtain ⟨ob,vb,rb,sb⟩ := take_slot ao hk wb.isLt hb p he
  obtain ⟨og,vg,rg,sg⟩ := take_slot ao hk ww.isLt hg p he
  have rest (f) (hf : f ∈ other) : Available p f := by
    obtain ⟨u,hu⟩ := others f hf
    obtain ⟨_,v,_,h⟩ := take_slot ao hk u.isLt hu p he
    exact ⟨v,h⟩
  obtain ⟨D,hD,⟨suffix,rowsD⟩,sz,pa,pb,out⟩ := split_pack p a b g other va vb vg sa sb sg rest
  have leq : p.gates.length = rank n C cuts k := congrArg List.length he
  rw [leq] at sz pa pb
  have kcost := rank_expense C cuts ao k hk
  refine ⟨D,(oa,va.val),(ob,vb.val),(og,vg.val),suffix,ra,rb,rg,?_,hD,by omega,pa,pb,out.trans agree⟩
  exact rowsD.trans (congrArg (fun gs => gs ++ (⟨.and,[va.val,vg.val]⟩ :: ⟨.and,[vb.val,vg.val]⟩ :: suffix)) he)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
