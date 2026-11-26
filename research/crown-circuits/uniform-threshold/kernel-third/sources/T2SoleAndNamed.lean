import T2SoleAndMinor

namespace T2SoleAndMinor
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2PhysicalMaximum
open T2SoleOrSplice T2CubeDeletion T2RawTopology T2NamedProducer T2SoleAndDirty

theorem named_syntactic {m : Nat} (two : 2≤m) (i : Fin (m+1)) (out : Nat)
    (a b c d : List Raw) (p : Raw) (x y u v : Nat) (oh : Op)
    (reads : (x=i.val ∧ y=(m+1)+a.length) ∨ (y=i.val ∧ x=(m+1)+a.length))
    (edge : u=(m+1)+(a ++ p::b).length ∨ v=(m+1)+(a ++ p::b).length)
    (left : ∀ g ∈ (a ++ p::b).map native, i.val ∉ g.inputs)
    (right : ∀ g ∈ (c ++ (oh,u,v)::d).map native, i.val ∉ g.inputs)
    (nout : out ≠ i.val)
    (ok : RawValid (m+1) (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))))
    (obs : out<(m+1)+(a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))).length)
    (hc : Computes (m+1) (source (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))) out)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧
      D.size+3 ≤ (a ++ p::(b ++ (.and,x,y)::(c ++ (oh,u,v)::d))).length := by
  have raw : x=i.val ∨ y=i.val := reads.imp And.left And.left
  apply named_minor two i out a b c d p x y u v oh raw edge ok obs hc
  intro s sn
  let j := (m+1)+a.length
  have ord : j ≠ i.val := by have := i.isLt; dsimp [j]; omega
  obtain ⟨dir,eg⟩ : ∃ dir : Bool, native (.and,x,y) = andGate dir i.val j := by
    rcases reads with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  have computes : Computes (m+1)
      ⟨(a ++ p::b).map native ++ andGate dir i.val j :: (c ++ (oh,u,v)::d).map native,out⟩ := by
    rw [←eg]
    simpa only [source_eq,List.map_append,List.map_cons,List.append_assoc,List.cons_append] using hc
  have nz : (embedded i s).Nonempty := by
    apply Finset.card_pos.mp
    rw [embedded_card]
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr sn)
  have hit := and_nonempty (m+1) i (embedded i s) nz (miss i s) j out _ _ dir ord nout computes left right
  have eq := named_value a b p (vector (embedded i s))
  have len : (vector (embedded i s)).length=m+1 := by simp [vector]
  rw [len] at eq
  exact eq.symm.trans hit

#print axioms named_syntactic
end T2SoleAndMinor
