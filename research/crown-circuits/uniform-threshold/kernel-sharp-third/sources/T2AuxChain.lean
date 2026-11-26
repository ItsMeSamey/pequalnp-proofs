import T2AndChain
import T2PhysicalOverride

namespace T2AuxChain
open ResidualSurplus T2PhysicalOverride

theorem debit (n i : Nat) (ts : List Tag) (a b c d : List Raw) (p : Raw)
    (x y u v : Nat) (oh : Op) (len : ts.length=n+1)
    (aux : tagRead ts 0 = some true) (ib : i<n) (pin : tagRead ts (i+1) = some false)
    (raw : x=i ∨ y=i) (edge : u=n+(a ++ p::b).length ∨ v=n+(a ++ p::b).length) :
    3 ≤ (closedRows (rawEdited a (b ++ (.and,x,y)::(c ++ (oh,u,v)::d)) p.1) ts).length := by
  let ap := a.map rawShift
  let bp := ap ++ (p.1,0,0)::b.map rawShift
  let cp := bp ++ (.and,x+1,y+1)::c.map rawShift
  apply and_chain_three _ ts (i+1) ap bp cp
    ((b ++ (.and,x,y)::(c ++ (oh,u,v)::d)).map rawShift)
    ((c ++ (oh,u,v)::d).map rawShift) (d.map rawShift) p.1 oh (x+1) (y+1) (u+1) (v+1)
  · rfl
  · simp [rawEdited,ap,bp,rawShift,List.append_assoc]
  · simp [rawEdited,ap,bp,cp,rawShift,List.append_assoc]
  · simp [bp] <;> omega
  · simp [cp] <;> omega
  · omega
  · exact aux
  · omega
  · exact pin
  · omega
  · simp only [List.length_append,List.length_cons,List.length_map] at edge
    simp only [bp,ap,List.length_append,List.length_cons,List.length_map,len]
    omega

#print axioms debit
end T2AuxChain
