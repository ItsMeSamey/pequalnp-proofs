import T2SoleAndNamed
import T2ReaderConsumer

namespace T2SoleAndMinor
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2PhysicalMaximum
open T2SoleOrSplice T2CubeDeletion T2RawTopology T2NamedProducer T2SoleAndDirty T2ReaderConsumer
open private read_earlier from GateSurplus

theorem valid_tail (pre post : List Raw) (n : Nat) (ok : RawValid n (pre++post)) :
    RawValid (n+pre.length) post := by
  induction pre generalizing n with
  | nil => simpa using ok
  | cons a pre ih =>
    have rest := ih (n+1) ok.2.2
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

theorem sole_and_case {m : Nat} (two : 2≤m) (i : Fin (m+1)) (out p x y : Nat)
    (pre post : List Raw) (reads : (x=i.val ∧ y=p) ∨ (y=i.val ∧ x=p))
    (distinct : p ≠ i.val)
    (left : ∀ g ∈ pre.map native, i.val ∉ g.inputs)
    (right : ∀ g ∈ post.map native, i.val ∉ g.inputs)
    (ok : RawValid (m+1) (pre ++ (.and,x,y)::post))
    (obs : out<(m+1)+(pre ++ (.and,x,y)::post).length)
    (hc : Computes (m+1) (source (pre ++ (.and,x,y)::post) out)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧
      D.size+3 ≤ (pre ++ (.and,x,y)::post).length := by
  classical
  let n := m+1
  let C := source (pre ++ (.and,x,y)::post) out
  let addr := n+pre.length
  obtain ⟨dir,gEq⟩ : ∃ b : Bool, native (.and,x,y) = andGate b i.val p := by
    rcases reads with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  have ceq : C = ⟨pre.map native ++ andGate dir i.val p :: post.map native,out⟩ := by
    simp [C,source_eq,List.map_append,gEq]
  have nout : out ≠ i.val := by
    intro e
    have h := hc {i}
    have hh : C.eval (vector {i}) = true := by
      rw [ceq]
      change (run _ (vector {i})).getD out false = true
      rw [e,read_earlier _ _ _ (by simpa [vector] using i.isLt),vec_get]
      simp [i.isLt]
    have hn := h.mp hh
    simp at hn
  have rep : Computes n ⟨pre.map native ++ andGate dir i.val p :: post.map native,out⟩ :=
    ceq ▸ hc
  have low := other_internal n (by dsimp [n]; omega) i p out (pre.map native) (post.map native)
    dir distinct nout rep left right
  have rOK := valid_tail pre ((.and,x,y)::post) n ok
  have high : p<addr := by
    obtain ⟨xl,yl,_⟩ := rOK
    rcases reads with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact yl
    · exact xl
  obtain ⟨a,r,b,es,addrP⟩ := typed_split pre n p low high
  let many := embedded i (Finset.univ : Finset (Fin m))
  have olen : ∀ s : Finset (Fin (m+1)), (vector s).length=n := by intro s; simp [vector,n]
  have neqD : out ≠ addr := by
    intro e
    have yes : C.eval (vector many) = true := (hc many).mpr (by simpa [many,embedded_card] using two)
    have vx : (run (pre.map native) (vector many)).getD i.val false = false := by
      rw [read_earlier _ _ _ (by simpa [vector] using i.isLt),vec_get]
      simp [i.isLt,many,miss]
    have eq := named_value pre post (.and,x,y) (vector many)
    rw [olen] at eq
    have no : C.eval (vector many) = false := by
      rw [show C=⟨(pre ++ (.and,x,y)::post).map native,out⟩ by exact source_eq _ _,e]
      change (run ((pre ++ (.and,x,y)::post).map native) (vector many)).getD addr false = false
      rw [show addr=n+pre.length by rfl,eq]
      unfold computed
      rw [gEq]
      have vc : (run (pre.map native) (vector many))[i.val]?.getD false = false := by
        simpa only [List.getD_eq_getElem?_getD] using vx
      cases dir <;> simp [andGate,val,binary,gateOp,GateOp.eval,vc]
    simp_all
  let j := i.succAbove (⟨0,by omega⟩ : Fin m)
  have ji : j ≠ i := Fin.succAbove_ne _ _
  let l := vector {j}
  let h := vector (insert i {j})
  have diff : C.eval l ≠ C.eval h := by
    intro e
    have yes : C.eval h = true := (hc _).mpr (by simp [Finset.card_insert_of_notMem,ji.symm])
    have bad := (hc {j}).mp (e.trans yes)
    simp at bad
  have lr : T2RawIsolation.AgreeOff i.val l h := off_insert {j} i
  have ch : C = ⟨pre.map native ++ native (.and,x,y) :: post.map native,out⟩ := by simpa [gEq] using ceq
  rw [ch] at diff
  have abs : (run (pre.map native) h).length=addr := by simp [h,vector,addr,n,run_size]
  obtain ⟨g,mem,ref⟩ := exists_consumer (pre.map native) (post.map native) (native (.and,x,y))
    lr nout left right (by simpa [abs] using neqD) diff
  obtain ⟨rH,memH,rfl⟩ := List.mem_map.mp mem
  obtain ⟨oh,u,v⟩ := rH
  obtain ⟨c,d,esH⟩ := List.append_of_mem memH
  have edge : u=addr ∨ v=addr := by simpa [abs,native,binary,eq_comm] using ref
  subst pre
  subst post
  simp only [List.append_assoc,List.cons_append] at ok obs hc ⊢
  apply named_syntactic two i out a b c d r x y u v oh
  · have e : (m+1)+a.length=p := addrP
    simpa only [e] using reads
  · exact edge
  · exact left
  · exact right
  · exact nout
  · simpa [List.append_assoc] using ok
  · simpa [List.append_assoc] using obs
  · simpa [List.append_assoc] using hc

#print axioms sole_and_case
end T2SoleAndMinor
