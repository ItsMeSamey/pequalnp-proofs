import Q0ClauseRegion
import Q1PureBase

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0ReaderDeps Q0
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private def rawGood (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  rawKind n C w ∧ ∀ x : Fin n → Bool, S90.val C (List.ofFn x) w = true ↔
    ∃ i ∈ orIn n C w, x i = true

private theorem rawGood_pin (ao : IsAO2 n C) (tf : PEqualNP.TopForm.TopForm G C)
    (cleanReaders : NoDirtyOr G C) {j w : ℕ} (hj : j < C.gates.length)
    (andj : (gateAt C j).op = GateOp.and) (pin : w ∈ (gateAt C j).inputs)
    (kind : rawKind n C w) : rawGood n C w := by
  refine ⟨kind, fun x => ⟨?_, ?_⟩⟩
  · intro hv
    obtain ⟨v,reach,hv',hi | ⟨k,hk,rfl,hor⟩⟩ := S90.or_trace (n := n) (by simp) w hv
    · let i : Fin n := ⟨v,hi⟩
      refine ⟨i,S90.reach_mem_orIn i reach,?_⟩
      simpa only [← S90.val_ofFn C x i] using hv'
    · exfalso
      have hand := (ao.1 _ (S90.gateAt_mem hk)).resolve_right hor
      have bad : ¬ BelowF G C k := fun hb => tf k hk j hj hand hb andj
        (S90.operand_cone hj pin (ao.2.1 j hj w pin) reach)
      have dirty := (S4183.junk_iff G C k).mpr ⟨hk,hand,bad⟩
      rcases Relation.ReflTransGen.cases_tail reach with he | ⟨_,_,step⟩
      · rcases kind with h | ⟨k',_,h',op⟩
        · omega
        · have eq : k'=k := by omega
          subst k'
          exact hor op
      · obtain ⟨r,hr,_,hop,hin,_⟩ := step
        exact cleanReaders dirty hr hin hop
  · rintro ⟨i,hi,hx⟩
    exact S90.reach_var_val x w i (S90.mem_orIn_reach i hi) hx

theorem routed_frontier (ao : IsAO2 n C) (tf : PEqualNP.TopForm.TopForm G C)
    (cleanReaders : NoDirtyOr G C) {H : ℕ} (hc : H ∈ centreless G C) :
    ∃ S : Finset ℕ, (S.image (orIn n C)).card ≤ (routedJunk n G C H).card + 2 ∧
      (∀ x, gateVal n C H x = true ↔ ∀ A ∈ S.image (orIn n C), ∃ i ∈ A, x i = true) ∧
      ∀ w ∈ S, rawKind n C w := by
  classical
  let D := (routedJunk n G C H).filter (· < H)
  let js := H :: D.sort (· ≥ ·)
  have hjs (j : ℕ) : j ∈ js ↔ j = H ∨ j ∈ routedJunk n G C H ∧ j < H := by
    simp [js,D]
  have hiH : H ∈ tops G C := (Finset.mem_filter.mp hc).1
  have topH := Finset.mem_filter.mp hiH
  have selected {j} (hj : j ∈ js) :
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      j ≤ H ∧ DirtyRoute n G C j H := by
    rcases (hjs j).mp hj with rfl | ⟨hd,lt⟩
    · exact ⟨Finset.mem_range.mp topH.1,topH.2.1,le_rfl,.stop hc⟩
    · obtain ⟨hJ,route⟩ := mem_routedJunk.mp hd
      obtain ⟨hk,ha,_⟩ := (S4183.junk_iff G C j).mp hJ
      exact ⟨hk,ha,lt.le,route⟩
  have operands {j} (hj : j ∈ js) : (gateAt C j).inputs = [opnd C j 0,opnd C j 1] := by
    obtain ⟨a,b,e⟩ := List.length_eq_two.mp (ao.2.2 _ (S90.gateAt_mem (selected hj).1))
    simp [opnd,e]
  have pinCover : ∀ j ∈ js, ∀ b : Fin 2, rawGood n C (opnd C j b) ∨
      ∃ k ∈ js, k < j ∧ opnd C j b = n+k := by
    intro j hj b
    obtain ⟨jlt,andj,jle,route⟩ := selected hj
    let w := opnd C j b
    have pin : w ∈ (gateAt C j).inputs := by
      rw [operands hj]; fin_cases b <;> simp [w]
    have lt := ao.2.1 j jlt w pin
    by_cases hw : w < n
    · exact Or.inl (rawGood_pin ao tf cleanReaders jlt andj pin (Or.inl hw))
    let k := w-n
    have e : w = n+k := by dsimp [k]; omega
    have kj : k < j := by omega
    have klt : k < C.gates.length := by omega
    by_cases hOR : (gateAt C k).op = GateOp.or
    · exact Or.inl (rawGood_pin ao tf cleanReaders jlt andj pin (Or.inr ⟨k,klt,e,hOR⟩))
    have ha := (ao.1 _ (S90.gateAt_mem klt)).resolve_right hOR
    have hin : n+k ∈ (gateAt C j).inputs := e ▸ pin
    have hb : ¬ BelowF G C k := fun h => tf k klt j jlt ha h andj
      ((S90.inCone_iff n C k j).mpr ⟨jlt,k,kj,hin,Or.inl rfl⟩)
    have hJ := (S4183.junk_iff G C k).mpr ⟨klt,ha,hb⟩
    have hn : k ∉ centreless G C := by
      intro h
      have hh : k ∈ tops G C := (Finset.mem_filter.mp h).1
      exact hb (Finset.mem_filter.mp hh).2.2
    have hr : j ∈ readers n C k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jlt,hin⟩
    have mem := (mem_routedJunk (n := n) (G := G) (C := C) (t := H) (d := k)).mpr
      ⟨hJ,.next hn ⟨hJ,hr⟩ route⟩
    exact Or.inr ⟨k,(hjs k).mpr (Or.inr ⟨mem,by omega⟩),kj,e⟩
  have desc : js.Pairwise (· > ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_,D.sortedGT_sort.pairwise⟩
    intro k hk
    have hD : k ∈ D := by simpa using hk
    exact (Finset.mem_filter.mp hD).2
  let S := clauseFrontier n C js {n+H}
  have raw : ∀ w ∈ S, rawGood n C w := by
    apply clauseFrontier_closed (rawGood n C) js desc pinCover
    intro w hw
    simp only [Finset.mem_singleton] at hw
    exact Or.inr ⟨H,List.mem_cons_self,hw⟩
  refine ⟨S, ?_, ?_, fun w hw => (raw w hw).1⟩
  · have hc₁ := Finset.card_image_le (s := S) (f := orIn n C)
    have hc₂ := clauseFrontier_card n C js {n+H}
    change S.card ≤ _ at hc₂
    simp [js] at hc₂
    have hc₃ : D.card ≤ (routedJunk n G C H).card := Finset.card_filter_le _ _
    omega
  · intro x
    let P := fun w => S90.val C (List.ofFn x) w = true
    have hp : ∀ j ∈ js, P (n+j) ↔ P (opnd C j 0) ∧ P (opnd C j 1) := by
      intro j hj
      obtain ⟨jlt,hjop,_,_⟩ := selected hj
      have eq := S90.val_and (C := C) (x := List.ofFn x) (n := n) (by simp) jlt hjop
      have l₀ := S4183.opnd_lt ao.2.2 ao.2.1 jlt (0 : Fin 2)
      have l₁ := S4183.opnd_lt ao.2.2 ao.2.1 jlt (1 : Fin 2)
      simpa [P, operands hj, l₀, l₁] using eq
    have he := clauseFrontier_semantics n C js P hp {n+H}
    simp at he
    change P (n+H) ↔ _
    rw [he]
    constructor
    · intro h A hm
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hm
      exact ((raw w hw).2 x).mp (h w hw)
    · intro h w hw
      exact ((raw w hw).2 x).mpr (h _ (Finset.mem_image_of_mem _ hw))

private theorem allTrue_wire (ao : IsAO2 n C) (w : ℕ) (hw : w < n+C.gates.length) :
    S90.val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h : w < n
    · exact S90.val_ofFn C _ ⟨w,h⟩
    let k := w-n
    have eq : w = n+k := by dsimp [k]; omega
    have hk : k < C.gates.length := by omega
    obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp (ao.2.2 _ (S90.gateAt_mem hk))
    have hv (i) (hi : i ∈ (gateAt C k).inputs) :
        i < n+k ∧ S90.val C (List.ofFn (fun _ : Fin n => true)) i = true := by
      have lt := ao.2.1 k hk i hi
      exact ⟨lt,ih i (by omega) (by omega)⟩
    rw [eq]
    rcases ao.1 _ (S90.gateAt_mem hk) with hand | hor
    · exact (S90.val_and (by simp) hk hand).mpr hv
    · have hp : p ∈ (gateAt C k).inputs := by simp [hpq]
      exact (S90.val_or (by simp) hk hor).mpr ⟨p,hp,hv p hp⟩

theorem routedJunk_pos (ao : IsAO2 n C) (tf : PEqualNP.TopForm.TopForm G C)
    (cleanReaders : NoDirtyOr G C) {H : ℕ} (hc : H ∈ centreless G C) :
    0 < (routedJunk n G C H).card := by
  have htop : H ∈ tops G C := (Finset.mem_filter.mp hc).1
  obtain ⟨hmem,andH,_⟩ := Finset.mem_filter.mp htop
  have hH := Finset.mem_range.mp hmem
  obtain ⟨b,empty⟩ : ∃ b : Fin 2, orIn n C (opnd C H b) = ∅ := by
    rcases (Finset.mem_filter.mp hc).2 with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  let w := opnd C H b
  have pin : w ∈ (gateAt C H).inputs := by
    obtain ⟨p,q,e⟩ := List.length_eq_two.mp (ao.2.2 _ (S90.gateAt_mem hH))
    fin_cases b <;> simp [w,opnd,e]
  have lt := ao.2.1 H hH w pin
  have notRaw : ¬ rawKind n C w := by
    intro kind
    obtain ⟨i,hi,_⟩ := ((rawGood_pin ao tf cleanReaders hH andH pin kind).2
      (fun _ => true)).mp (allTrue_wire ao w (by omega))
    change i ∈ orIn n C (opnd C H b) at hi
    rw [empty] at hi
    exact Finset.notMem_empty i hi
  have hn : n ≤ w := Nat.le_of_not_gt (fun hl => notRaw (Or.inl hl))
  let j := w-n
  have e : w = n+j := by dsimp [j]; omega
  have jH : j < H := by omega
  have jl : j < C.gates.length := by omega
  have hor : (gateAt C j).op ≠ GateOp.or := fun op => notRaw (Or.inr ⟨j,jl,e,op⟩)
  have hand := (ao.1 _ (S90.gateAt_mem jl)).resolve_right hor
  have hin : n+j ∈ (gateAt C H).inputs := e ▸ pin
  have hb : ¬ BelowF G C j := fun h => tf j jl H hH hand h andH
    ((S90.inCone_iff n C j H).mpr ⟨hH,j,jH,hin,Or.inl rfl⟩)
  have hj := (S4183.junk_iff G C j).mpr ⟨jl,hand,hb⟩
  have hnt : j ∉ centreless G C := by
    intro h
    have ht : j ∈ tops G C := (Finset.mem_filter.mp h).1
    exact hb (Finset.mem_filter.mp ht).2.2
  have hr : H ∈ readers n C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hH,hin⟩
  exact Finset.card_pos.mpr ⟨j,mem_routedJunk.mpr ⟨hj,.next hnt ⟨hj,hr⟩ (.stop hc)⟩⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
