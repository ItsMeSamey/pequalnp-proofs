import Q0Clauses
import Q0Routes

namespace PEqualNP.Outside.L_meta_4186_aux.Q0
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0ReaderDeps
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def rawKind (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  w < n ∨ ∃ k < C.gates.length, w = n+k ∧ (gateAt C k).op = GateOp.or

private def rawGood (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  rawKind n C w ∧ ∀ x : Fin n → Bool, S90.val C (List.ofFn x) w = true ↔
    ∃ i ∈ orIn n C w, x i = true

private theorem rawGood_pin (ao : IsAO2 n C) (tf : PEqualNP.TopForm.TopForm G C)
    (q : (orN G C \ lam G C).card = 0) {j w : ℕ} (hj : j < C.gates.length)
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
        exact dirty_reader_not_or ao q dirty hr hin hop
  · rintro ⟨i,hi,hx⟩
    exact S90.reach_var_val x w i (S90.mem_orIn_reach i hi) hx

theorem routed_frontier (ao : IsAO2 n C) (tf : PEqualNP.TopForm.TopForm G C)
    (q : (orN G C \ lam G C).card = 0) {H : ℕ} (hc : H ∈ centreless G C) :
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
    · exact Or.inl (rawGood_pin ao tf q jlt andj pin (Or.inl hw))
    let k := w-n
    have e : w = n+k := by dsimp [k]; omega
    have kj : k < j := by omega
    have klt : k < C.gates.length := by omega
    by_cases hOR : (gateAt C k).op = GateOp.or
    · exact Or.inl (rawGood_pin ao tf q jlt andj pin (Or.inr ⟨k,klt,e,hOR⟩))
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
end PEqualNP.Outside.L_meta_4186_aux.Q0
