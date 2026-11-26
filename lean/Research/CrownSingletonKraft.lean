import Research.CrownIndexedOrReads
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

def singleInput {n : ℕ} (i : Fin n) : List Bool := List.ofFn (fun j : Fin n => decide (j=i))

def singletonWeight {n : ℕ} (C : Circuit) (i : Fin n) : ℚ :=
  (1/2:ℚ)^((trueOrFlags C.gates (singleInput i)).count true)

private def mass {I : Type*} [Fintype I] (weight : I → ℚ) (f : I → Bool) : ℚ :=
  ∑ i, if f i then weight i else 0

private def bounded {I : Type*} [Fintype I] (z : List Bool) (x : I → List Bool) (weight : I → ℚ) : Prop :=
  ∀ a, z.getD a false = false → mass weight (fun i => (x i).getD a false) ≤ 1

private def discount {I : Type*} (g : Gate) (x : I → List Bool) (wt : I → ℚ) (i : I) : ℚ :=
  if isOrGate g && gateBool g (x i) then wt i / 2 else wt i

private theorem discount_le {I : Type*} (g : Gate) (x : I → List Bool) (wt : I → ℚ)
    (pos : ∀ i, 0 ≤ wt i) (i : I) : discount g x wt i ≤ wt i := by
  unfold discount
  split <;> linarith [pos i]

private theorem discount_pos {I : Type*} (g : Gate) (x : I → List Bool) (wt : I → ℚ)
    (pos : ∀ i, 0 ≤ wt i) (i : I) : 0 ≤ discount g x wt i := by
  unfold discount
  split <;> linarith [pos i]

private theorem bounded_gate {I : Type*} [Fintype I] (g : Gate) (z : List Bool) (x : I → List Bool)
    (wt : I → ℚ) (pos : ∀ i, 0 ≤ wt i) (inv : bounded z x wt)
    (hop : g.op = .and ∨ g.op = .or) (fanin : g.inputs.length ≤ 2) (off : gateBool g z = false) :
    mass (discount g x wt) (fun i => gateBool g (x i)) ≤ 1 := by
  classical
  rcases hop with ha | ho
  · have ex : ∃ a ∈ g.inputs, z.getD a false = false := by simpa [gateBool,ha,GateOp.eval] using off
    obtain ⟨a,am,af⟩ := ex
    refine le_trans ?_ (inv a af)
    apply Finset.sum_le_sum
    intro i _
    by_cases on : gateBool g (x i) = true
    · have all : ∀ b ∈ g.inputs, (x i).getD b false = true := by simpa [gateBool,ha,GateOp.eval] using on
      simpa only [on,all a am,↓reduceIte] using discount_le g x wt pos i
    · simp only [ite_eq_right on]
      split <;> simp [pos]
  · let R := g.inputs.toFinset
    have fro : ∀ a ∈ g.inputs, z.getD a false = false := by simpa [gateBool,ho,GateOp.eval] using off
    have paid (i : I) : (if gateBool g (x i) then wt i else 0) ≤
        ∑ a ∈ R, if (x i).getD a false then wt i else 0 := by
      by_cases hit : gateBool g (x i) = true
      · have ex : ∃ a ∈ g.inputs, (x i).getD a false = true := by simpa [gateBool,ho,GateOp.eval] using hit
        obtain ⟨a,am,yes⟩ := ex
        have h := Finset.single_le_sum (s := R) (f := fun b => if (x i).getD b false then wt i else 0)
          (fun b _ => by split <;> simp [pos]) (List.mem_toFinset.mpr am)
        simpa only [yes,hit,↓reduceIte] using h
      · simp only [ite_eq_right hit]
        apply Finset.sum_nonneg
        intro a _
        split <;> simp [pos]
    have base : mass wt (fun i => gateBool g (x i)) ≤ 2 := by
      calc
        _ ≤ ∑ i, ∑ a ∈ R, if (x i).getD a false then wt i else 0 := Finset.sum_le_sum (fun i _ => paid i)
        _ = ∑ a ∈ R, mass wt (fun i => (x i).getD a false) := Finset.sum_comm
        _ ≤ ∑ _a ∈ R, (1:ℚ) := Finset.sum_le_sum (fun a am => inv a (fro a (List.mem_toFinset.mp am)))
        _ ≤ 2 := by
          have cap : R.card ≤ 2 := (List.toFinset_card_le g.inputs).trans fanin
          simpa using (show (R.card:ℚ) ≤ 2 by exact_mod_cast cap)
    have eq : mass (discount g x wt) (fun i => gateBool g (x i)) = mass wt (fun i => gateBool g (x i)) / 2 := by
      unfold mass
      rw [div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      cases e : gateBool g (x i) <;> simp [discount,isOrGate,ho,e,div_eq_mul_inv]
    linarith

private theorem bounded_advance {I : Type*} [Fintype I] (g : Gate) (z : List Bool) (x : I → List Bool)
    (len : ∀ i, (x i).length = z.length) (wt : I → ℚ) (pos : ∀ i, 0 ≤ wt i) (inv : bounded z x wt)
    (hop : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2) :
    bounded (advance g z) (fun i => advance g (x i)) (discount g x wt) := by
  intro a off
  by_cases lt : a < z.length
  · rw [getD_advance_lt _ _ _ lt] at off
    refine le_trans ?_ (inv a off)
    apply Finset.sum_le_sum
    intro i _
    change (if (advance g (x i)).getD a false then discount g x wt i else 0) ≤
      (if (x i).getD a false then wt i else 0)
    rw [getD_advance_lt g (x i) a (by rw [len i]; exact lt)]
    split <;> first | exact discount_le g x wt pos i | exact le_rfl
  · by_cases eq : a = z.length
    · subst a
      rw [getD_advance_eq] at off
      have ev (i : I) : (advance g (x i)).getD z.length false = gateBool g (x i) := by
        rw [←len i,getD_advance_eq]
        rfl
      simpa only [ev] using bounded_gate g z x wt pos inv hop fan off
    · have ev (i : I) : (advance g (x i)).getD a false = false :=
        getD_missing (by rw [advance_len,len]; omega)
      simp only [mass,ev,Bool.false_eq_true,↓reduceIte,Finset.sum_const_zero,zero_le_one]

private theorem bounded_run {I : Type*} [Fintype I] (gs : List Gate) (z : List Bool) (x : I → List Bool)
    (len : ∀ i, (x i).length = z.length) (wt : I → ℚ) (pos : ∀ i, 0 ≤ wt i) (inv : bounded z x wt)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    bounded ((Circuit.mk gs 0).wires z) (fun i => (Circuit.mk gs 0).wires (x i))
      (fun i => wt i * (1/2:ℚ)^((trueOrFlags gs (x i)).count true)) := by
  induction gs generalizing z x wt with
  | nil =>
    change bounded z x (fun i => wt i * (1/2:ℚ)^((trueOrFlags [] (x i)).count true))
    simpa only [trueOrFlags,List.count_nil,pow_zero,mul_one] using inv
  | cons g gs ih =>
    have hg := hm g (List.mem_cons_self ..)
    have next := ih (advance g z) (fun i => advance g (x i)) (fun i => by simp [advance_len,len])
      (discount g x wt) (discount_pos g x wt pos) (bounded_advance g z x len wt pos inv hg.1 hg.2)
      (fun a ha => hm a (List.mem_cons_of_mem _ ha))
    have ew : (fun i => wt i * (1/2:ℚ)^((trueOrFlags (g::gs) (x i)).count true)) =
        (fun i => discount g x wt i * (1/2:ℚ)^((trueOrFlags gs (advance g (x i))).count true)) := by
      funext i
      change wt i * (1/2:ℚ)^(((isOrGate g && gateBool g (x i)) :: trueOrFlags gs (advance g (x i))).count true) = _
      cases hb : isOrGate g && gateBool g (x i) <;> simp [discount,hb,pow_succ] <;> ring
    rw [ew]
    exact next

theorem singleton_weight_capacity {n : ℕ} (C : Circuit) (hm : Monotone2 C) (a : ℕ)
    (off : (C.wires (List.replicate n false)).getD a false = false) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (C.wires (singleInput i)).getD a false),
      singletonWeight C i ≤ 1 := by
  classical
  let z := List.replicate n false
  have init : bounded z (fun i : Fin n => singleInput i) (fun _ => 1) := by
    intro b _
    by_cases lt : b < n
    · simp [mass,singleInput,List.getD_eq_getElem?_getD,lt,eq_comm]
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    · simp [mass,singleInput,List.getD_eq_getElem?_getD,lt,eq_comm]
  have h := bounded_run C.gates z (fun i : Fin n => singleInput i)
    (fun i => by simp [singleInput,z]) (fun _ => 1) (fun _ => by norm_num) init hm a off
  rw [Finset.sum_filter]
  have hw (i : Fin n) : (Circuit.mk C.gates 0).wires (singleInput i) = C.wires (singleInput i) := rfl
  simpa only [mass,one_mul,singletonWeight,hw] using h

end PEqualNP.Research.MissingCell
