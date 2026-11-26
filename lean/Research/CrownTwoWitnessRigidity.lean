import Research.CrownMaskedRigidity

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- If the same masked conjunction is true at two witnesses, its only
relevant raw inputs are the coordinates true at both witnesses. -/
theorem masked_joint_rigidity (gs : List Gate) (u v x y : List Bool)
    (lv : v.length = u.length) (lx : x.length = u.length) (ly : y.length = u.length)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (agree : ∀ a, u.getD a false = true → v.getD a false = true → x.getD a false = y.getD a false)
    (a : ℕ) (wu : (maskedWires gs u).getD a false = true) (wv : (maskedWires gs v).getD a false = true) :
    (maskedWires gs x).getD a false = ((Circuit.mk gs 0).wires y).getD a false := by
  induction gs generalizing u v x y with
  | nil => exact agree a wu wv
  | cons g gs ih =>
    apply ih (advance (maskGate g) u) (advance (maskGate g) v) (advance (maskGate g) x) (advance g y)
      (by simp [advance_len,lv]) (by simp [advance_len,lx]) (by simp [advance_len,ly])
      (fun b h => mono b (List.mem_cons_of_mem _ h)) _ wu wv
    intro b
    by_cases lt : b < u.length
    · simpa only [getD_advance_lt _ _ _ lt,getD_advance_lt (maskGate g) v b (by omega),
        getD_advance_lt (maskGate g) x b (by omega),getD_advance_lt g y b (by omega)] using agree b
    · by_cases eq : b = u.length
      · subst b
        have ev := getD_advance_eq (maskGate g) v
        have ex := getD_advance_eq (maskGate g) x
        have ey := getD_advance_eq g y
        rw [lv] at ev
        rw [lx] at ex
        rw [ly] at ey
        rw [getD_advance_eq,ev,ex,ey]
        rcases mono g (List.mem_cons_self ..) with hand | hor
        · have same : maskGate g = g := by simp [maskGate,isOrGate,hand]
          rw [same]
          intro hu hv
          have au : ∀ t ∈ g.inputs, u.getD t false = true := by simpa [hand,GateOp.eval] using hu
          have av : ∀ t ∈ g.inputs, v.getD t false = true := by simpa [hand,GateOp.eval] using hv
          congr 1
          apply List.map_congr_left
          intro t ht
          exact agree t (au t ht) (av t ht)
        · simp [maskGate,isOrGate,hor,GateOp.eval]
      · rw [getD_missing (by rw [advance_len];omega : (advance (maskGate g) u).length ≤ b)]
        simp

theorem raw_oneEach_on {n : ℕ} (u v : Fin n) (k : ℕ) :
    (oneEach u v).getD k false = true ↔ k = u.val ∨ k = n + v.val := by
  by_cases h : k < n
  · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,h]
    constructor
    · intro e
      exact Or.inl (congrArg Fin.val e)
    · rintro (e|e)
      · exact Fin.ext e
      · omega
  · by_cases hb : k-n < n
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt h,hb]
      constructor
      · intro e
        have eq := congrArg Fin.val e
        simp at eq
        omega
      · rintro (e|e)
        · omega
        · apply Fin.ext
          simp only
          omega
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt h,hb]
      omega

private theorem singleton_meet (i u v : Fin 12) (ne : u ≠ v) :
    ∃ z < 24, ∀ k, (oneEach i i).getD k false = true → (oneEach u v).getD k false = true → k = z := by
  by_cases vi : v = i
  · refine ⟨12+i.val,by omega,?_⟩
    intro k hk hj
    rcases (raw_oneEach_on i i k).mp hk with a | b
    · rcases (raw_oneEach_on u v k).mp hj with c | d
      · exact False.elim (ne (Fin.ext (by omega)))
      · omega
    · exact b
  · refine ⟨i.val,by omega,?_⟩
    intro k hk hj
    rcases (raw_oneEach_on i i k).mp hk with a | b
    · exact a
    · rcases (raw_oneEach_on u v k).mp hj with c | d
      · omega
      · exact False.elim (vi (Fin.ext (by omega)))

theorem masked_trigger_raw_or_diagonal (C : Circuit) (hm : Monotone2 C) (a : ℕ) (i : Fin 12)
    (hit : (maskedWires C.gates (oneEach i i)).getD a false = true)
    (cold : (maskedWires C.gates (List.replicate 24 false)).getD a false = false)
    (u v : Fin 12) (ne : u ≠ v) (pos : (C.wires (oneEach u v)).getD a false = true) :
    ∃ z < 24, ∀ y : List Bool, y.length = 24 → (C.wires y).getD a false = y.getD z false := by
  let U := oneEach i i
  let V := oneEach u v
  let Z := List.replicate 24 false
  have lu : U.length = 24 := by simp [U,oneEach]
  have lv : V.length = U.length := by simp [U,V,oneEach]
  have lz : Z.length = U.length := by simp [Z,lu]
  have mono := fun g hg => (hm g hg).1
  have wv := (masked_true_wire_rigid C.gates U V lv mono a hit).trans pos
  obtain ⟨z,zl,only⟩ := singleton_meet i u v ne
  refine ⟨z,zl,?_⟩
  intro y yl
  have hy := yl.trans lu.symm
  cases flag : y.getD z false with
  | true =>
    have h := masked_joint_rigidity C.gates U V U y lv rfl hy mono
      (fun k uk vk => uk.trans ((only k uk vk) ▸ flag.symm)) a hit wv
    exact h.symm.trans hit
  | false =>
    have h := masked_joint_rigidity C.gates U V Z y lv lz hy mono
      (fun k uk vk => by
        rw [only k uk vk,flag]
        simp only [Z,List.getD_eq_getElem?_getD,List.getElem?_replicate,ite_eq_left zl,Option.getD_some]) a hit wv
    exact h.symm.trans cold

theorem masked_baseline_true_is_constant (C : Circuit) (hm : Monotone2 C) (a n : ℕ)
    (hit : (maskedWires C.gates (List.replicate n false)).getD a false = true)
    (y : List Bool) (ly : y.length = n) : (C.wires y).getD a false = true := by
  let z := List.replicate n false
  have no (k : ℕ) : z.getD k false = false := by
    by_cases h : k < n <;> simp [z,List.getD_eq_getElem?_getD,h]
  have eq := masked_joint_rigidity C.gates z z z y rfl rfl (by simp [z,ly])
    (fun g hg => (hm g hg).1)
    (fun k hk _ => False.elim (by rw [no k] at hk; contradiction)) a hit hit
  exact eq.symm.trans hit

end PEqualNP.Research.MissingCell
