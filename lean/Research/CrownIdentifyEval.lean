import Research.CrownIdentifyCore

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell CrownDiagonalCharge

private theorem old_index {α : Type*} (l : List α) (a d : α) (k : ℕ) (lt : k < l.length) :
    (l++[a]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]

private theorem new_index {α : Type*} (l : List α) (a d : α) :
    (l++[a]).getD l.length d = a := by simp [List.getD_eq_getElem?_getD]

private def rawIds (rho : List ℕ) (bad : ℕ) : Prop :=
  ∀ i : Fin 12, rho.getD i.val bad = i.val ∧ rho.getD (12+i.val) bad = i.val

private theorem rawIds_append (rho : List ℕ) (a bad : ℕ) (len : 24 ≤ rho.length)
    (raw : rawIds rho bad) : rawIds (rho++[a]) bad := by
  intro i
  rw [old_index rho a bad i.val (by omega),old_index rho a bad (12+i.val) (by omega)]
  exact raw i

private def matchAt (rho : List ℕ) (x y : List Bool) (bad : ℕ) : Prop :=
  ∀ k < rho.length, x.getD k false = y.getD (rho.getD k bad) false

private theorem mapped_bound (rho : List ℕ) (low : ∀ k ∈ rho, k < n) (i bad : ℕ) (hi : i < rho.length) :
    rho.getD i bad < n := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact low _ (List.getElem_mem hi)

private theorem matchAll (rho : List ℕ) (x y : List Bool) (bad : ℕ)
    (lx : rho.length = x.length) (bylen : y.length ≤ bad) (m : matchAt rho x y bad) (i : ℕ) :
    x.getD i false = y.getD (rho.getD i bad) false := by
  by_cases hi : i < rho.length
  · exact m i hi
  · rw [getD_missing (by omega : x.length ≤ i)]
    have q : rho.getD i bad = bad := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    rw [q,getD_missing bylen]

private theorem match_append (rho : List ℕ) (x y y' : List Bool) (bad a : ℕ) (b : Bool)
    (lx : rho.length = x.length) (low : ∀ q ∈ rho, q < y.length) (m : matchAt rho x y bad)
    (old : ∀ q < y.length, y'.getD q false = y.getD q false) (val : b = y'.getD a false) :
    matchAt (rho++[a]) (x++[b]) y' bad := by
  intro k hk
  by_cases lt : k < rho.length
  · rw [old_index _ _ _ _ (by omega : k < x.length),old_index _ _ _ _ lt,
      old _ (mapped_bound rho low k bad lt)]
    exact m k lt
  · have eq : k = rho.length := by simp only [List.length_append,List.length_cons,List.length_nil] at hk; omega
    subst k
    rw [new_index,show (x++[b]).getD rho.length false = b by rw [lx,new_index]]
    exact val

private theorem paired_value (g : Gate) (x y : List Bool) (rho : List ℕ) (bad : ℕ)
    (len : rho.length = x.length) (cap : y.length ≤ bad) (m : matchAt rho x y bad)
    (raw : rawIds rho bad) (h : isRawPair g rho.length) :
    gateBool g x = y.getD h.choose.val false := by
  let i := h.choose
  have rp : orReads g x.length = {i.val,12+i.val} := len ▸ h.choose_spec
  have ev := or_value_on_reads g x (rawPair_isOr g rho.length h)
  have e1 := matchAll rho x y bad len cap m i.val
  have e2 := matchAll rho x y bad len cap m (12+i.val)
  rw [(raw i).1] at e1
  rw [(raw i).2] at e2
  apply Bool.eq_iff_iff.mpr
  rw [ev,rp]
  constructor
  · rintro ⟨k,hk,hv⟩
    rcases Finset.mem_insert.mp hk with eq | hs
    · exact e1.symm.trans (eq ▸ hv)
    · exact e2.symm.trans ((Finset.mem_singleton.mp hs) ▸ hv)
  · intro hy
    exact ⟨i.val,Finset.mem_insert_self ..,e1.trans hy⟩

theorem compress_eval (gs : List Gate) (rho : List ℕ) (x y : List Bool) (bad out : ℕ)
    (lx : rho.length = x.length) (orig : 24 ≤ rho.length) (small : 12 ≤ y.length)
    (cap : y.length+gs.length ≤ bad) (low : ∀ q ∈ rho, q < y.length)
    (raw : rawIds rho bad) (matched : matchAt rho x y bad) :
    (compress gs rho y.length bad out).eval y = (Circuit.mk gs out).eval x := by
  classical
  induction gs generalizing rho x y with
  | nil => exact (matchAll rho x y bad lx (by simpa using cap) matched out).symm
  | cons g gs ih =>
    by_cases h : isRawPair g rho.length
    · rw [compress,dite_eq_left h]
      change _ = (Circuit.mk gs out).eval (advance g x)
      apply ih (rho++[h.choose.val]) (advance g x) y (by simp [advance_len,lx]) (by simp; omega) small
        (by simp only [List.length_cons] at cap; omega)
      · intro q hq
        rcases List.mem_append.mp hq with old | tail
        · exact low q old
        · simp only [List.mem_singleton] at tail
          rw [tail]
          omega
      · exact rawIds_append _ _ _ orig raw
      · exact match_append rho x y y bad h.choose.val (gateBool g x) lx low matched (fun _ _ => rfl)
          (paired_value g x y rho bad lx (by omega) matched raw h)
    · let t : Gate := ⟨g.op,g.inputs.map (fun k => rho.getD k bad)⟩
      let d := compress gs (rho++[y.length]) (y.length+1) bad out
      change ((compress (g::gs) rho y.length bad out).eval y) = (Circuit.mk gs out).eval (advance g x)
      rw [compress,dite_eq_right h]
      change d.eval (advance t y) = _
      have eq : gateBool g x = gateBool t y := by
        simp only [gateBool,t,List.map_map]
        congr 1
        apply List.map_congr_left
        intro k _
        exact matchAll rho x y bad lx (by omega) matched k
      dsimp only [d]
      rw [←advance_len t y]
      apply ih (rho++[y.length]) (advance g x) (advance t y) (by simp [advance_len,lx])
        (by simp; omega) (by rw [advance_len];omega) (by rw [advance_len]; simp only [List.length_cons] at cap; omega)
      · intro q hq
        rw [advance_len]
        rcases List.mem_append.mp hq with old | tail
        · exact Nat.lt_succ_of_lt (low q old)
        · simp only [List.mem_singleton] at tail
          omega
      · exact rawIds_append _ _ _ orig raw
      · apply match_append rho x y (advance t y) bad y.length (gateBool g x) lx low matched
        · exact getD_advance_lt t y
        · exact eq.trans (getD_advance_eq t y).symm

theorem foldCrown_eval (C : Circuit) (w : List Bool) (len : w.length = 12) :
    (foldCrown C).eval w = C.eval (w++w) := by
  let bad := 12+C.size
  have raw : rawIds initialMap bad := by
    intro i
    constructor
    · simp [initialMap,List.getD_eq_getElem?_getD,List.getElem?_append_left,i.isLt]
    · simp [initialMap,List.getD_eq_getElem?_getD,List.getElem?_append_right]
  have hh := compress_eval C.gates initialMap (w++w) w bad C.output
    (by simp [initialMap,len]) (by decide) (by omega) (by simp [len,bad,Circuit.size])
    (by intro q hq; simp [initialMap] at hq; omega) raw
  change (compress C.gates initialMap 12 bad C.output).eval w = C.eval (w++w)
  rw [←len]
  apply hh
  intro k hk
  have kb : k < 24 := hk
  by_cases lt : k < 12
  · rw [(raw ⟨k,lt⟩).1]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left,len,lt]
  · let i : Fin 12 := ⟨k-12,by omega⟩
    have eq : 12+i.val = k := by dsimp [i]; omega
    have rm := (raw i).2
    rw [eq] at rm
    rw [rm]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show w.length ≤ k by omega),len,i]

end PEqualNP.Research.CrownIdentify
