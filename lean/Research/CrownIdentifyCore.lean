import Research.CrownProperOrReads

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell CrownDiagonalCharge

def isRawPair (g : Gate) (n : ℕ) : Prop :=
  ∃ i : Fin 12, orReads g n = {i.val,12+i.val}

noncomputable def compress (gs : List Gate) (rho : List ℕ) (n bad out : ℕ) : Circuit := by
  classical
  exact match gs with
  | [] => ⟨[],rho.getD out bad⟩
  | g::rest =>
    if h : isRawPair g rho.length then
      compress rest (rho ++ [h.choose.val]) n bad out
    else
      let d := compress rest (rho ++ [n]) (n+1) bad out
      ⟨⟨g.op,g.inputs.map (fun k => rho.getD k bad)⟩ :: d.gates,d.output⟩

noncomputable def pairCount (gs : List Gate) (m : ℕ) : ℕ := by
  classical
  exact match gs with
  | [] => 0
  | g::rest => (if isRawPair g m then 1 else 0) + pairCount rest (m+1)

theorem rawPair_isOr (g : Gate) (m : ℕ) (h : isRawPair g m) : isOrGate g = true := by
  obtain ⟨i,hi⟩ := h
  by_contra nf
  have mt : orReads g m = ∅ := by simp [orReads,nf]
  have mem : i.val ∈ orReads g m := by simp [hi]
  simp [mt] at mem

theorem compress_counts (gs : List Gate) (rho : List ℕ) (n bad out : ℕ) :
    (compress gs rho n bad out).size + pairCount gs rho.length = gs.length ∧
    ((compress gs rho n bad out).gates.filter isOrGate).length + pairCount gs rho.length =
      (gs.filter isOrGate).length := by
  classical
  induction gs generalizing rho n with
  | nil => simp [compress,pairCount,Circuit.size]
  | cons g gs ih =>
    by_cases h : isRawPair g rho.length
    · have t := ih (rho++[h.choose.val]) n
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at t
      have ho := rawPair_isOr g _ h
      simp only [compress,dite_eq_left h,pairCount,ite_eq_left h,List.filter_cons,ho,
        ↓reduceIte,List.length_cons]
      constructor <;> omega
    · have t := ih (rho++[n]) (n+1)
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at t
      dsimp only [Circuit.size] at t ⊢
      simp only [compress,dite_eq_right h,pairCount,ite_eq_right h,Nat.zero_add,List.length_cons]
      have same : isOrGate ⟨g.op,g.inputs.map (fun k => rho.getD k bad)⟩ = isOrGate g := rfl
      cases ho : isOrGate g <;> simp only [List.filter_cons,same,ho,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> omega

theorem compress_mono (gs : List Gate) (rho : List ℕ) (n bad out : ℕ)
    (mono : Monotone2 ⟨gs,out⟩) : Monotone2 (compress gs rho n bad out) := by
  classical
  induction gs generalizing rho n with
  | nil => simp [compress,Monotone2]
  | cons g gs ih =>
    have tail : Monotone2 ⟨gs,out⟩ := fun b hb => mono b (List.mem_cons_of_mem _ hb)
    by_cases h : isRawPair g rho.length
    · simpa only [compress,dite_eq_left h] using ih (rho++[h.choose.val]) n tail
    · intro a ha
      simp only [compress,dite_eq_right h,List.mem_cons] at ha
      rcases ha with rfl | ht
      · simpa only [List.length_map] using mono g (List.mem_cons_self ..)
      · exact ih (rho++[n]) (n+1) tail a ht

def initialMap : List ℕ := List.range 12 ++ List.range 12

noncomputable def foldCrown (C : Circuit) : Circuit := compress C.gates initialMap 12 (12+C.size) C.output

theorem foldCrown_counts (C : Circuit) :
    (foldCrown C).size + pairCount C.gates 24 = C.size ∧
    ((foldCrown C).gates.filter isOrGate).length + pairCount C.gates 24 = (C.gates.filter isOrGate).length :=
  compress_counts C.gates initialMap 12 (12+C.size) C.output

end PEqualNP.Research.CrownIdentify
