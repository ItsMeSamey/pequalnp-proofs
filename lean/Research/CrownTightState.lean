import Research.CrownTightMass

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def wireSupport {n : ℕ} (gs : List Gate) (a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ((Circuit.mk gs 0).wires (singleInput i)).getD a false)

def tightWire (n : ℕ) (gs : List Gate) (a : ℕ) : Prop :=
  ((Circuit.mk gs 0).wires (List.replicate n false)).getD a false = false ∧
  (∑ i ∈ wireSupport (n:=n) gs a, singletonWeight (Circuit.mk gs 0) i) = 1

namespace TightStep

def cut (n : ℕ) (gs : List Gate) (g : Gate) : Finset (Fin n) :=
  Finset.univ.filter (fun i => isOrGate g && gateBool g ((Circuit.mk gs 0).wires (singleInput i)))

theorem flags_append (gs : List Gate) (g : Gate) (w : List Bool) :
    trueOrFlags (gs ++ [g]) w = trueOrFlags gs w ++ [isOrGate g && gateBool g ((Circuit.mk gs 0).wires w)] := by
  induction gs generalizing w with
  | nil => rfl
  | cons h hs ih =>
    change _ :: trueOrFlags (hs ++ [g]) (advance h w) = _ :: _
    rw [ih];rfl

theorem next_weight {n : ℕ} (gs : List Gate) (g : Gate) (i : Fin n) :
    singletonWeight (Circuit.mk (gs++[g]) 0) i =
      if i ∈ cut n gs g then singletonWeight (Circuit.mk gs 0) i / 2 else singletonWeight (Circuit.mk gs 0) i := by
  unfold singletonWeight
  rw [flags_append,List.count_append]
  have mem : i ∈ cut n gs g ↔ (isOrGate g && gateBool g ((Circuit.mk gs 0).wires (singleInput i))) = true :=
    by simp only [cut,Finset.mem_filter,Finset.mem_univ,true_and]
  cases h : isOrGate g && gateBool g ((Circuit.mk gs 0).wires (singleInput i)) with
  | false =>
    have no : i ∉ cut n gs g := fun hi => Bool.noConfusion (h.symm.trans (mem.mp hi))
    rw [ite_eq_right no]; simp
  | true =>
    rw [ite_eq_left (mem.mpr h)]; simp [pow_succ]; ring

theorem prefix_len (gs : List Gate) (w : List Bool) :
    ((Circuit.mk gs 0).wires w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).length = _
    rw [ih,advance_len,List.length_cons];omega

theorem next_val (gs : List Gate) (g : Gate) (w : List Bool) (a : ℕ) :
    ((Circuit.mk (gs++[g]) 0).wires w).getD a false =
      if a=w.length+gs.length then gateBool g ((Circuit.mk gs 0).wires w) else
      ((Circuit.mk gs 0).wires w).getD a false := by
  have eq : (Circuit.mk (gs++[g]) 0).wires w = advance g ((Circuit.mk gs 0).wires w) := by
    simp [Circuit.wires,List.foldl_append,advance]
  rw [eq,←prefix_len]
  let v := (Circuit.mk gs 0).wires w
  change (advance g v).getD a false = if a=v.length then gateBool g v else v.getD a false
  by_cases lt : a<v.length
  · rw [ite_eq_right (Nat.ne_of_lt lt),getD_advance_lt _ _ _ lt]
  · by_cases equal : a=v.length
    · subst a;rw [ite_eq_left rfl,getD_advance_eq];rfl
    · rw [ite_eq_right equal,getD_missing (by rw [advance_len];omega),getD_missing (by omega)]

def freshSupport {n : ℕ} (gs : List Gate) (g : Gate) : Finset (Fin n) :=
  Finset.univ.filter (fun i => gateBool g ((Circuit.mk gs 0).wires (singleInput i)))

theorem next_support {n : ℕ} (gs : List Gate) (g : Gate) (a : ℕ) :
    wireSupport (n:=n) (gs++[g]) a = if a=n+gs.length then freshSupport gs g else wireSupport gs a := by
  have len (i : Fin n) : (singleInput i).length = n := by simp [singleInput]
  by_cases h : a=n+gs.length
  · rw [ite_eq_left h]
    ext i
    simp only [wireSupport,freshSupport,Finset.mem_filter,Finset.mem_univ,true_and,next_val,len,h,ite_true]
  · rw [ite_eq_right h]
    ext i
    simp only [wireSupport,Finset.mem_filter,Finset.mem_univ,true_and,next_val,len,ite_eq_right h]

theorem weight_positive {n} (gs : List Gate) (i : Fin n) : 0 < singletonWeight (Circuit.mk gs 0) i := by
  unfold singletonWeight
  positivity

/-- A tight support is inherited from an old tight wire whose inputs were
unaffected by the discount, or is precisely the new OR's support. -/
theorem transfer {n : ℕ} (gs : List Gate) (g : Gate)
    (hm : Monotone2 (Circuit.mk gs 0)) (op : g.op = .and ∨ g.op = .or)
    (a : ℕ) (ht : tightWire n (gs++[g]) a) :
    wireSupport (n:=n) (gs++[g]) a = cut n gs g ∨
      ∃ p, tightWire n gs p ∧ wireSupport (n:=n) (gs++[g]) a = wireSupport gs p ∧
        Disjoint (wireSupport (n:=n) gs p) (cut n gs g) := by
  obtain ⟨off,full⟩ := ht
  rw [next_val,List.length_replicate] at off
  rw [next_support] at full ⊢
  by_cases idx : a=n+gs.length
  · rw [ite_eq_left idx] at off full ⊢
    rcases op with hand|hor
    · have none : cut n gs g = ∅ := by ext i; simp [cut,isOrGate,hand]
      have ex : ∃ p ∈ g.inputs, ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false := by
        simpa [gateBool,hand,GateOp.eval] using off
      obtain ⟨p,hp,cold⟩ := ex
      have sub : freshSupport (n:=n) gs g ⊆ wireSupport gs p := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have all : ∀ j ∈ g.inputs, ((Circuit.mk gs 0).wires (singleInput i)).getD j false = true := by
          simpa [gateBool,hand,GateOp.eval] using (Finset.mem_filter.mp hi).2
        exact all p hp
      simp only [next_weight,none,Finset.notMem_empty,ite_false] at full
      obtain ⟨eq,mass⟩ := tight_subset_rigidity _ _ _ (weight_positive gs) sub full
        (singleton_weight_capacity (Circuit.mk gs 0) hm p cold)
      exact Or.inr ⟨p,⟨cold,mass⟩,eq,by simp [none]⟩
    · left; ext i; simp [cut,freshSupport,isOrGate,hor]
  · rw [ite_eq_right idx] at off full ⊢
    simp only [next_weight] at full
    obtain ⟨dis,mass⟩ := tight_discount_rigidity _ _ _ (weight_positive gs)
      (singleton_weight_capacity (Circuit.mk gs 0) hm a off) full
    exact Or.inr ⟨a,⟨off,mass⟩,rfl,dis⟩

end TightStep

open TightStep
/-- In a monotone fan-in-two circuit the cold wires attaining singleton
Kraft mass one form disjoint blocks, allowing repetitions of a block. -/
theorem tight_supports_equal_or_disjoint (n : ℕ) (gs : List Gate)
    (hm : Monotone2 (Circuit.mk gs 0)) (a b : ℕ)
    (ta : tightWire n gs a) (tb : tightWire n gs b) :
    wireSupport (n:=n) gs a = wireSupport gs b ∨
      Disjoint (wireSupport (n:=n) gs a) (wireSupport gs b) := by
  induction gs using List.reverseRecOn generalizing a b with
  | nil =>
    by_cases id : a = b
    · subst b;exact Or.inl rfl
    · right;apply Finset.disjoint_left.mpr
      intro t u v
      have at_raw (j : ℕ) (h : t ∈ wireSupport [] j) : j = t.val := by
        have hh := (Finset.mem_filter.mp h).2
        change (singleInput t).getD j false = true at hh
        by_cases valid : j < n
        · have e : (singleInput t).getD j false = decide ((⟨j,valid⟩ : Fin n) = t) := by
            simp only [singleInput,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left valid,Option.getD_some]
          exact congrArg Fin.val (of_decide_eq_true (e.symm.trans hh))
        · rw [getD_missing (by simp [singleInput];omega)] at hh
          contradiction
      exact id ((at_raw a u).trans (at_raw b v).symm)
  | append_singleton gs g ih =>
    have hm' : Monotone2 (Circuit.mk gs 0) := fun h hx => hm h (List.mem_append_left _ hx)
    have op := (hm g (by simp)).1
    rcases transfer gs g hm' op a ta with ea | ⟨p,tp,ea,da⟩ <;>
      rcases transfer gs g hm' op b tb with eb | ⟨q,tq,eb,db⟩
    · exact Or.inl (ea.trans eb.symm)
    · exact Or.inr (ea ▸ eb ▸ db.symm)
    · exact Or.inr (ea ▸ eb ▸ da)
    · rw [ea,eb];exact ih hm' p q tp tq
end PEqualNP.Research.MissingCell
