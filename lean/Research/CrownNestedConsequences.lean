import Research.CrownNestedReaders
import Research.CrownDisjointSingletonWires
import Research.CrownNestedSingleton

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem nest_singleton_spec {n : Nat} (t : Fin n) (j : Nat) :
    (nestSingleton t).getD j false = true ↔ j = t.val := by
  by_cases small : j < n
  · simp [nestSingleton,List.getD_eq_getElem?_getD,small,Fin.ext_iff]
  · simp [nestSingleton,List.getD_eq_getElem?_getD,small,show j ≠ t.val by omega]

private theorem raw_wire_iff {n : Nat} (C : Circuit) (t q : Fin n) :
    (C.wires (nestSingleton t)).getD q.val false = true ↔ t = q := by
  have keep : (C.wires (nestSingleton t)).getD q.val false = (nestSingleton t).getD q.val false :=
    nest_input_preserved _ _ _ (by simp [nestSingleton])
  rw [keep,nest_singleton_spec]
  simp [Fin.ext_iff,eq_comm]

/-- A nested later OR fires on precisely its earlier OR's singleton support
together with the later sibling literal. -/
theorem nest_second_support (C : Circuit) (b : Fin 24) (g h : Fin C.gates.length)
    (seed : List Bool) (live : (trueOrFlags C.gates seed).getD g.val false = true)
    (rh : readAt C.gates 24 h.val = {b.val,24+g.val}) (t : Fin 24) :
    h ∈ activeOrIds C.gates (nestSingleton t) ↔
      t = b ∨ g ∈ activeOrIds C.gates (nestSingleton t) := by
  have len : (nestSingleton t).length = 24 := by simp [nestSingleton]
  rw [activeOrIds_iff_final_parent, len,rh,activeOrIds_mem]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  have equiv := nest_flag_as_wire C.gates seed (nestSingleton t) g.val live
  rw [len] at equiv
  rw [equiv]
  constructor
  · rintro ⟨i,hi,on⟩
    rcases hi with rfl|rfl
    · exact Or.inl ((raw_wire_iff C t b).mp on)
    · exact Or.inr on
  · rintro (e|live')
    · exact ⟨b.val,Or.inl rfl,(raw_wire_iff C t b).mpr e⟩
    · exact ⟨24+g.val,Or.inr rfl,live'⟩

/-- Two raw parents fix exactly the singleton support of their OR. -/
theorem nest_raw_support (C : Circuit) (a j t : Fin 24) (g : Fin C.gates.length)
    (parents : readAt C.gates 24 g.val = {a.val,j.val}) :
    g ∈ activeOrIds C.gates (nestSingleton t) ↔ t = a ∨ t = j := by
  rw [activeOrIds_iff_final_parent,show (nestSingleton t).length = 24 by simp [nestSingleton],parents]
  constructor
  · rintro ⟨i,hi,hot⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact Or.inl ((raw_wire_iff C t a).mp hot)
    · exact Or.inr ((raw_wire_iff C t j).mp hot)
  · rintro (e|e)
    · exact ⟨a.val,by simp,(raw_wire_iff C t a).mpr e⟩
    · exact ⟨j.val,by simp,(raw_wire_iff C t j).mpr e⟩

theorem nest_contaminated_first_readers (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (a j : Fin 24) (aj : a ≠ j) (g h : Fin C.gates.length) (gh : g < h)
    (aReads : a.val ∈ readAt C.gates 24 g.val)
    (hit : g ∈ activeOrIds C.gates (nestSingleton j))
    (next : h ∈ activeOrIds C.gates (nestSingleton j))
    (cap : (activeOrIds C.gates (nestSingleton j)).card ≤ 2) :
    readAt C.gates 24 g.val = {a.val,j.val} := by
  let S := activeOrIds C.gates (nestSingleton j)
  have hr : ({g,h} : Finset _) ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with e|e
    · exact e ▸ hit
    · exact (Finset.mem_singleton.mp e) ▸ next
  have eS := Finset.eq_of_subset_of_card_le hr (by simpa [ne_of_lt gh] using cap)
  have bef (k : Nat) (hk : k < g.val) : (trueOrFlags C.gates (nestSingleton j)).getD k false = false := by
    cases e : (trueOrFlags C.gates (nestSingleton j)).getD k false with
    | false => rfl
    | true =>
      let t : Fin C.gates.length := ⟨k,by omega⟩
      have mem : t ∈ S := (activeOrIds_mem ..).mpr e
      rw [← eS] at mem
      simp only [Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] at mem
      dsimp [t] at mem
      omega
  have jr := nest_first_read C hm rep mini size ors (nestSingleton j) (by simp [nestSingleton]) j
    (nest_singleton_spec j) _ ((activeOrIds_mem ..).mp hit) bef
  have both : ({a.val,j.val} : Finset Nat) ⊆ readAt C.gates 24 g.val := by
    intro i hi
    rcases Finset.mem_insert.mp hi with e|e
    · exact e ▸ aReads
    · exact (Finset.mem_singleton.mp e) ▸ jr
  apply (Finset.eq_of_subset_of_card_le both _).symm
  simpa [show a.val ≠ j.val from fun e => aj (Fin.ext e)] using
    readAt_card_le_two C.gates 24 g.val (fun op hh => (hm op hh).2)


/-- A clean first OR and its copy-through second OR have signatures disjoint
from every other singleton except the sibling. -/
theorem nest_clean_separate (C : Circuit) (a b : Fin 24) (g h : Fin C.gates.length)
    (early : activeOrIds C.gates (nestSingleton a) = {g,h})
    (rh : readAt C.gates 24 h.val = {b.val,24+g.val})
    (clean : ∀ t : Fin 24, g ∈ activeOrIds C.gates (nestSingleton t) → t = a)
    (q : Fin 24) (qa : q ≠ a) (qb : q ≠ b) :
    Disjoint (activeOrIds C.gates (nestSingleton a)) (activeOrIds C.gates (nestSingleton q)) := by
  have hit : g ∈ activeOrIds C.gates (nestSingleton a) := by rw [early]; simp
  have rule := nest_second_support C b g h (nestSingleton a) ((activeOrIds_mem ..).mp hit) rh q
  apply Finset.disjoint_left.mpr
  intro k hk hq
  rw [early] at hk
  rcases Finset.mem_insert.mp hk with rfl|hk
  · exact qa (clean q hq)
  · have he := Finset.mem_singleton.mp hk
    subst k
    exact (rule.mp hq).elim qb (fun f => qa (clean q f))

/-- A third literal accepted by the first gate forces its sibling to fire no
OR, provided the two sibling traces share a diagonal with at most two ORs. -/
theorem nest_bad_sibling_zero (C : Circuit) (a b j sibling : Fin 24) (g h : Fin C.gates.length)
    (gh : g ≠ h) (ga : readAt C.gates 24 g.val = {a.val,j.val})
    (hb : readAt C.gates 24 h.val = {b.val,24+g.val})
    (na : sibling ≠ a) (nb : sibling ≠ b) (nj : sibling ≠ j)
    (diag : Finset (Fin C.gates.length)) (cap : diag.card ≤ 2)
    (jsub : activeOrIds C.gates (nestSingleton j) ⊆ diag)
    (sub : activeOrIds C.gates (nestSingleton sibling) ⊆ diag) :
    activeOrIds C.gates (nestSingleton sibling) = ∅ := by
  have gj := (nest_raw_support C a j j g ga).mpr (Or.inr rfl)
  have rule := nest_second_support C b g h (nestSingleton j) ((activeOrIds_mem ..).mp gj) hb
  have ng : g ∉ activeOrIds C.gates (nestSingleton sibling) :=
    fun mem => ((nest_raw_support C a j sibling g ga).mp mem).elim na nj
  exact CrownNestedSingleton.contaminated_sibling (fun t => activeOrIds C.gates (nestSingleton t))
    diag j sibling g h gh gj ((rule j).mpr (Or.inr gj)) jsub sub cap ng
    (fun mem => ((rule sibling).mp mem).elim nb ng)

end PEqualNP.Research.MissingCell
