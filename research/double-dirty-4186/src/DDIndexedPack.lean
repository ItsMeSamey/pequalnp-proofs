import DDIndexedRows
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q1Double S4183.S98
attribute [local instance] gateOpDecEq

private def Bounded (k : ℕ) (r : Ref) := ∀ a, r = some a → a.2 < k

private theorem pin_bound {n j : ℕ} {C : Circuit} {p : Cuts}
    (s : State) (h : ∀ r ∈ s.refs, Bounded (n+s.gates.length) r) (b : Fin 2) :
    Bounded (n+s.gates.length) (pin s n C p j b) := by
  simp only [pin]
  split
  · simp [Bounded]
  · unfold ref
    by_cases hw : opnd C j b < s.refs.length
    · rw [List.getD_eq_getElem _ _ hw]; exact h _ (List.getElem_mem hw)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [Bounded]

private theorem step_bound {n j : ℕ} (C : Circuit) (p : Cuts) (s : State)
    (h : ∀ r ∈ s.refs, Bounded (n+s.gates.length) r) :
    ∀ r ∈ (step s n C p j).refs, Bounded (n+(step s n C p j).gates.length) r := by
  intro r hr
  have L := pin_bound (C:=C) (p:=p) (j:=j) s h 0
  have R := pin_bound (C:=C) (p:=p) (j:=j) s h 1
  change r ∈ _ ++ [_] at hr
  rcases List.mem_append.mp hr with old | last
  · intro a ha
    have := h _ old _ ha
    change _ < n+(s.gates ++ _).length
    rw [List.length_append]; omega
  · obtain rfl := List.mem_singleton.mp last
    cases hl : pin s n C p j 0 <;> cases hr : pin s n C p j 1 <;>
      cases ho : p.omit j <;> by_cases hop : (gateAt C j).op = .and <;>
      simp_all [Bounded,dest,step,instruction,Option.orElse] <;> omega

private theorem all_bound (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    ∀ r ∈ (build n C p k).refs, Bounded (n+rank n C p k) r := by
  induction k with
  | zero =>
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simpa [Bounded,build,initial,rank] using List.mem_range.mp hi
  | succ k ih => exact step_bound C p _ ih

theorem ref_bound {n k w v : ℕ} {C : Circuit} {p : Cuts} {o : Origin}
    (h : ref (build n C p k) w = some (o,v)) : v < n+rank n C p k := by
  have hw : w < (build n C p k).refs.length := by
    by_contra! bad
    unfold ref at h
    rw [List.getD_eq_default _ _ bad] at h
    contradiction
  unfold ref at h
  rw [List.getD_eq_getElem _ _ hw] at h
  exact all_bound n C p k _ (List.getElem_mem hw) _ h

theorem pack_exists {n : ℕ} (C : Circuit) (cuts : Cuts) (ao : IsAO2 n C)
    (k : ℕ) (hk : k ≤ C.gates.length) : ∃ p : Pack n, p.gates = (build n C cuts k).gates := by
  induction k with
  | zero => exact ⟨Pack.empty n,rfl⟩
  | succ j ih =>
    obtain ⟨pack,eq⟩ := ih (by omega)
    let s := build n C cuts j
    by_cases no : ins n C cuts j = none
    · exact ⟨pack, by simpa [gates_step,no] using eq⟩
    have both : ∃ a b : Origin × ℕ, pin s n C cuts j 0 = some a ∧ pin s n C cuts j 1 = some b ∧
        cuts.omit j = false := by
      cases l : pin s n C cuts j 0 <;> cases r : pin s n C cuts j 1 <;> cases o : cuts.omit j <;>
        simp_all [ins,s,instruction]
    obtain ⟨a,b,hl,hr,ho⟩ := both
    have bound := all_bound n C cuts j
    let aw : pack.Wire := ⟨a.2, by rw [eq]; exact pin_bound s bound 0 a hl⟩
    let bw : pack.Wire := ⟨b.2, by rw [eq]; exact pin_bound s bound 1 b hr⟩
    have op := (AO_of_IsAO2 n C ao j (by omega)).1
    have inst : ins n C cuts j = some ⟨(gateAt C j).op,[a.2,b.2]⟩ := by
      change instruction _ _ (pin s n C cuts j 0) (pin s n C cuts j 1) = _
      simp [hl,hr,ho,instruction]
    rcases op with hop | hop
    · refine ⟨pack.emit true aw bw,?_⟩
      change pack.gates ++ [⟨.and,[a.2,b.2]⟩] = _
      rw [gates_step,inst,hop,eq] <;> rfl
    · refine ⟨pack.emit false aw bw,?_⟩
      change pack.gates ++ [⟨.or,[a.2,b.2]⟩] = _
      rw [gates_step,inst,hop,eq] <;> rfl

theorem prefix_ao2 {n : ℕ} (C : Circuit) (cuts : Cuts) (ao : IsAO2 n C)
    (k : ℕ) (hk : k ≤ C.gates.length) (out : ℕ) :
    IsAO2 n ⟨(build n C cuts k).gates,out⟩ := by
  obtain ⟨p,hp⟩ := pack_exists C cuts ao k hk
  rw [←hp]
  refine ⟨p.allowed,?_,p.arity⟩
  intro j hj v hv
  apply p.earlier ⟨j,hj⟩ v
  simpa only [gateAt,List.getD_eq_get _ _ (⟨j,hj⟩ : Fin p.gates.length)] using hv
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
