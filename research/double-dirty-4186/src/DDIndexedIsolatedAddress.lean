import DDIndexedRootCover
import DDComparable
import DDIndexedDominance
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

theorem isolated_clean_reader {n e j : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (top : e ∈ tops G C)
    (reader : j ∈ readers n C e) : j ∈ orT G C := by
  obtain ⟨hr,_,clean⟩ := Finset.mem_filter.mp top
  obtain ⟨read,out,_⟩ := main_real n G C edge least form
  have neq : n+e ≠ C.output := by
    intro eq
    have ix : C.output-n = e := by omega
    rw [ix] at out
    simpa [out] using reader
  obtain ⟨r,one,op,below⟩ := read e (Finset.mem_range.mp hr) clean neq
  have eq := reader
  rw [one,Finset.mem_singleton] at eq
  subst r
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp reader).1,op,below⟩

theorem address_isolated {n m e : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (top : e ∈ tops G C)
    {ge : Gate} (paid : ins n C (splitCuts n C (orT G C) m) e = some ge) :
    let p := splitCuts n C (orT G C) m
    ∀ k ≤ C.size, ∀ w < n+k, ∀ o, ref (build n C p k) w = some (o,n+rank n C p e) → w=n+e := by
  dsimp only
  let p := splitCuts n C (orT G C) m
  change ∀ k ≤ C.size, ∀ w < n+k, ∀ o, ref (build n C p k) w = some (o,n+rank n C p e) → w=n+e
  intro k
  induction k with
  | zero =>
    intro _ w hw o h
    have hw' : w<n := by omega
    simp [ref,build,initial,List.getD_eq_getElem?_getD,hw'] at h
    omega
  | succ j ih =>
    intro jk w hw o eq
    have jl : j<C.size := by omega
    by_cases prev : w<n+j
    · rw [stable_ref C p prev] at eq
      exact ih (by omega) w prev o eq
    have wj : w=n+j := by omega
    subst w
    rw [row_ref C p (Nat.lt_succ_self j)] at eq
    have omitted (b : Fin 2) (z : Origin × ℕ) (hit : pin (build n C p j) n C p j b = some z)
        (addr : z.2 = n+rank n C p e) : p.omit j = true := by
      have hpin := opnd_mem least.1 jl b
      have bound := least.1.2.1 j jl _ hpin
      simp only [pin] at hit
      split at hit
      · contradiction
      · have hh : ref (build n C p j) (opnd C j b) = some (z.1,n+rank n C p e) := by simpa [←addr] using hit
        have eqw := ih (by omega) _ bound _ hh
        rw [eqw] at hpin
        have clean := isolated_clean_reader edge least form top (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,hpin⟩)
        simp [p,splitCuts,clean]
    cases hl : pin (build n C p j) n C p j 0 with
    | none =>
      cases hr : pin (build n C p j) n C p j 1 with
      | none => cases skip : p.omit j <;> by_cases op : (gateAt C j).op = .and <;> simp_all [dest]
      | some r =>
        by_cases skip : p.omit j = true
        · simp [dest,skip,hl,hr] at eq
        have op : (gateAt C j).op = .and := by by_contra h;simp [dest,skip,hl,hr,h] at eq
        have pair : r = (o,n+rank n C p e) := by simpa [dest,skip,hl,hr,op] using eq
        exact (skip (omitted 1 r hr (congrArg Prod.snd pair))).elim
    | some l =>
      cases hr : pin (build n C p j) n C p j 1 with
      | none =>
        by_cases skip : p.omit j = true
        · simp [dest,skip,hl,hr] at eq
        have op : (gateAt C j).op = .and := by by_contra h;simp [dest,skip,hl,hr,h] at eq
        have pair : l = (o,n+rank n C p e) := by simpa [dest,skip,hl,hr,op] using eq
        exact (skip (omitted 0 l hl (congrArg Prod.snd pair))).elim
      | some r =>
        by_cases skip : p.omit j = true
        · simp [dest,skip,hl,hr] at eq
        have paidj : ins n C p j = some ⟨(gateAt C j).op,[l.2,r.2]⟩ := by simp [ins,instruction,hl,hr,skip]
        have pair : (Origin.gate j,n+rank n C p j) = (o,n+rank n C p e) := by simpa [dest,skip,hl,hr] using eq
        have addr : rank n C p j = rank n C p e := Nat.add_left_cancel (congrArg Prod.snd pair)
        rw [owner_unique C p paidj paid addr]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
