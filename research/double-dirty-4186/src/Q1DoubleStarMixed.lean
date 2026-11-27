import Q1DoubleStarGeometry
import Q1PrivateBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private

variable {n k p : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {shared : Fin k → Clause n} {other : Fin p → Clause n}

theorem crossing_endpoint (P : Batch G C shared other 2) (hk : 0 < k)
    (v : Fin n) (anchor : ∀ c z, z ∈ shared c → G.Adj v z ∧ s(v,z) ∈ starEdges G C)
    (i : Fin 2) (b : Bool) (outside : ¬ G.Adj v (P.pt i (!b))) :
    (∀ c, P.pt i b ∈ shared c) ∧ P.pt i (!b) ≠ v := by
  have hits (c : Fin k) : P.pt i b ∈ shared c := by
    have h : P.pt i false ∈ shared c ∨ P.pt i true ∈ shared c := P.hits (.inl c) i
    have no : P.pt i (!b) ∉ shared c := fun m => outside (anchor c _ m).1
    cases b <;> simp_all
  refine ⟨hits,fun eq => ?_⟩
  let c : Fin k := ⟨0,hk⟩
  have star := (anchor c _ (hits c)).2
  have res := (Finset.mem_sdiff.mp (P.res i (!b))).2
  simp only [Bool.not_not,eq] at res
  exact res star

private theorem private_reject (P : Batch G C shared other 2)
    (x : Bool) (allX : ∀ c, P.pt 0 x ∈ shared c) (b : Bool) :
    ∃ j, P.pt 0 x ∉ other j ∧ P.pt 1 b ∉ other j := by
  let t : Fin 2 → Bool := fun i => if i=0 then x else b
  obtain ⟨c,hc⟩ := P.reject t
  have f := hc 0
  have s := hc 1
  cases c with
  | inl c => exact (f (by simpa [t,literals] using allX c)).elim
  | inr j => exact ⟨j,by simpa [t,literals] using f,by simpa [t,literals] using s⟩

theorem mixed_private (P : Batch G C shared other 2) (x : Bool)
    (allX : ∀ c, P.pt 0 x ∈ shared c) (small : p < 3) :
    p=2 ∧ ∀ j, P.pt 0 (!x) ∈ other j := by
  classical
  obtain ⟨i,ix,ia⟩ := private_reject P x allX false
  obtain ⟨j,jx,jb⟩ := private_reject P x allX true
  have inner (c : Fin p) : P.pt 1 false ∈ other c ∨ P.pt 1 true ∈ other c := P.hits (.inr c) 1
  have ne : i ≠ j := by rintro rfl; exact (inner i).elim ia jb
  have eq : p=2 := by
    by_contra bad
    have hi := i.isLt; have hj := j.isLt
    exact ne (Fin.ext (by omega))
  refine ⟨eq,fun c => ?_⟩
  have either : c=i ∨ c=j := by
    by_contra! nc
    have hci : c.val ≠ i.val := fun h => nc.1 (Fin.ext h)
    have hcj : c.val ≠ j.val := fun h => nc.2 (Fin.ext h)
    have hij : i.val ≠ j.val := fun h => ne (Fin.ext h)
    have hi := i.isLt; have hj := j.isLt; have hc := c.isLt
    omega
  have hx : P.pt 0 x ∉ other c := by rcases either with rfl|rfl <;> assumption
  have hit : P.pt 0 false ∈ other c ∨ P.pt 0 true ∈ other c := P.hits (.inr c) 0
  cases x <;> simp_all

theorem mixed_power (P : Batch G C shared other 2) (four : NoFourCycle G)
    (z x v : Fin n) (zv : z ≠ v) (xz : G.Adj z x) (vx : G.Adj v x)
    (priv : ∀ j, z ∈ other j) {r : ℕ} (edge : Fin (r+1) → Bool → Fin n)
    (endpointDistinct : ∀ i j, i ≠ j → ∀ b c, edge i b ≠ edge j c)
    (adj : ∀ i, G.Adj (edge i false) (edge i true))
    (inside : ∀ i b, G.Adj v (edge i b))
    (hit : ∀ c i, edge i false ∈ shared c ∨ edge i true ∈ shared c) :
    2^r ≤ k := by
  classical
  obtain ⟨drop,noX⟩ := omit_vertex edge endpointDistinct x
  let pt := fun i b => edge (drop.succAbove i) b
  have h := deficient_shared_slots (P := Fin p) G z pt (fun c y => y ∈ shared c)
    (fun c y => y ∈ other c) (fun c i => hit c _) (fun i b hadj => by
      have eq := common_center four (noX i b) (inside _ b) vx hadj xz
      exact zv eq.symm)
    (fun t i j => by
      by_cases he : i=j
      · subst j; exact G.loopless.irrefl _
      · exact neighborhood_induced G v (fun h => common_center four h) edge adj inside endpointDistinct
          _ _ (fun ht => he (Fin.succAbove_right_inj.mp ht)) _ _)
    priv (fun S hs ho => by
      let T := Finset.univ.filter S
      obtain ⟨a,ha,b,hb,hab⟩ := P.clean T (by
        intro l
        cases l with
        | inl c =>
          obtain ⟨y,hy,hm⟩ := hs c
          exact ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ y,hy⟩,hm⟩
        | inr c =>
          obtain ⟨y,hy,hm⟩ := ho c
          exact ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ y,hy⟩,hm⟩)
      exact ⟨a,b,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2,hab⟩)
  simpa using h
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
