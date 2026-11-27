import ExactPlaneMaskCompatibility
import ExactPlaneComputedDeficit
namespace ExactPlaneEnumeratedFirst
open ExactPlaneFirstRelation ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlanePairSearch (Key)
variable {N d : Nat}
abbrev F := ZMod 2
abbrev Mask (N : Nat) := Fin N→F

def masks (k : Fin N→Key d) (b : Fin N→Plane) :=
  (ExactPlaneNumericalRows.words N).filter (fun z=>
    decide (aggregate k z=0) && ExactPlaneMaskCompatibility.test k b (support z))

theorem mem_masks (k : Fin N→Key d) (b : Fin N→Plane) (z : Mask N) :
    z∈masks k b ↔ ∃g,z∈relation k b g := by
  simp only [masks,List.mem_filter,ExactPlaneNumericalRows.mem_words,true_and,Bool.and_eq_true_iff,
    decide_eq_true_eq,ExactPlaneMaskCompatibility.test_iff,mem_relation]
  constructor
  · rintro ⟨h,g,u⟩; exact ⟨g,h,u⟩
  · rintro ⟨g,h,u⟩; exact ⟨h,g,u⟩

def sites (l : List (Mask N)) (i : Fin l.length) : Mask N := l[i]

theorem range_sites (l : List (Mask N)) (z : Mask N) :
    z∈Set.range (sites l) ↔ z∈l := by
  constructor
  · rintro ⟨i,rfl⟩; exact List.getElem_mem _
  · intro h
    obtain ⟨i,lt,eq⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i,lt⟩,eq⟩

theorem span_masks (k : Fin N→Key d) (b : Fin N→Plane) :
    Submodule.span F (Set.range (sites (masks k b)))=first k b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨g,hg⟩ := (mem_masks k b z).mp ((range_sites _ _).mp hz)
    exact (le_iSup (relation k b) g) hg
  · apply iSup_le
    intro g z hz
    exact Submodule.subset_span ((range_sites _ _).mpr ((mem_masks k b z).mpr ⟨g,hz⟩))

def basisIds (l : List (Mask N)) :=
  ExactPlaneEagerBank.basis Finset.univ (sites l) (fun _=>0) (fun _=>0)

def basisList (l : List (Mask N)) := ((basisIds l).sort (·≤·)).map (sites l)

theorem basisList_count (k : Fin N→Key d) (b : Fin N→Plane) :
    (basisList (masks k b)).length=Module.finrank F (first k b) := by
  let l := masks k b
  rw [basisList,List.length_map,Finset.length_sort]
  change ExactPlaneComputedDeficit.keyRank (sites l) Finset.univ=_
  rw [ExactPlaneComputedDeficit.keyRank_eq]
  have eq : Set.range (fun j : ↥(Finset.univ : Finset (Fin l.length))=>sites l j.val)=Set.range (sites l) := by
    ext z
    exact ⟨fun ⟨i,e⟩=>⟨i.val,e⟩,fun ⟨i,e⟩=>⟨⟨i,Finset.mem_univ _⟩,e⟩⟩
  rw [eq,span_masks]

theorem basisList_span (l : List (Mask N)) :
    Submodule.span F (Set.range (sites (basisList l)))=Submodule.span F (Set.range (sites l)) := by
  let p := sites l
  let b : Fin l.length→Plane := 0
  let pr := LinearMap.fst F (Mask N) (Plane×Plane)
  have projection (A : Finset (Fin l.length)) :
      (physicalSpan p b b A).map pr=Submodule.span F (Set.range (fun i : ↥A=>p i.val)) := by
    rw [physicalSpan,Submodule.map_span,←Set.range_comp]
    rfl
  have same : physicalSpan p b b (basisIds l)=physicalSpan p b b Finset.univ := by
    change physicalSpan p b b (ExactPlaneEagerBank.basis Finset.univ p b b)=_
    rw [ExactPlaneEagerBank.basis_eq]
    exact (ExactPlaneGaussianIDs.keep_spec _ _ _ _).2.2
  have rho := congrArg (fun S=>Submodule.map pr S) same
  rw [projection,projection] at rho
  have left : Set.range (sites (basisList l))=Set.range (fun i : ↥(basisIds l)=>p i.val) := by
    ext v
    rw [range_sites]
    simp only [basisList,List.mem_map,Finset.mem_sort]
    exact ⟨fun ⟨i,hi,eq⟩=>⟨⟨i,hi⟩,eq⟩,fun ⟨i,eq⟩=>⟨i.val,i.property,eq⟩⟩
  have right : Set.range (fun i : ↥(Finset.univ : Finset (Fin l.length))=>p i.val)=Set.range p := by
    ext v
    exact ⟨fun ⟨i,e⟩=>⟨i.val,e⟩,fun ⟨i,e⟩=>⟨⟨i,Finset.mem_univ _⟩,e⟩⟩
  rw [left,←right]
  exact rho

def solve (k : Fin N→Key d) (b h : Fin N→Plane) :=
  let rows := basisList (masks k b)
  ExactPlanePairSearch.solve (sites rows) k b h

theorem decision (k : Fin N→Key d) (b h : Fin N→Plane) :
    solve k b h≠none ↔ ∃A : Finset (Fin N), ExactTrace k b h A := by
  apply ExactPlanePairSearch.complete
  intro z hz
  rw [←span_masks k b,←basisList_span] at hz
  exact (Submodule.mem_span_range_iff_exists_fun F).mp hz

theorem returned {k : Fin N→Key d} {b h : Fin N→Plane} {A : Finset (Fin N)}
    (ok : solve k b h=some A) : ExactTrace k b h A := ExactPlanePairSearch.returned ok

theorem pair_count (k : Fin N→Key d) (b : Fin N→Plane) :
    (ExactPlanePairSearch.pairs (sites (basisList (masks k b)))).length=4^(Module.finrank F (first k b)) := by
  rw [ExactPlanePairSearch.count,basisList_count]
#print axioms decision
#print axioms returned
#print axioms pair_count
end ExactPlaneEnumeratedFirst
