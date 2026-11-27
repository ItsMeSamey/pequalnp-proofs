import ExactPlanePairSearch
namespace ExactPlaneFirstRankOracle
open ExactPlaneFirstRelation ExactPlaneFirstRank ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlanePairSearch (Key combine)
variable {r N d : Nat}
abbrev Mask (N : Nat) := Fin N→ZMod 2
structure Result (N : Nat) where
  answer : Option (Finset (Fin N))
  calls : Nat

def scan (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) : List (Mask N) → Result N
  | [] => ⟨none,0⟩
  | u::us =>
    if aggregate h u=0 then scan h oracle us else
      match oracle u with
      | some R => ⟨some (support u∪R),1⟩
      | none =>
        let tail := scan h oracle us
        ⟨tail.answer,tail.calls+1⟩

def run (row : Fin r→Mask N) (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) :=
  scan h oracle ((ExactPlaneNumericalRows.words r).map (combine row))

theorem scan_count (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) (l : List (Mask N)) :
    (scan h oracle l).calls≤l.length := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    by_cases zero : aggregate h u=0
    · simpa only [scan,if_pos zero,List.length_cons] using ih.trans (Nat.le_succ _)
    · cases hr : oracle u <;> simp [scan,zero,hr,ih]

theorem bound (row : Fin r→Mask N) (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) :
    (run row h oracle).calls≤2^r := by
  simpa [run,ExactPlaneNumericalRows.length_words] using scan_count h oracle
    ((ExactPlaneNumericalRows.words r).map (combine row))

theorem returns (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) (l : List (Mask N))
    (A : Finset (Fin N)) (ok : (scan h oracle l).answer=some A) :
    ∃ u∈l,aggregate h u≠0 ∧ ∃R,oracle u=some R ∧ A=support u∪R := by
  induction l with
  | nil => simp [scan] at ok
  | cons u us ih =>
    by_cases zero : aggregate h u=0
    · rw [scan,if_pos zero] at ok
      obtain ⟨v,vm,rest⟩ := ih ok
      exact ⟨v,List.mem_cons_of_mem _ vm,rest⟩
    · cases hr : oracle u with
      | none =>
        simp only [scan,if_neg zero,hr] at ok
        obtain ⟨v,vm,rest⟩ := ih ok
        exact ⟨v,List.mem_cons_of_mem _ vm,rest⟩
      | some R =>
        simp only [scan,if_neg zero,hr,Option.some.injEq] at ok
        exact ⟨u,List.mem_cons_self,zero,R,hr,ok.symm⟩

theorem succeeds (h : Fin N→Plane) (oracle : Mask N→Option (Finset (Fin N))) (l : List (Mask N))
    (u : Mask N) (mem : u∈l) (nz : aggregate h u≠0) (got : oracle u≠none) :
    (scan h oracle l).answer≠none := by
  induction l with
  | nil => simp at mem
  | cons v vs ih =>
    by_cases zero : aggregate h v=0
    · rw [scan,if_pos zero]
      exact ih ((List.mem_cons.mp mem).resolve_left (by rintro rfl; exact nz zero))
    · cases hr : oracle v with
      | some R => simp [scan,zero,hr]
      | none =>
        simp only [scan,if_neg zero,hr]
        exact ih ((List.mem_cons.mp mem).resolve_left (by rintro rfl; exact got hr))

theorem conditional (row : Fin r→Mask N) (k : Fin N→Key d) (b h : Fin N→Plane)
    (correctRows : ∀x,combine row x∈first k b) (covers : ∀u∈first k b,∃x,combine row x=u)
    (oracle : Mask N→Option (Finset (Fin N)))
    (sound : ∀u∈first k b,∀R,oracle u=some R→ExactPlaneForcedLine.QTrace k b (scalar h u) (support u) R)
    (all : ∀u∈first k b,∀R,Disjoint R (support u) →
      ExactPlaneForcedLine.QTrace k b (scalar h u) (support u) R → oracle u≠none) :
    ((run row h oracle).answer≠none ↔ ∃A : Finset (Fin N),ExactTrace k b h A) ∧
    ∀ A,(run row h oracle).answer=some A→ExactTrace k b h A := by
  let ls := (ExactPlaneNumericalRows.words r).map (combine row)
  have yes (A) (found : (run row h oracle).answer=some A) : ExactTrace k b h A := by
    obtain ⟨u,hm,_,R,o,id⟩ := returns h oracle ls A found
    obtain ⟨x,_,hx⟩ := List.mem_map.mp hm
    have hu := hx ▸ correctRows x
    rw [id]
    exact original_union k b h u hu R (sound u hu R o)
  refine ⟨⟨?_,?_⟩,yes⟩
  · intro pass
    cases z : (run row h oracle).answer with
    | none => exact False.elim (pass z)
    | some A => exact ⟨A,yes A z⟩
  · intro witness
    obtain ⟨u,hu,nz,R,dis,ok⟩ := (forced k b h).mp witness
    obtain ⟨x,eq⟩ := covers u hu
    exact succeeds h oracle ls u (List.mem_map.mpr ⟨x,ExactPlaneNumericalRows.mem_words x,eq⟩)
      nz (all u hu R dis ok)
#print axioms bound
#print axioms conditional
end ExactPlaneFirstRankOracle
