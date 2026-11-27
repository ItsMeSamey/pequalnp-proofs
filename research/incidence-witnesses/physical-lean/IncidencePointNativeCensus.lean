import IncidencePointBooking
import IncidenceNativePin
import Research.IncidenceRobust
namespace IncidencePointBooking
open CircuitRewire IncidenceRobust SparseQueryCut IncidenceZeroRestriction
variable {n : Nat}

def lineInputs (n j : Nat) : Set (Finset (Fin n)) :=
  if h : j<n then {T| (⟨j,h⟩ : Fin n)∈T} else ∅

theorem native_census (I : Fin n→Fin n→Prop) [DecidableRel I]
    (degree : ∀ l,Fintype.card {p // I p l}=402)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    (hn : n=401^2+401+1) (s : Nat) (raw : Nat→Gate) (C : Finset (Fin n))
    (W : Fin n→Finset (Fin n)) (o : Fin n→Nat) (few : ∀ x∈C,(W x).card≤2)
    (anti : ∀ x∈C,∀ y∈C,x≠y → x∈W y → y∉W x)
    (top : ∀ j<s,(raw j).left<n+j ∧ (raw j).right<n+j)
    (bound : ∀ x∈C,o x<n+s)
    (pos : ∀ x∈C,∀ l∈lines I x,({l} : Finset (Fin n))∈execute n raw (lineInputs n) s (o x))
    (neg : ∀ x∈C,∀ T : Finset (Fin n),T.card≤199 → Disjoint T ((W x).biUnion (lines I)) →
      T∉execute n raw (lineInputs n) s (o x))
    (size : s≤646424) (edited total : Nat) (partition : total=edited+C.card) (paid : edited≤3213) :
    total≤6461 := by
  classical
  let X := execute n raw (lineInputs n) s
  have input (j : Nat) (hj : j<n) : X j=lineInputs n j := run_inputs n s raw _ j hj
  have laws (j : Nat) (hj : j<s) : X (n+j)=(raw j).eval X :=
    run_gate n s raw _ j hj (top j hj).1 (top j hj).2
  apply census n s raw X C (lines I) W o (fun _ _ h=>line_overlap I unique h)
    few anti top laws _ _ bound (fun x _=>lines_card I degree unique (q:=401) (by decide) hn x)
    pos neg size edited total partition paid
  · intro j hj
    have pr : profile X j={⟨j,hj⟩} := by
      ext l
      rw [mem_profile,input j hj]
      simp [lineInputs,hj,eq_comm]
    simp [pr]
  · intro j hj l T hl
    obtain ⟨S,_,refs,cut⟩ := LocalGateCut.cut_ordered n s j raw X hj top laws (Finset.range s)
    apply cut
    intro i hi hot
    obtain ⟨lim,rawOr⟩ := refs i hi
    have small : i<n := by
      rcases rawOr with h|outside
      · exact h
      · by_contra! ge
        exact outside (Finset.mem_range.mpr (by omega))
    rw [input i small] at hot ⊢
    simpa [lineInputs,small] using (show (⟨i,small⟩ : Fin n)∈T by
      have same : (⟨i,small⟩ : Fin n)=l := by simpa [lineInputs,small] using hot
      simpa [same] using hl)
#print axioms native_census
end IncidencePointBooking
