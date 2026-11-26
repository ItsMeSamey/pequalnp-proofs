import ThresholdStarTruth
import Mathlib.Data.Fintype.EquivFin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ThresholdOrGroups ThresholdOrExtraction
open ThresholdSimpleIncidence ThresholdRegularSource ThresholdStarTruth T2SoleOrSplice ThresholdPeelSchedule
namespace ThresholdGraphStar

theorem physical_star_floor {B : Circuit} {n : Nat} (L : Layout B n)
    (two : ∀ w,(endpoints L w).card=2)
    (center : {v : T2OrPartition.Id B // v∈vertices L})
    (S : Finset {v : T2OrPartition.Id B // v∈vertices L})
    (linked : ∀ a∈S,(graph L).Adj center a)
    (C D : Circuit) (mono : Monotone2 C) (u : Pins B.gates.length)
    (ok : Match C (fun s => D.eval (List.ofFn (row s))) u)
    (rep : ∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card)
    (keepCenter : center.val∈u) (keep : ∀ a∈S,a.val∈u) :
    2*S.card-4 ≤ ors C.gates := by
  classical
  by_cases pos : 0<S.card
  · let named := S.equivFin.symm
    let nbr : Fin S.card ↪ Fin B.gates.length :=
      ⟨fun i => (named i).val.val, fun a b he =>
        named.injective (Subtype.ext (Subtype.ext he))⟩
    have adj (i : Fin S.card) := linked _ (named i).property
    have ne (i : Fin S.card) : center.val≠nbr i := fun h => (adj i).1 (Subtype.ext h)
    let pick := fun i : Fin S.card => (adj i).2.choose
    have shape (i : Fin S.card) : endpoints L (pick i)={center.val,nbr i} := by
      obtain ⟨a,b⟩ := (adj i).2.choose_spec
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        rcases Finset.mem_insert.mp hj with eq|hj
        · simpa [eq] using a
        · rw [Finset.mem_singleton.mp hj]
          change (named i).val.val ∈ endpoints L (pick i)
          exact b
      · rw [two]; simp [ne i]
    have inj : Function.Injective pick := by
      intro i j eq
      have mem : nbr i∈endpoints L (pick j) := eq ▸ (by rw [shape]; simp)
      rw [shape] at mem
      exact nbr.injective (Finset.mem_singleton.mp ((Finset.mem_insert.mp mem).resolve_left (Ne.symm (ne i))))
    exact star_floor C mono (endpoints L) (fun s => D.eval (List.ofFn (row s))) u ok
      (fun s => by rw [←covered_profile]; exact rep s) center.val nbr ⟨pick,inj⟩ shape keepCenter
      (fun i => keep _ (named i).property) pos
  · have z : S.card=0 := by omega
    simp [z]

#print axioms physical_star_floor
end ThresholdGraphStar
