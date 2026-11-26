import ThresholdQuarterCubes
import ThresholdRegularSource
import T2CubeAgreement
import Batteries.Tactic.OpenPrivate

namespace ThresholdFirstActive
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice ThresholdQuarterCubes
open private run_old from T2SoleOrEval

variable {C : Circuit} {n : Nat}

/-- Paths use physical wire indices and stop before the first AND. -/
inductive OrPath (L : Layout C n) (x : Fin n) : Nat → Prop where
  | raw : OrPath L x x.val
  | left {i : T2OrPartition.Id C} (op : L.op i = .or) (p : OrPath L x (L.left i)) :
      OrPath L x (n+i.val)
  | right {i : T2OrPartition.Id C} (op : L.op i = .or) (p : OrPath L x (L.right i)) :
      OrPath L x (n+i.val)

def bit (C : Circuit) {n : Nat} (s : Finset (Fin n)) (j : Nat) := (C.wires (vector s)).getD j false
def Active (L : Layout C n) (s : Finset (Fin n)) (i : T2OrPartition.Id C) :=
  L.op i = .and ∧ bit C s (n+i.val) = true

private theorem raw_bit (s : Finset (Fin n)) (x : Fin n) :
    bit C s x.val = decide (x ∈ s) := by
  change (run C.gates (vector s)).getD x.val false = _
  rw [run_old _ _ _ (by simpa [vector] using x.isLt),vec_get]
  simp [x.isLt]

theorem OrPath.lit {L : Layout C n} {x : Fin n} {w : Nat} (p : OrPath L x w) :
    bit C {x} w = true := by
  induction p with
  | raw => simp [raw_bit]
  | left op _ ih =>
    change (C.wires _).getD _ false = _
    rw [(L.atIndex _).eval _ (by simp [vector]),op]
    change bit C {x} _ || bit C {x} _ = true
    rw [ih]; rfl
  | right op _ ih =>
    change (C.wires _).getD _ false = _
    rw [(L.atIndex _).eval _ (by simp [vector]),op]
    change bit C {x} _ || bit C {x} _ = true
    rw [ih]; simp

/-- Trace a true wire to a raw OR-only path or an active AND at or below the wire. -/
theorem provenance (L : Layout C n) (s : Finset (Fin n)) (w : Nat)
    (fit : w < n+C.gates.length) (on : bit C s w = true) :
    (∃ x ∈ s, OrPath L x w) ∨ ∃ i, n+i.val ≤ w ∧ Active L s i := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<n
    · let x : Fin n := ⟨w,raw⟩
      have h : decide (x ∈ s) = true := (raw_bit (C := C) s x).symm.trans on
      exact Or.inl ⟨x,of_decide_eq_true h,.raw⟩
    · let i : T2OrPartition.Id C := ⟨w-n,by omega⟩
      have wi : w = n+i.val := by dsimp [i]; omega
      have g := L.atIndex i
      rcases hi : L.op i with _ | _
      · exact Or.inr ⟨i,by omega,hi,by simpa only [wi] using on⟩
      · have lit := g.eval (vector s) (by simp [vector])
        rw [hi] at lit
        have both : bit C s (L.left i) = true ∨ bit C s (L.right i) = true := by
          have atGate : bit C s (n+i.val) = true := wi ▸ on
          unfold bit at atGate
          rw [lit] at atGate
          simpa [bit,act] using atGate
        rcases both with hl | hr
        · have lt : L.left i < w := by rw [wi]; exact g.leftEarlier
          rcases ih _ lt (by omega) hl with ⟨x,hx,hp⟩ | ⟨j,hj,ac⟩
          · exact Or.inl ⟨x,hx,wi.symm ▸ OrPath.left hi hp⟩
          · exact Or.inr ⟨j,by omega,ac⟩
        · have lt : L.right i < w := by rw [wi]; exact g.rightEarlier
          rcases ih _ lt (by omega) hr with ⟨x,hx,hp⟩ | ⟨j,hj,ac⟩
          · exact Or.inl ⟨x,hx,wi.symm ▸ OrPath.right hi hp⟩
          · exact Or.inr ⟨j,by omega,ac⟩

theorem pair_active (L : Layout C n) (correct : Computes n C) (out : C.output < n+C.gates.length)
    (x y : Fin n) (ne : x ≠ y) : ∃ i, Active L {x,y} i := by
  have yes : bit C {x,y} C.output = true := (correct {x,y}).mpr (by simp [ne])
  rcases provenance L {x,y} C.output out yes with ⟨r,_,p⟩ | ⟨i,_,ha⟩
  · have no := (correct {r}).mp p.lit
    simp at no
  · exact ⟨i,ha⟩

def port (L : Layout C n) (i : T2OrPartition.Id C) : Bool → Nat
  | false => L.left i
  | true => L.right i

/-- Structural boundary hypothesis: each raw has at most the two indicated
    first AND ports after following all zero or more intervening ORs. -/
def CoversPorts (L : Layout C n) (x : Fin n) (p : TwoPins (T2OrPartition.Id C)) :=
  ∀ i, L.op i = .and → ∀ b, OrPath L x (port L i b) → Hits p i b

theorem avoiding_bound (L : Layout C n) (correct : Computes n C)
    (out : C.output < n+C.gates.length) (E : Finset (Fin n))
    (pins : (e : E) → TwoPins (T2OrPartition.Id C))
    (covers : ∀ e, CoversPorts L e.val (pins e)) : E.card ≤ 4 := by
  classical
  have result := bound_of_first_active pins (fun e f => Active L {e.val,f.val})
    (fun e f ne => pair_active L correct out e.val f.val (fun eq => ne (Subtype.ext eq))) (by
      intro e f ne i ac b
      have ev := (L.atIndex i).eval (vector {e.val,f.val}) (by simp [vector])
      rw [ac.1] at ev
      have lit : bit C {e.val,f.val} (port L i b) = true := by
        have a := ac.2
        unfold bit at a
        rw [ev] at a
        cases b <;> simp_all [port,bit,act]
      have lt : port L i b < n+i.val := by
        cases b
        · exact (L.atIndex i).leftEarlier
        · exact (L.atIndex i).rightEarlier
      have il := i.isLt
      rcases provenance L {e.val,f.val} _ (by omega) lit with ⟨x,hx,hp⟩ | ⟨j,hj,ha⟩
      · rcases Finset.mem_insert.mp hx with h | h
        · subst x; exact Or.inl (covers e i ac.1 b hp)
        · have h' := Finset.mem_singleton.mp h
          subst x; exact Or.inr (Or.inl (covers f i ac.1 b hp))
      · exact Or.inr (Or.inr ⟨j,by omega,ha⟩))
  simpa using result

end ThresholdFirstActive
