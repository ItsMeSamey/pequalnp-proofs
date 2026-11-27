import ExactPlaneEagerDecision
namespace ExactPlaneChargedOdd
variable {C : Type*} [AddMonoid C]
structure Output (C : Type*) where
  charts : List C
  emitted : Nat
  terms : Nat

/-- Operand occurrences in chart words are distinct from bit operations on
materialized physical inputs. -/
def emit : List (List C) → Output C
  | [] => ⟨[],0,0⟩
  | w::ws =>
    let rest := emit ws
    ⟨w.sum::rest.charts,rest.emitted+1,w.length+rest.terms⟩

theorem emit_spec (ws : List (List C)) :
    emit ws=⟨ws.map List.sum,ws.length,(ws.map List.length).sum⟩ := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [emit,ih]

def counted (s : List C) :=
  emit (ExactPlaneOddChartList.words s 1 ++ ExactPlaneOddChartList.words s 3 ++ ExactPlaneOddChartList.words s 5)

def card (s : Nat) := s+s^3+s^5
def occurrences (s : Nat) := s+3*s^3+5*s^5

theorem terms (s : List C) (j : Nat) :
    ((ExactPlaneOddChartList.words s j).map List.length).sum=s.length^j*j := by
  have all : (ExactPlaneOddChartList.words s j).map List.length =
      (ExactPlaneOddChartList.words s j).map (fun _=>j) := by
    apply List.map_congr_left
    intro x hx
    exact ((ExactPlaneOddChartList.mem_words _ _ _).mp hx).1
  rw [all]
  simp [ExactPlaneOddChartList.length_words]

theorem counted_spec (s : List C) :
    counted s=⟨ExactPlaneOddChartList.candidates s,card s.length,occurrences s.length⟩ := by
  simp only [counted,emit_spec,ExactPlaneOddChartList.candidates,List.length_append,
    ExactPlaneOddChartList.length_words,List.map_append,List.sum_append,terms,card,occurrences,pow_one,
    Nat.mul_one,Nat.mul_comm]
#print axioms counted_spec
end ExactPlaneChargedOdd
