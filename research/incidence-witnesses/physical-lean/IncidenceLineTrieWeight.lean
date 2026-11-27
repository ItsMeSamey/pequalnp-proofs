import Lean.Elab.Tactic.Omega
namespace IncidenceLineTrieWeight

inductive Tree where
  | single
  | pair
  | fork (left right : Tree)
open Tree

def count : Tree → Nat
  | single => 1
  | pair => 2
  | fork a b => count a+count b

/-- External path length after expanding each terminal pair into a cherry. -/
def length : Tree → Nat
  | single => 0
  | pair => 2
  | fork a b => length a+length b+count a+count b

def loss : Tree → Nat
  | single => 1
  | _ => 0

/-- Eligible assignment retained after discarding a singleton child once. -/
def weight : Tree → Nat
  | single | pair => 0
  | fork a b => weight a + weight b + (count a - loss a) + (count b - loss b)

theorem count_pos (t : Tree) : 0<count t := by
  induction t <;> simp_all [count] <;> omega
theorem loss_le_count (t : Tree) : loss t≤count t := by cases t <;> simp [count,loss]

theorem weight_length (t : Tree) : length t + loss t ≤ weight t + count t := by
  induction t with
  | single => decide
  | pair => decide
  | fork a b A B =>
    have u := loss_le_count a
    have v := loss_le_count b
    change length a + length b + count a + count b + 0 ≤ weight a + weight b + (count a - loss a) + (count b - loss b) + (count a + count b)
    omega

/-- Discrete Kraft tangent, uniform in the chosen depth. -/
theorem external (t : Tree) (k : Nat) :
    (k+2)*count t ≤ length t + 2^(k+1) := by
  induction k generalizing t with
  | zero =>
    induction t with
    | single => decide
    | pair => decide
    | fork a b A B =>
      have pa := count_pos a
      have pb := count_pos b
      simp only [length,count]
      omega
  | succ k ih =>
    cases t with
    | single =>
      have prev := ih single
      simp only [count,length,Nat.mul_one,Nat.zero_add] at prev ⊢
      rw [Nat.pow_succ (2:Nat) (k+1)]
      omega
    | pair =>
      have prev := ih pair
      simp only [count,length] at prev ⊢
      rw [Nat.pow_succ (2:Nat) (k+1)]
      have pos : 0<2^k := Nat.pow_pos (by decide)
      rw [Nat.pow_succ (2:Nat) k] at prev ⊢
      omega
    | fork a b =>
      have A := ih a
      have B := ih b
      simp only [count,length,Nat.mul_add]
      rw [Nat.pow_succ (2:Nat) (k+1)]
      rw [show k.succ+2=(k+2)+1 by omega]
      simp only [Nat.add_mul,Nat.one_mul] at *
      omega

theorem eligible_402 (t : Tree) (n : count t=402) : 3106≤weight t := by
  have h := external t 8
  have a := weight_length t
  rw [n] at h a
  omega

#print axioms eligible_402
end IncidenceLineTrieWeight
