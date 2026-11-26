import FreshBuild

namespace Probe25057
open ProbeFrontier PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.MissingCell

def pairs : Vector (Fin 6 × Fin 6) 21 := #v[
  (0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),
  (2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(4,4),(4,5),(5,5)]

def inputs (p : Fin 21) : List Bool :=
  List.ofFn fun k : Fin 6 => decide (k=(pairs[p]).1 ∨ k=(pairs[p]).2)

def sig (n : ℕ) : Mask (Fin 21) := fun p => n.testBit p.val
def target := sig 302717
def rawCodes : Vector ℕ 6 := #v[63,1986,30852,233736,860688,1721376]
def raw (k : Fin 6) := sig rawCodes[k]
def start : Finset (Mask (Fin 21)) := Finset.univ.image raw

private theorem raw_correct : ∀ (k : Fin 6) (p : Fin 21),
    (inputs p).getD k.val false = raw k p := by decide +kernel

private theorem target_correct : ∀ p : Fin 21,
    (270585021 : ℕ).testBit (6 * min (pairs[p]).1.val (pairs[p]).2.val +
      max (pairs[p]).1.val (pairs[p]).2.val) = target p := by decide +kernel

/-- Sufficient starting columns, even for a circuit with dead or invalid wires. -/
theorem physical_to_build (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 9)
    (out : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k=i ∨ k=j)) =
      (270585021 : ℕ).testBit (6*min i.val j.val + max i.val j.val)) :
    ∃ b t, b+t ≤ 9 ∧ Build target b t start := by
  obtain ⟨b,t,sz,run⟩ := simulate C.gates 6 C.output inputs (fun p => by simp [inputs]) fan
  have vals : (fun p => C.eval (inputs p)) = target := by
    funext p
    exact (out (pairs[p]).1 (pairs[p]).2).trans (target_correct p)
  change Run (fun p => C.eval (inputs p)) b t _ at run
  rw [vals] at run
  have nh : target ≠ zero := by intro e; have h := congrFun e 0; revert h; decide +kernel
  have nf : target ≠ one := by intro e; have h := congrFun e 1; revert h; decide +kernel
  obtain ⟨b',t',hb,ht,build⟩ := run.toBuild nh nf start (fun x hx => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have lt := live_lt C.gates 6 C.output i hi
    left
    exact Finset.mem_image.mpr ⟨⟨i,lt⟩,Finset.mem_univ _,(funext (raw_correct ⟨i,lt⟩)).symm⟩)
  change C.gates.length ≤ 9 at size
  exact ⟨b',t',by omega,build⟩

private theorem essential : ∀ k : Fin 6, ∃ i j : Fin 21, target i ≠ target j ∧
    ∀ l : Fin 6, raw l i ≠ raw l j → l=k := by decide +kernel

/-- Every separating subset of the initial bank is the full six-column bank. -/
theorem subset_essential (D : Finset (Mask (Fin 21))) (sub : D ⊆ start)
    (sep : ∀ i j : Fin 21, target i ≠ target j → ∃ x ∈ D, x i ≠ x j) : D=start := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,j,ht,hk⟩ := essential k
  obtain ⟨y,hy,hd⟩ := sep i j ht
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp (sub hy)
  exact hk l hd ▸ hy

end Probe25057
