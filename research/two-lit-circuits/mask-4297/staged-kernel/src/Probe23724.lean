import FreshBuild

namespace Probe23724
open ProbeFrontier PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.MissingCell

def pairs : Vector (Fin 5 × Fin 5) 15 := #v[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]

def inputs (p : Fin 15) : List Bool :=
  List.ofFn fun k : Fin 5 => decide (k=(pairs[p]).1 ∨ k=(pairs[p]).2)

def sig (n : ℕ) : Mask (Fin 15) := fun p => n.testBit p.val
def target := sig 617
def rawCodes : Vector ℕ 5 := #v[31,482,3652,13448,26896]
def raw (k : Fin 5) := sig rawCodes[k]
def start : Finset (Mask (Fin 15)) := Finset.univ.image raw

private theorem raw_correct : ∀ (k : Fin 5) (p : Fin 15),
    (inputs p).getD k.val false = raw k p := by decide +kernel

private theorem target_correct : ∀ p : Fin 15,
    (4297 : ℕ).testBit (5 * min (pairs[p]).1.val (pairs[p]).2.val +
      max (pairs[p]).1.val (pairs[p]).2.val) = target p := by decide +kernel

/-- Sufficient starting columns, even for a circuit with dead or invalid wires. -/
theorem physical_to_build (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 6)
    (out : ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k=i ∨ k=j)) =
      (4297 : ℕ).testBit (5*min i.val j.val + max i.val j.val)) :
    ∃ b t, b+t ≤ 6 ∧ Build target b t start := by
  obtain ⟨b,t,sz,run⟩ := simulate C.gates 5 C.output inputs (fun p => by simp [inputs]) fan
  have vals : (fun p => C.eval (inputs p)) = target := by
    funext p
    exact (out (pairs[p]).1 (pairs[p]).2).trans (target_correct p)
  change Run (fun p => C.eval (inputs p)) b t _ at run
  rw [vals] at run
  have nh : target ≠ zero := by intro e; have h := congrFun e 0; revert h; decide +kernel
  have nf : target ≠ one := by intro e; have h := congrFun e 1; revert h; decide +kernel
  obtain ⟨b',t',hb,ht,build⟩ := run.toBuild nh nf start (fun x hx => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have lt := live_lt C.gates 5 C.output i hi
    left
    exact Finset.mem_image.mpr ⟨⟨i,lt⟩,Finset.mem_univ _,(funext (raw_correct ⟨i,lt⟩)).symm⟩)
  change C.gates.length ≤ 6 at size
  exact ⟨b',t',by omega,build⟩

private theorem essential : ∀ k : Fin 5, ∃ i j : Fin 15, target i ≠ target j ∧
    ∀ l : Fin 5, raw l i ≠ raw l j → l=k := by decide +kernel

/-- Every separating subset of the initial bank is the full five-column bank. -/
theorem subset_essential (D : Finset (Mask (Fin 15))) (sub : D ⊆ start)
    (sep : ∀ i j : Fin 15, target i ≠ target j → ∃ x ∈ D, x i ≠ x j) : D=start := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,j,ht,hk⟩ := essential k
  obtain ⟨y,hy,hd⟩ := sep i j ht
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp (sub hy)
  exact hk l hd ▸ hy

end Probe23724
