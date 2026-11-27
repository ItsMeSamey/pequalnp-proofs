import ShoreConstruction

namespace OnePerShore.Upper
open PEqualNP.Represents
open scoped BigOperators

theorem rowBuilt {n m} (i : Fin n) : Built (fun (u : Fin n) (_ : Fin m) => decide (u=i)) 1 :=
  ⟨.var (.inl i),.var _,fun u v => by simp [Compiler.Ex.eval,readFlag,eq_comm]⟩

theorem colBuilt {n m} (j : Fin m) : Built (fun (_ : Fin n) (v : Fin m) => decide (v=j)) 1 :=
  ⟨.var (.inr j),.var _,fun u v => by simp [Compiler.Ex.eval,readFlag,eq_comm]⟩

theorem rectBuilt {n m} (r : Finset (Fin n)) (c : Finset (Fin m)) (hr : r.Nonempty) (hc : c.Nonempty) :
    Built (fun u v => decide (u ∈ r ∧ v ∈ c)) (r.card+c.card) := by
  have a := built_any r (fun i (u : Fin n) (_ : Fin m) => decide (u=i)) (fun _ => 1)
    hr (fun i _ => rowBuilt i)
  have b := built_any c (fun j (_ : Fin n) (v : Fin m) => decide (v=j)) (fun _ => 1)
    hc (fun j _ => colBuilt j)
  simpa [anyOn] using a.and b

inductive Term (n m : ℕ) where
  | row (i : Fin n)
  | col (j : Fin m)
  | box (r : Finset (Fin n)) (c : Finset (Fin m))
deriving DecidableEq

def Term.weight {n m} : Term n m → ℕ
  | .row _ | .col _ => 1
  | .box r c => r.card+c.card

def Term.valid {n m} : Term n m → Prop
  | .row _ | .col _ => True
  | .box r c => r.Nonempty ∧ c.Nonempty

def Term.pred {n m} : Term n m → Pred n m
  | .row i => fun u _ => decide (u=i)
  | .col j => fun _ v => decide (v=j)
  | .box r c => fun u v => decide (u ∈ r ∧ v ∈ c)

theorem Term.built {n m} (t : Term n m) (h : t.valid) : Built t.pred t.weight := by
  cases t with
  | row i => exact rowBuilt i
  | col j => exact colBuilt j
  | box r c => exact rectBuilt r c h.1 h.2

theorem physical_of_partition {n m} (A : Pred n m) (terms : Finset (Term n m))
    (ne : terms.Nonempty) (valid : ∀ t ∈ terms,t.valid)
    (rep : ∀ u v, A u v = true ↔ ∃ t ∈ terms,t.pred u v = true)
    (count : ∑ t ∈ terms,t.weight = charged A) :
    RepSizeAtMost A (charged A - 1) := by
  have b := built_any terms Term.pred Term.weight ne (fun t ht => t.built (valid t ht))
  have eq : anyOn terms Term.pred = A := by
    funext u v; apply Bool.eq_iff_iff.mpr; simpa [anyOn] using (rep u v).symm
  rw [eq,count] at b
  exact b.realize

end OnePerShore.Upper
