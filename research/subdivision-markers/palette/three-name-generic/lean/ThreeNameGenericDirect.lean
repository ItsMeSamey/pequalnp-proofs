import ThreeNameGenericPositive

namespace ThreeNameGenericDirect
open ThreeNameGenericPositive ThreeNamePacked ThreeNamePinReduction

def tagPair (u v : Bool) : Tags := fun j => if j = 0 then bit u else bit v

def namedWord {w : Nat} (target a b : BitVec w) (u v y : Bool) : BitVec w :=
  ((if y then target else 0) ^^^ (if u then a else 0)) ^^^ (if v then b else 0)

private theorem pick {w : Nat} (b : Bool) (x : BitVec w) :
    decode (if b then x else 0) = bit b • decode x := by
  cases b
  · change decode (0 : BitVec w) = (0 : F) • decode x
    rw [decode_zero,zero_smul]
  · change decode x = (1 : F) • decode x
    rw [one_smul]

theorem decode_namedWord {w : Nat} (target a b : BitVec w) (u v y : Bool) :
    decode (namedWord target a b u v y) = named target a b (tagPair u v,bit y) := by
  simp only [namedWord,decode_xor,pick,named_apply]
  have h0 : tagPair u v 0 = bit u := by simp [tagPair]
  have h1 : tagPair u v 1 = bit v := by simp [tagPair]
  rw [h0,h1]

def checkConflict {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (pins : List I) (target a b : BitVec w) (u v y : Bool) (witness : List I) : Bool :=
  (u || v) && witness.all (fun i => decide (i ∈ pins)) &&
    decide (xorSum (witness.map col) = namedWord target a b u v y)

theorem conflict_no {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (pins : List I) (target a b : BitVec w) (u v y : Bool) (witness : List I)
    (ok : checkConflict col pins target a b u v y witness = true) :
    ∀ A : Finset I, pins.toFinset ⊆ A → ¬ Exact (fun i => decode (col i)) (named target a b) A := by
  simp only [checkConflict,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨nonzero,inside⟩,word⟩ := ok
  intro A hA he
  have hm := xor_mem col A witness (fun i hi => hA (List.mem_toFinset.mpr (inside i hi)))
  rw [word,decode_namedWord] at hm
  have eq := (he (tagPair u v) (bit y)).mp hm
  have h0 := congrFun eq (0 : Fin 2)
  have h1 := congrFun eq (1 : Fin 2)
  cases u <;> cases v <;> simp_all [tagPair,bit]

def checkOutside {I : Type*} [Fintype I] {w : Nat} (col : I → BitVec w)
    (target : BitVec w) (row : List (Fin w)) : Bool :=
  parity row target && decide (∀ i, parity row (col i) = false)

theorem outside_no {I : Type*} [DecidableEq I] [Fintype I] {w : Nat} (col : I → BitVec w)
    (target a b : BitVec w) (row : List (Fin w)) (ok : checkOutside col target row = true) :
    ∀ A : Finset I, ¬ Exact (fun i => decode (col i)) (named target a b) A := by
  simp only [checkOutside,Bool.and_eq_true,decide_eq_true_eq] at ok
  intro A h
  have ax := (h 0 1).mpr rfl
  have targetMem : decode target ∈ indexedSpan (fun i => decode (col i)) A := by
    simpa [named_apply] using ax
  have le : indexedSpan (fun i => decode (col i)) A ≤ LinearMap.ker (functional row) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,_,rfl⟩
    change functional row (decode (col i)) = 0
    rw [functional_decode,ok.2 i]
    rfl
  have hz : functional row (decode target) = 0 := le targetMem
  rw [functional_decode,ok.1] at hz
  exact one_ne_zero hz

example : checkConflict (fun _ : Fin 1 => (3 : BitVec 3)) [0] 1 2 4 true false true [0] = true := by decide
example : checkConflict (fun _ : Fin 1 => (3 : BitVec 3)) [] 1 2 4 true false true [0] = false := by decide
example : checkOutside (fun _ : Fin 2 => (4 : BitVec 3)) 1 [0] = true := by decide
example : checkOutside (fun _ : Fin 2 => (1 : BitVec 3)) 1 [0] = false := by decide

#print axioms conflict_no
#print axioms outside_no
end ThreeNameGenericDirect
