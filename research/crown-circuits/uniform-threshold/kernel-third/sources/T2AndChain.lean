import T2PhysicalRowTags
import T2ThreeReaders

namespace ResidualSurplus
open private tag_old from GateSurplus

def closedRows (gs : List Raw) (ts : List Tag) :=
  (items ts.length (annotate gs ts)).reverse.filter
    (closedReader (fun i => (tagRead (extendTags gs ts) i).isNone))

def Charged (gs : List Raw) (ts : List Tag) (k : Nat) : Prop :=
  ∃ z ∈ (items ts.length (annotate gs ts)).reverse,
    z.1 = ts.length+k ∧
    closedReader (fun i => (tagRead (extendTags gs ts) i).isNone) z = true

theorem named_charge {gs : List Raw} (ts : List Tag) (a b : List Raw) (o : Op) (x y : Nat)
    (shape : gs = a ++ (o,x,y)::b)
    (pin : tagRead (extendTags gs ts) x ≠ none ∨ tagRead (extendTags gs ts) y ≠ none) :
    Charged gs ts a.length := by
  subst gs
  obtain ⟨z,mem,addr,hx,hy⟩ := named_item a b ts ts.length o x y
  refine ⟨z, by simpa using mem, addr, ?_⟩
  simp only [closedReader, hx, hy]
  rcases pin with p | p
  · cases h : tagRead (extendTags (a ++ (o,x,y)::b) ts) x with
    | none => exact (p h).elim
    | some v => rfl
  · cases h : tagRead (extendTags (a ++ (o,x,y)::b) ts) y with
    | none => exact (p h).elim
    | some v => simp

theorem three_charged {gs : List Raw} {ts : List Tag} {i j k : Nat} (ij : i<j) (jk : j<k)
    (a : Charged gs ts i) (b : Charged gs ts j) (c : Charged gs ts k) :
    3 ≤ (closedRows gs ts).length := by
  obtain ⟨p,pm,pi,pc⟩ := a
  obtain ⟨d,dm,dj,dc⟩ := b
  obtain ⟨t,tm,tk,tc⟩ := c
  exact three_closed_credits _ _ p d t (by omega) (by omega) (by omega) pm dm tm pc dc tc

/-- The two raw pins and the downstream AND-output pin charge different rows.
Lists a, b and c are the prefixes ending just before these three rows. -/
theorem and_chain_three (gs : List Raw) (ts : List Tag) (i : Nat)
    (a b c afterP afterD afterH : List Raw) (op oh : Op) (x y u v : Nat)
    (pShape : gs = a ++ (op,0,0)::afterP)
    (dShape : gs = b ++ (.and,x,y)::afterD)
    (hShape : gs = c ++ (oh,u,v)::afterH)
    (ab : a.length < b.length) (bc : b.length < c.length)
    (auxBound : 0 < ts.length) (aux : tagRead ts 0 = some true)
    (ib : i < ts.length) (pin : tagRead ts i = some false)
    (readsI : x=i ∨ y=i)
    (readsD : u=ts.length+b.length ∨ v=ts.length+b.length) :
    3 ≤ (closedRows gs ts).length := by
  have rawAux : tagRead (extendTags gs ts) 0 = some true :=
    (tag_old gs ts 0 auxBound).trans aux
  have rawX (rs : List Raw) : tagRead (extendTags rs ts) i = some false :=
    (tag_old rs ts i ib).trans pin
  have dreads (rs : List Raw) : tagRead (extendTags rs ts) x = some false ∨
      tagRead (extendTags rs ts) y = some false := by
    rcases readsI with rfl | rfl
    · exact Or.inl (rawX _)
    · exact Or.inr (rawX _)
  have dFalse : tagRead (extendTags gs ts) (ts.length+b.length) = some false := by
    rw [dShape]
    exact named_and_false b afterD ts x y (dreads b)
  apply three_charged ab bc
  · exact named_charge ts a afterP op 0 0 pShape (Or.inl (by simp [rawAux]))
  · apply named_charge ts b afterD .and x y dShape
    rcases dreads gs with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  · apply named_charge ts c afterH oh u v hShape
    rcases readsD with rfl | rfl
    · exact Or.inl (by simp [dFalse])
    · exact Or.inr (by simp [dFalse])

#print axioms and_chain_three
end ResidualSurplus
