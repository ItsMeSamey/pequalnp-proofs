import T2RawDirect
import T2SoleOrSuffix
import T2SoleOrSplice
import Mathlib.Data.Fin.Embedding

namespace T2CubeDeletion
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice

/-- Delete x from m+1 original raw inputs, preserving the order of the m
    surviving inputs. An optional leading true raw is used only by the
    temporary edit in the sole-AND case. -/
def embedded {m : Nat} (x : Fin (m+1)) (s : Finset (Fin m)) :=
  s.map (Fin.succAboveEmb x)

def baseTags {m : Nat} (x : Fin (m+1)) : List Tag :=
  List.ofFn (fun j : Fin (m+1) => if j=x then some false else none)

def tags {m : Nat} (aux : Bool) (x : Fin (m+1)) :=
  if aux then some true :: baseTags x else baseTags x

def large {m : Nat} (aux : Bool) (x : Fin (m+1)) (s : Finset (Fin m)) :=
  if aux then true :: vector (embedded x s) else vector (embedded x s)

def pinnedIndex {m : Nat} (aux : Bool) (x : Fin (m+1)) :=
  (if aux then 1 else 0) + x.val

def source (gs : List Raw) (out : Nat) : Circuit :=
  ⟨gs.map (fun (o,x,y) => binary o x y),out⟩

theorem embedded_card {m : Nat} (x : Fin (m+1)) (s : Finset (Fin m)) :
    (embedded x s).card=s.card := by simp [embedded]

theorem miss {m : Nat} (x : Fin (m+1)) (s : Finset (Fin m)) : x∉embedded x s := by
  intro h
  obtain ⟨j,_,eq⟩ := Finset.mem_map.mp h
  exact Fin.succAbove_ne x j eq

theorem survives {m : Nat} (x : Fin (m+1)) (s : Finset (Fin m)) (j : Fin m) :
    x.succAbove j∈embedded x s ↔ j∈s := by
  change (Fin.succAboveEmb x) j∈s.map (Fin.succAboveEmb x) ↔ _
  simp

private theorem port {m : Nat} (s : Finset (Fin m)) (j : Fin m) :
    (vector s).getD j.val false = decide (j∈s) := by
  simp [vector,List.getD_eq_getElem?_getD]

private theorem tagBase {m : Nat} (x j : Fin (m+1)) :
    tagRead (baseTags x) j.val = if j=x then some false else none := by
  simp only [tagRead,baseTags,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos j.isLt,Option.getD_some]

theorem closed {m : Nat} (aux : Bool) (x : Fin (m+1)) :
    tagRead (tags aux x) (pinnedIndex aux x) = some false := by
  have base : tagRead (baseTags x) x.val=some false := by rw [tagBase,if_pos rfl]
  cases aux with
  | false => simpa [tags,pinnedIndex] using base
  | true => simpa [tags,pinnedIndex,Nat.add_comm,tagRead,List.getD_eq_getElem?_getD] using base

theorem in_bounds {m : Nat} (aux : Bool) (x : Fin (m+1)) :
    pinnedIndex aux x < (tags aux x).length := by
  cases aux <;> simp [pinnedIndex,tags,baseTags] <;> have := x.isLt <;> omega

theorem fit {m : Nat} (aux : Bool) (x : Fin (m+1)) (s : Finset (Fin m)) :
    Fits (tags aux x) (large aux x s) := by
  have base : Fits (baseTags x) (vector (embedded x s)) := by
    refine ⟨by simp [baseTags,vector],?_⟩
    intro i
    by_cases h : i<m+1
    · let j : Fin (m+1) := ⟨i,h⟩
      change holds (tagRead (baseTags x) j.val) ((vector (embedded x s)).getD j.val false)
      rw [tagBase,port]
      by_cases eq : j=x
      · rw [eq]; simp [miss,holds]
      · simp [eq,holds]
    · have ht : ¬i<(baseTags x).length := by simpa [baseTags] using h
      have hv : ¬i<(vector (embedded x s)).length := by simpa [vector] using h
      simp [tagRead,List.getD_eq_getElem?_getD,ht,hv,holds]
  cases aux with
  | false => simpa [tags,large] using base
  | true =>
    refine ⟨by simp [tags,large,base.1],?_⟩
    intro i
    cases i with
    | zero => rfl
    | succ i => simpa [tags,large,tagRead,List.getD_eq_getElem?_getD] using base.2 i

/-- Total inverse on natural indices. Closed and out-of-range indices have a
    harmless default, since the reindexing theorem reads only open tags. -/
noncomputable def inverse {m : Nat} (x : Fin (m+1)) (i : Nat) : Nat := by
  classical
  exact if h : ∃ j : Fin m, (x.succAbove j).val=i then h.choose.val else 0

noncomputable def ren {m : Nat} (aux : Bool) (x : Fin (m+1)) (i : Nat) :=
  inverse x (i-(if aux then 1 else 0))

private theorem inverse_on {m : Nat} (x : Fin (m+1)) (j : Fin m) :
    inverse x (x.succAbove j).val=j.val := by
  classical
  have h : ∃ k : Fin m, (x.succAbove k).val=(x.succAbove j).val := ⟨j,rfl⟩
  have eu : (Fin.succAboveEmb x) h.choose=(Fin.succAboveEmb x) j := Fin.ext h.choose_spec
  simp only [inverse,dif_pos h]
  exact congrArg Fin.val ((Fin.succAboveEmb x).injective eu)

theorem supply {m : Nat} (aux : Bool) (x : Fin (m+1)) (i : Nat)
    (openTag : tagRead (tags aux x) i=none) :
    ren aux x i<m ∧ ∀ s : Finset (Fin m),
      (vector s).getD (ren aux x i) false=(large aux x s).getD i false := by
  have base (k : Nat) (hk : tagRead (baseTags x) k=none) :
      inverse x k<m ∧ ∀ s : Finset (Fin m),
        (vector s).getD (inverse x k) false=(vector (embedded x s)).getD k false := by
    have bound : k<m+1 := by
      by_contra h
      have ht : ¬k<(baseTags x).length := by simpa [baseTags] using h
      simp [tagRead,List.getD_eq_getElem?_getD,ht] at hk
    let d : Fin (m+1) := ⟨k,bound⟩
    have ne : d≠x := by
      intro eq
      have wrong : tagRead (baseTags x) d.val=some false := by rw [tagBase,if_pos eq]
      have bad : (none : Tag) = some false := hk.symm.trans wrong
      cases bad
    obtain ⟨j,eq⟩ := Fin.exists_succAbove_eq ne
    have valEq : (x.succAbove j).val=k := congrArg Fin.val eq
    rw [←valEq,inverse_on]
    exact ⟨j.isLt,fun s => by rw [port,port]; simp [survives]⟩
  cases aux with
  | false => simpa [ren,large] using base i (by simpa [tags] using openTag)
  | true =>
    cases i with
    | zero => simp [tagRead,tags,List.getD_eq_getElem?_getD] at openTag
    | succ i =>
      have h := base i (by simpa [tagRead,tags,List.getD_eq_getElem?_getD] using openTag)
      simpa [ren,large,List.getD_eq_getElem?_getD] using h

/-- Threshold semantics required only on the complete residual cube. The
    edited source is allowed to compute a different function off that cube. -/
def CorrectOn {m : Nat} (aux : Bool) (x : Fin (m+1)) (gs : List Raw) (out : Nat) : Prop :=
  ∀ s : Finset (Fin m), (source gs out).eval (large aux x s)=true ↔ 2≤s.card

theorem correct_on_plain {m : Nat} (x : Fin (m+1)) (gs : List Raw) (out : Nat)
    (hc : Computes (m+1) (source gs out)) : CorrectOn false x gs out := by
  intro s
  change (source gs out).eval (vector (embedded x s))=true ↔ 2≤s.card
  simpa only [embedded_card] using hc (embedded x s)

theorem correct_on_override {m : Nat} (x : Fin (m+1)) (original : Circuit)
    (edited : List Raw) (out : Nat) (hc : Computes (m+1) original)
    (same : ∀ s : Finset (Fin m),
      (source edited out).eval (true :: vector (embedded x s))=original.eval (vector (embedded x s))) :
    CorrectOn true x edited out := by
  intro s
  change (source edited out).eval (true :: vector (embedded x s))=true ↔ _
  rw [same,hc,embedded_card]

theorem threshold_witnesses {m : Nat} (two : 2≤m) :
    ∃ a b : Finset (Fin m), a=∅ ∧ b.card=2 := by
  let i : Fin m := ⟨0,by omega⟩
  let j : Fin m := ⟨1,by omega⟩
  have ne : i≠j := by intro e; have bad := congrArg Fin.val e; change (0:Nat)=1 at bad; omega
  exact ⟨∅,{i,j},rfl,by simp [ne]⟩

theorem nonconstant {m : Nat} (aux : Bool) (x : Fin (m+1)) (gs : List Raw) (out : Nat)
    (two : 2≤m) (hc : CorrectOn aux x gs out) :
    ∃ a b : Finset (Fin m),
      Circuit.eval ⟨(annotate gs (tags aux x)).map Row.full,out⟩ (large aux x a) ≠
      Circuit.eval ⟨(annotate gs (tags aux x)).map Row.full,out⟩ (large aux x b) := by
  obtain ⟨_,b,rfl,card⟩ := threshold_witnesses two
  refine ⟨∅,b,?_⟩
  simp only [annotation_full]
  change (source gs out).eval (large aux x ∅) ≠ (source gs out).eval (large aux x b)
  rw [(hc b).mpr (by omega)]
  intro h; have := (hc ∅).mp h; simp at this

def closedCount (gs : List Raw) (ts : List Tag) :=
  ((items ts.length (annotate gs ts)).reverse.filter
    (closedReader (fun j => (tagRead (extendTags gs ts) j).isNone))).length

theorem closed_deletion {m : Nat} (aux : Bool) (x : Fin (m+1)) (gs : List Raw)
    (out k : Nat) (two : 2≤m) (hc : CorrectOn aux x gs out)
    (valid : Valid (tags aux x).length (annotate gs (tags aux x)))
    (outOK : out < (tags aux x).length+(annotate gs (tags aux x)).length)
    (charges : k≤closedCount gs (tags aux x)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧ D.size+k≤gs.length := by
  let ts := tags aux x
  obtain ⟨D,mono,same,price⟩ := reader_deletion_minor gs ts out m
    (large aux x) vector (fit aux x) (fun s => by simp [vector]) valid outOK
    (nonconstant aux x gs out two hc) (ren aux x) (supply aux x)
  refine ⟨D,mono,?_,?_⟩
  · intro s; rw [same]; exact hc s
  · change D.size+closedCount gs ts≤(items ts.length (annotate gs ts)).length at price
    rw [items_annotated_length] at price
    exact (Nat.add_le_add_left charges D.size).trans price

theorem direct_deletion {m : Nat} (aux : Bool) (x : Fin (m+1)) (gs : List Raw)
    (out : Nat) (two : 2≤m) (hc : CorrectOn aux x gs out)
    (valid : Valid (tags aux x).length (annotate gs (tags aux x)))
    (outOK : out<(tags aux x).length+(annotate gs (tags aux x)).length) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧
      D.size+(gs.filter (rawReads (pinnedIndex aux x))).length≤gs.length := by
  obtain ⟨D,mono,same,price⟩ := direct_reader_deletion_minor gs (tags aux x) out m
    (large aux x) vector (fit aux x) (fun s => by simp [vector]) valid outOK
    (nonconstant aux x gs out two hc) (ren aux x) (supply aux x)
    (pinnedIndex aux x) (in_bounds aux x) (by rw [closed]; decide)
  refine ⟨D,mono,?_,price⟩
  intro s; rw [same]; exact hc s

theorem tags_len {m : Nat} (aux : Bool) (x : Fin (m+1)) :
    (tags aux x).length=(if aux then 1 else 0)+(m+1) := by
  cases aux <;> simp [tags,baseTags] <;> omega

theorem annotate_len (gs : List Raw) (ts : List Tag) : (annotate gs ts).length=gs.length := by
  simpa only [List.length_map] using congrArg List.length (annotation_full gs ts)

/-- Tag annotations preserve operand indices; hence physical properness alone
    supplies Valid (including for shifted/edited gates). -/
theorem valid_of_physical (gs : List Raw) (ts : List Tag)
    (ok : SuffixOK ts.length (source gs 0).gates) :
    Valid ts.length (annotate gs ts) := by
  induction gs generalizing ts with
  | nil => trivial
  | cons row gs ih =>
    obtain ⟨o,l,r⟩ := row
    change (∃ k : Op, ∃ u v, binary o l r=binary k u v ∧ u<ts.length ∧ v<ts.length) ∧
      SuffixOK (ts.length+1) (source gs 0).gates at ok
    obtain ⟨⟨k,u,v,eq,ul,vl⟩,tail⟩ := ok
    have pars : l=u ∧ r=v := by simpa [binary] using congrArg Gate.inputs eq
    obtain ⟨rfl,rfl⟩ := pars
    let more := ts ++ [foldTag o (tagRead ts l) (tagRead ts r)]
    have len : more.length=ts.length+1 := by simp [more]
    have IH := ih more (by simpa only [len] using tail)
    exact ⟨ul,vl,by simpa only [len] using IH⟩

theorem closed_deletion_physical {m : Nat} (aux : Bool) (x : Fin (m+1))
    (gs : List Raw) (out k : Nat) (two : 2≤m) (hc : CorrectOn aux x gs out)
    (ok : SuffixOK (tags aux x).length (source gs out).gates)
    (obs : out < (tags aux x).length+gs.length)
    (charges : k≤closedCount gs (tags aux x)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧ D.size+k≤gs.length :=
  closed_deletion aux x gs out k two hc (valid_of_physical gs _ ok)
    (by simpa only [annotate_len] using obs) charges

#print axioms closed_deletion
#print axioms direct_deletion
end T2CubeDeletion
