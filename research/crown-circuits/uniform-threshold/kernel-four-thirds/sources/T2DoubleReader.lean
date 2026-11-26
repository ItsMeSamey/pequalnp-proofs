import T2MinimalLive
import T2CubeDeletion
import T2AndChain

namespace T2DoubleReader
open ResidualSurplus PEqualNP.CircuitLowerBounds T2SoleOrSplice T2CubeDeletion
open private tag_old from GateSurplus

def At (gs : List Raw) (i : Nat) (r : Raw) : Prop :=
  ∃ a b, gs=a++r::b ∧ i=a.length

def Reads (r : Raw) (x : Nat) := r.2.1=x ∨ r.2.2=x

theorem no_duplicate_raw (n x out : Nat) (a b : List Raw) (o : Op)
    (hx : x<n+a.length) : ¬ LexMinimum n (source (a++(o,x,x)::b) out) := by
  intro m
  let f := fun (r : Raw) => binary r.1 r.2.1 r.2.2
  apply T2MinimalLive.no_duplicate_at_minimum n x out (a.map f) (b.map f) o
  · convert m using 1 <;> simp [source,f,List.map_append]
  · simpa using hx

private theorem at_unique {gs : List Raw} {i : Nat} {r t : Raw}
    (a : At gs i r) (b : At gs i t) : r=t := by
  have get {v : Raw} (h : At gs i v) : gs[i]?=some v := by
    obtain ⟨pre,post,rfl,rfl⟩ := h
    simp [List.getElem?_append]
  exact Option.some.inj ((get a).symm.trans (get b))

private theorem charged_at {gs : List Raw} {i w : Nat} {r : Raw} {ts : List Tag}
    (h : At gs i r) (reader : Reads r w) (off : tagRead (extendTags gs ts) w≠none) :
    Charged gs ts i := by
  obtain ⟨a,b,eq,rfl⟩ := h
  obtain ⟨o,l,u⟩ := r
  apply named_charge ts a b o l u eq
  change l=w ∨ u=w at reader
  exact reader.elim (fun hl => Or.inl (by simpa only [hl] using off))
    (fun hu => Or.inr (by simpa only [hu] using off))

private theorem any_three {gs : List Raw} {ts : List Tag} {i j k : Nat}
    (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (a : Charged gs ts i) (b : Charged gs ts j) (c : Charged gs ts k) :
    3≤closedCount gs ts := by
  obtain ⟨p,pm,pi,pc⟩ := a
  obtain ⟨d,dm,dj,dc⟩ := b
  obtain ⟨t,tm,tk,tc⟩ := c
  exact three_closed_credits _ _ p d t (by omega) (by omega) (by omega) pm dm tm pc dc tc

private theorem use_after {m : Nat} {x : Fin (m+1)} {gs : List Raw} {out i : Nat} {r : Raw}
    (lc : LexMinimum (m+1) (source gs out)) (atI : At gs i r)
    (notOut : out≠m+1+i) :
    ∃ j t, i < j ∧ At gs j t ∧ Reads t (m+1+i) := by
  obtain ⟨pre,post,rfl,rfl⟩ := atI
  let f := fun (s : Raw) => binary s.1 s.2.1 s.2.2
  obtain ⟨o,l,u⟩ := r
  have src : source (pre++(o,l,u)::post) out =
      ⟨pre.map f ++ binary o l u :: post.map f,out⟩ := by
    simp [source,f,List.map_append]
  have min' : LexMinimum (m+1) ⟨pre.map f++binary o l u::post.map f,out⟩ := src ▸ lc
  obtain ⟨a,mem,read⟩ := T2MinimalLive.consumer_at_minimum (m+1) x.val out (pre.map f)
    (post.map f) (binary o l u) min' (by have := x.isLt; simp; omega) (by simpa using notOut)
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp mem
  obtain ⟨before,after,eq⟩ := List.append_of_mem ht
  subst post
  refine ⟨(pre++(o,l,u)::before).length,t,by simp,
    ⟨pre++(o,l,u)::before,after,by simp [List.append_assoc],rfl⟩,?_⟩
  obtain ⟨op,y,z⟩ := t
  simpa [f,binary,Reads,eq_comm] using read

theorem double_and_deletion {m : Nat} (x : Fin (m+1)) (gs : List Raw) (out i b : Nat)
    (r s : Raw) (two : 2≤m) (lc : LexMinimum (m+1) (source gs out))
    (atG : At gs i r) (andG : r.1=.and) (rawG : Reads r x.val)
    (atB : At gs b s) (rawB : Reads s x.val) (distinct : i≠b) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧ D.size+3≤gs.length := by
  let ts := tags false x
  have width : ts.length=m+1 := by simp [ts,tags_len]
  have correct := correct_on_plain x gs out lc.eligible.1
  obtain ⟨v,w,sep⟩ := nonconstant false x gs out two correct
  have openOut := open_of_nonconstant gs ts out _ _ (fit false x v) (fit false x w) sep
  let tag := tagRead (extendTags gs ts)
  have off : tag x.val=some false := by
    unfold tag
    rw [tag_old _ _ _ (by have := x.isLt; omega)]
    simpa [ts,pinnedIndex] using closed false x
  have chargeG := charged_at (ts:=ts) atG rawG (by change tag x.val≠none; rw [off]; decide)
  have chargeB := charged_at (ts:=ts) atB rawB (by change tag x.val≠none; rw [off]; decide)
  have gOff : tag (m+1+i)=some false := by
    obtain ⟨pre,post,eq,idx⟩ := atG
    obtain ⟨o,l,u⟩ := r
    change o=.and at andG
    subst o
    have addr : m+1+i=ts.length+pre.length := by omega
    rw [addr]
    unfold tag
    rw [eq]
    apply named_and_false
    have hx : tagRead (extendTags pre ts) x.val=some false := by
      rw [tag_old _ _ _ (by have := x.isLt; omega)]
      simpa [ts,pinnedIndex] using closed false x
    change l=x.val ∨ u=x.val at rawG
    rcases rawG with h|h
    · exact Or.inl (by simpa only [h] using hx)
    · exact Or.inr (by simpa only [h] using hx)
  have notG : out≠m+1+i := by intro eq; rw [eq] at openOut; simpa [tag,openOut] using gOff
  obtain ⟨j,t,ij,atJ,useG⟩ := use_after (x:=x) lc atG notG
  have jCharge := charged_at (ts:=ts) atJ useG (by change tag (m+1+i)≠none; rw [gOff]; decide)
  have score : 3≤closedCount gs ts := by
    by_cases overlap : j=b
    · subst j
      have identical := at_unique atJ atB
      subst t
      have xo : x.val≠m+1+i := by have := x.isLt; omega
      have bOff : tag (m+1+b)=some false := by
        obtain ⟨pre,post,eq,idx⟩ := atB
        obtain ⟨op,l,u⟩ := s
        have operands : (l=x.val ∧ u=m+1+i) ∨ (u=x.val ∧ l=m+1+i) := by
          change l=x.val ∨ u=x.val at rawB
          change l=m+1+i ∨ u=m+1+i at useG
          rcases rawB with h|h <;> rcases useG with z|z <;> omega
        let base := extendTags pre ts
        have xpre : tagRead base x.val=some false := by
          change tagRead (extendTags pre ts) x.val=some false
          rw [tag_old _ _ _ (by have := x.isLt; omega)]
          simpa [ts,pinnedIndex] using closed false x
        have gp : tagRead base (m+1+i)=some false := by
          have full := gOff
          change tagRead (extendTags gs ts) (m+1+i)=some false at full
          rw [eq,extendTags_append,tag_old] at full
          · exact full
          · simp [extendTags_length,width]; omega
        change tagRead (extendTags gs ts) (m+1+b)=some false
        have addr : m+1+b=ts.length+pre.length := by omega
        rw [addr,eq,named_row_tag]
        rcases operands with ⟨hl,hu⟩|⟨hu,hl⟩ <;>
          simp only [hl,hu,show extendTags pre ts=base from rfl,xpre,gp] <;>
          cases op <;> rfl
      have notB : out≠m+1+b := by intro eq; rw [eq] at openOut; simpa [tag,openOut] using bOff
      obtain ⟨k,q,bk,atK,useB⟩ := use_after (x:=x) lc atB notB
      have kCharge := charged_at (ts:=ts) atK useB (by change tag (m+1+b)≠none; rw [bOff]; decide)
      exact any_three distinct (by omega) (by omega) chargeG chargeB kCharge
    · exact any_three distinct (by omega) (Ne.symm overlap) chargeG chargeB jCharge
  have hc := (eligible_iff (m+1) (source gs out)).mp lc.eligible
  apply closed_deletion_physical false x gs out 3 two correct
  · change SuffixOK ts.length (source gs out).gates
    rw [width]; exact hc.2.2
  · change out<ts.length+gs.length
    rw [width]; simpa [source,Circuit.size] using hc.2.1
  · exact score

#print axioms double_and_deletion
end T2DoubleReader
