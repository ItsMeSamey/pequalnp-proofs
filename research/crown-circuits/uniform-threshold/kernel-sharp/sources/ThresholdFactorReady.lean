import ThresholdFactorForest
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open ThresholdFactorExpr ThresholdFactorRecipe ThresholdFactorNetwork ThresholdFactorForest
namespace ThresholdFactorReady
private theorem treeAvail {C : Circuit} {n} (t : Tree) (seen : List Nat)
    (checked : t.Checked C n) (refs : ∀ j∈t.exts,j∈seen) : (treeTerm t).Avail n seen := by
  induction t with
  | raw i => exact checked
  | external i => exact refs i (by simp [Tree.exts])
  | join j l r hl hr =>
    exact ⟨hl checked.2.1 (fun i hi => refs i (by simp [Tree.exts,hi])),
      hr checked.2.2 (fun i hi => refs i (by simp [Tree.exts,hi]))⟩

private theorem disjAvail (xs : List Term) (n : Nat) (seen : List Nat)
    (ok : ∀ t∈xs,t.Avail n seen) : ∀ t,disj xs=some t → t.Avail n seen := by
  induction xs with
  | nil => simp [disj]
  | cons x xs ih =>
    cases e : disj xs with
    | none =>
      intro t ht
      simp [disj,e] at ht
      exact ht ▸ ok x (by simp)
    | some a =>
      intro t ht
      simp [disj,e] at ht
      exact ht ▸ And.intro (ok x (by simp)) (ih (fun t h => ok t (by simp [h])) a e)

private theorem factorAvail {C : Circuit} {n x : Nat} (hx : x<n) (a b : Tree) (seen : List Nat)
    (ac : a.Checked C n) (bc : b.Checked C n)
    (ra : ∀ j∈a.exts,j∈seen) (rb : ∀ j∈b.exts,j∈seen) : (factored x a b).Avail n seen := by
  have chk (t : Tree) (tc : t.Checked C n) : ∀ j∈t.raws,j<n := by
    induction t with
    | raw i => simpa [Tree.raws,Tree.Checked] using tc
    | external i => simp [Tree.raws]
    | join j l r hl hr => intro i mem; exact (List.mem_append.mp mem).elim (hl tc.2.1 i) (hr tc.2.2 i)
  have valid (t : Tree) (tc : t.Checked C n) (ref : ∀ j∈t.exts,j∈seen) :
      ∀ q∈residual x t,q.Avail n seen := by
    intro q hq
    rcases List.mem_append.mp hq with raw|other
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp raw
      exact chk t tc i (List.mem_of_mem_erase hi)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp other
      exact ref i hi
  cases el : disj (residual x a) with
  | none => simpa [factored,el,Term.Avail] using hx
  | some l =>
    cases er : disj (residual x b) with
    | none => simpa [factored,el,er,Term.Avail] using hx
    | some r =>
      simp only [factored,el,er,Term.Avail]
      exact ⟨hx,disjAvail _ _ _ (valid a ac ra) l el,disjAvail _ _ _ (valid b bc rb) r er⟩

theorem jobs_ready {C : Circuit} {n x z : Nat} {a b : Tree} {bs : List Block}
    (cut : Cut C n x z a b bs) (book : Book C n [] bs) :
    valid n [] (bs.map (job x z a b)) := by
  obtain ⟨p,pa⟩ := cut.leftIn
  obtain ⟨q,qb⟩ := cut.rightIn
  have uniq := List.inj_on_of_nodup_map cut.distinctOutputs
  have step (todo : List Block) (seen : List Nat)
      (mem : ∀ g∈todo,g∈bs) (ok : Book C n seen todo)
      (depA : a.out∈seen → ∀ k∈a.exts,k∈seen)
      (depB : b.out∈seen → ∀ k∈b.exts,k∈seen) :
      valid n seen (todo.map (job x z a b)) := by
    induction todo generalizing seen with
    | nil => trivial
    | cons g gs ih =>
      obtain ⟨check,refs,rest⟩ := ok
      have hg := mem g (by simp)
      have extend (t : Tree) (pin : Nat) (occ : Block.group pin t∈bs)
          (prior : t.out∈seen → ∀ k∈t.exts,k∈seen) :
          t.out∈g.out::seen → ∀ k∈t.exts,k∈g.out::seen := by
        intro ht k hk
        rcases List.mem_cons.mp ht with eq|old
        · have same : g=.group pin t := uniq hg occ eq.symm
          subst g
          exact List.mem_cons_of_mem _ (refs k hk)
        · exact List.mem_cons_of_mem _ (prior old k hk)
      refine ⟨?_,ih _ (fun h memH => mem h (by simp [memH])) rest (extend a p pa depA) (extend b q qb depB)⟩
      change (target x z a b g).Avail n seen
      unfold target
      split
      · exact cut.raw
      · split
        next gmeet =>
          have same : g=.meet z a.out b.out := uniq hg cut.meetIn gmeet
          subst g
          exact factorAvail cut.raw a b seen cut.left cut.right
            (depA (refs a.out (by simp [Block.exts]))) (depB (refs b.out (by simp [Block.exts])))
        next =>
          cases g with
          | meet j l r => exact ⟨refs l (by simp [Block.exts]),refs r (by simp [Block.exts])⟩
          | group p t => exact treeAvail t seen check refs
  exact step bs [] (fun _ h => h) book (by simp) (by simp)

theorem exclude {C : Circuit} {n x z : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat)
    (internal : MeetsInternal L) (mini : T2SoleOrSplice.LexMinimum n C) (hn : 2≤n)
    (a b : Tree) (cut : Cut C n x z a b (forest L pin)) : False := by
  have ready := jobs_ready cut (extracted_book L internal pin)
  obtain ⟨D,mono,price,same⟩ := actual_saving L pin a b cut
    (T2BenchmarkNormalize.output_internal mini.eligible) ready
  have computes : T2SoleOrSplice.Computes n D := by
    intro s
    rw [same _ (by simp [T2SoleOrSplice.vector])]
    exact mini.eligible.1 s
  obtain ⟨E,good,cost⟩ := T2BenchmarkNormalize.canNormalize hn D mono computes
  have least := mini.primary E good
  omega
end ThresholdFactorReady
