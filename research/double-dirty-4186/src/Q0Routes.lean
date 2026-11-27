import Graph18272Bridge
import Q0Readers
import Q0Partition

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
open S4183.S98

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem edge_reaches_top {u v : Fin n} (least : IsLeastAO G C) (edge : G.Adj u v) :
    ∃ t ∈ tops G C, gateVal n C t (pairInput u v) = true := by
  have hf : ∀ x : Fin n → Bool, Q0ReaderDeps.S90.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun least.2.1 x
  obtain ⟨t, ht, hnot, path, hv⟩ := Q0ReaderDeps.S90.edge_trace G (graphFun G ∅)
    (fun i j => (Q0ReaderDeps.S90.graphFun_pair G i j).mp) hf u v
    ((Q0ReaderDeps.S90.graphFun_pair G u v).mpr edge)
  have hand := (least.1.1 _ (Q0ReaderDeps.S90.gateAt_mem ht)).resolve_right hnot
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hand,
    Q0ReaderDeps.S90.below_of_reach _ hf t path⟩, hv⟩

theorem residual_gamma_cover (least : IsLeastAO G C)
    (ordinary : ∀ t ∈ tops G C, t ∉ centreless G C → ∀ u v : Fin n, G.Adj u v →
      gateVal n C t (pairInput u v) = true → s(u,v) ∈ starEdges G C) :
    Ustar G C ⊆ (centreless G C).biUnion (fun t => Ustar G C ∩ gammaE G C t) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hedge, hmissing⟩ := Finset.mem_sdiff.mp he
    have hadj : G.Adj u v := by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
    obtain ⟨t, ht, hv⟩ := edge_reaches_top least hadj
    have hc : t ∈ centreless G C := by
      by_contra hn
      exact hmissing (ordinary t ht hn u v hadj hv)
    exact Finset.mem_biUnion.mpr ⟨t, hc, Finset.mem_inter.mpr ⟨he, Finset.mem_filter.mpr ⟨hedge, u, v, rfl, hv⟩⟩⟩

abbrev DirtyRoute (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  Q0Partition.EndsAt (fun i j => i ∈ junk G C ∧ j ∈ readers n C i) (fun i => i ∈ centreless G C)

theorem some_dirty_route (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : (orN G C \ lam G C).card = 0) (g : ℕ) (hg : g ∈ junk G C) :
    ∃ t ∈ centreless G C, DirtyRoute n G C g t := by
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun D hD agree =>
    least.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_, hout⟩ := least_out n C hL
    (by obtain ⟨x, hx⟩ := gf_true n G edge; exact ⟨x, (hf x).trans hx⟩)
    (by intro u; obtain ⟨x, hu, hx⟩ := gf_var n G u; exact ⟨x, hu, (hf x).trans hx⟩)
  have walk (d : ℕ) : ∀ i, C.gates.length - i = d → i ∈ junk G C →
      ∃ t ∈ centreless G C, DirtyRoute n G C i t := by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hdi hi
      obtain ⟨hir, _, hbad⟩ := (S4183.junk_iff G C i).mp hi
      have hnout : n+i ≠ C.output := by
        intro he
        apply hbad
        intro x hx
        change W n C x (n+i) = true at hx
        rw [he] at hx
        exact (hf x).symm.trans hx
      obtain ⟨r, hir', hr, hin⟩ := least_read n C hL hout i (by omega)
      have hreader : r ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hin⟩
      have hnterminal : i ∉ centreless G C := by
        intro hc
        have ht : i ∈ tops G C := (Finset.mem_filter.mp hc).1
        exact hbad (Finset.mem_filter.mp ht).2.2
      by_cases hb : BelowF G C r
      · have hc := clean_dirty_reader_centreless least.1 hq hi hr hin hb
        exact ⟨r, hc, .next hnterminal ⟨hi, hreader⟩ (.stop hc)⟩
      · have ha := (least.1.1 _ (Q0ReaderDeps.S90.gateAt_mem hr)).resolve_right
          (dirty_reader_not_or least.1 hq hi hr hin)
        have hj := (S4183.junk_iff G C r).mpr ⟨hr, ha, hb⟩
        obtain ⟨t, ht, tail⟩ := ih (C.gates.length-r) (by omega) r rfl hj
        exact ⟨t, ht, .next hnterminal ⟨hi, hreader⟩ tail⟩
  exact walk _ g rfl hg

noncomputable def routedJunk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (t : ℕ) : Finset ℕ := by
  classical
  exact (junk G C).filter (fun d => DirtyRoute n G C d t)

theorem mem_routedJunk {t d : ℕ} :
    d ∈ routedJunk n G C t ↔ d ∈ junk G C ∧ DirtyRoute n G C d t := by
  classical
  exact Finset.mem_filter

theorem routedJunk_covers (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : (orN G C \ lam G C).card = 0) :
    (centreless G C).biUnion (routedJunk n G C) = junk G C := by
  classical
  ext d
  constructor
  · intro h
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp h
    exact (mem_routedJunk.mp ht).1
  · intro hd
    obtain ⟨t, ht, hdt⟩ := some_dirty_route edge least hq d hd
    exact Finset.mem_biUnion.mpr ⟨t, ht, mem_routedJunk.mpr ⟨hd, hdt⟩⟩

end PEqualNP.Outside.L_meta_4186_aux.Q0
