import ThresholdThreeLayerUpper
import PEqualNP.Defs.MetaComplexityLgpMono
namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
def binaryBank (gs : List Gate) := ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2
def preserves {α : Type} (s : Build α) := ∀ gs,binaryBank gs → binaryBank (s.run gs).2
private theorem pure_ok {α : Type} (a : α) : preserves (pure a) := fun _ h => h
private theorem bind_ok {α β : Type} (s : Build α) (t : α → Build β)
    (a : preserves s) (b : ∀ x,preserves (t x)) : preserves (s >>= t) :=
  fun g h => b _ _ (a g h)
private theorem emit_ok (n a b : Nat) (o : GateOp) (ho : o=.and ∨ o=.or) :
    preserves (emit n o a b) := by
  intro gs h g mem
  change g∈gs++[⟨o,[a,b]⟩] at mem
  rcases List.mem_append.mp mem with old|new
  · exact h g old
  · have eq := List.mem_singleton.mp new
    subst g
    exact ⟨ho,rfl⟩
private theorem or_ok (n : Nat) (a b : Bit) : preserves (disj n a b) := by
  cases a <;> cases b <;> first | exact pure_ok _ | exact emit_ok _ _ _ _ (Or.inr rfl)
private theorem and_ok (n : Nat) (a b : Bit) : preserves (conj n a b) := by
  cases a <;> cases b <;> first | exact pure_ok _ | exact emit_ok _ _ _ _ (Or.inl rfl)
private theorem map_ok {α β : Type} (f : α → Build β) (h : ∀ a,preserves (f a))
    (items : List α) : preserves (items.mapM f) := by
  induction items with
  | nil => exact pure_ok _
  | cons a as ih =>
    rw [List.mapM_cons]
    exact bind_ok _ _ (h a) (fun _ => bind_ok _ _ ih (fun _ => pure_ok _))
private theorem fold_ok {α β : Type} (f : α → β → Build α) (h : ∀ a b,preserves (f a b))
    (items : List β) (start : α) : preserves (items.foldlM f start) := by
  induction items generalizing start with
  | nil => exact pure_ok _
  | cons b bs ih => exact bind_ok _ _ (h start b) ih
private theorem layer_ok {p q} (n) (a : Fin p → Finset (Fin q)) (src : List Bit) :
    preserves (layer n a src) := map_ok _ (fun _ => fold_ok _ (or_ok n) _ _) _
private theorem prefix_ok (n) (old : List Bit) (x : Bit) :
    preserves (prefixStep n old x) := by
  apply map_ok
  intro j
  by_cases e : j=0
  · simp only [e,if_pos,pure_bind]; exact or_ok _ _ _
  · simp only [if_neg e]; exact bind_ok _ _ (and_ok _ _ _) (fun t => or_ok _ _ _)
theorem circuit_binary {n v w z} (L : Layers n v w z) : binaryBank (circuit L).gates := by
  have hp : preserves (program L) :=
    bind_ok _ _ (layer_ok _ _ _) (fun _ =>
      bind_ok _ _ (layer_ok _ _ _) (fun _ =>
        bind_ok _ _ (layer_ok _ _ _) (fun _ =>
          bind_ok _ _ (fold_ok _ (prefix_ok _) _ _) (fun _ => pure_ok _))))
  exact hp [] (by simp [binaryBank])
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
theorem monotone2 {n v w z} (L : Layers n v w z) : PEqualNP.MetaComplexity.Monotone2 (circuit L) := by
  intro g mem
  obtain ⟨h,len⟩ := circuit_binary L g mem
  exact ⟨by simpa using h,by omega⟩
end ThresholdThreeLayerUpper
