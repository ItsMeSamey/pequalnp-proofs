import GateSurplus

namespace T2RawIsolation
open PEqualNP.CircuitLowerBounds
open ResidualSurplus

def AgreeOff (x : Nat) (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i, i ≠ x → u.getD i false = v.getD i false

theorem agree_push {x : Nat} {u v : List Bool} (h : AgreeOff x u v) (b : Bool) :
    AgreeOff x (u ++ [b]) (v ++ [b]) := by
  obtain ⟨len, same⟩ := h
  refine ⟨by simp [len], ?_⟩
  intro i hi
  by_cases hu : i < u.length
  · have hv : i < v.length := len ▸ hu
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hu,
      List.getElem?_append_left hv] using same i hi
  · have hu' : u.length ≤ i := Nat.le_of_not_gt hu
    have hv' : v.length ≤ i := len ▸ hu'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hu',
      List.getElem?_append_right hv', len]

theorem unread_gate {x : Nat} {u v : List Bool} (h : AgreeOff x u v) (g : Gate)
    (miss : x ∉ g.inputs) : val g u = val g v := by
  unfold val
  congr 1
  apply List.map_congr_left
  intro i hi
  apply h.2
  exact fun e => miss (e ▸ hi)

theorem unread_run (gs : List Gate) {x : Nat} {u v : List Bool} (h : AgreeOff x u v)
    (miss : ∀ g ∈ gs, x ∉ g.inputs) : AgreeOff x (run gs u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    change AgreeOff x (run gs (u ++ [val g u])) (run gs (v ++ [val g v]))
    apply ih _ (fun a ha => miss a (by simp [ha]))
    rw [unread_gate h g (miss g (by simp))]
    exact agree_push h _

/-- If one physical reader is insensitive on two input assignments that
differ only at x, no other output wire can distinguish them. -/
theorem isolated_reader (before after : List Gate) (g : Gate) {x out : Nat}
    {u v : List Bool} (h : AgreeOff x u v) (notOutput : out ≠ x)
    (pre : ∀ row ∈ before, x ∉ row.inputs)
    (post : ∀ row ∈ after, x ∉ row.inputs)
    (eq : val g (run before u) = val g (run before v)) :
    (run (before ++ g :: after) u).getD out false =
      (run (before ++ g :: after) v).getD out false := by
  let hpre := unread_run before h pre
  have hs : AgreeOff x (run before u ++ [val g (run before u)])
      (run before v ++ [val g (run before v)]) := by
    rw [eq]
    exact agree_push hpre _
  have hout := (unread_run after hs post).2 out notOutput
  simpa [run, val, List.foldl_append] using hout

#print axioms isolated_reader
end T2RawIsolation
