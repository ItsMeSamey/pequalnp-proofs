import ThresholdInteriorSchedule
namespace ThresholdPeelSchedule
variable {V E : Type*} [Fintype V] [DecidableEq V] {m : Nat}
    (j : V ↪ Fin m) (G : SimpleGraph V) (f : Pins m → Bool) (ends : E → Pins m)

theorem path_rows (rows : EdgeRows ends f)
    (edge : ∀ {a b}, G.Adj a b → ∃ e, ends e={j a,j b}) : PathRows j G f := by
  constructor
  · intro w z wz
    obtain ⟨e,eq⟩ := edge wz
    simpa [eq] using rows.single e
  · intro x w z xz xw wz
    obtain ⟨d,hd⟩ := edge xw
    obtain ⟨e,he⟩ := edge wz
    have ne : e≠d := by
      intro ed
      have hit : j x∈ends e := by simp [ed,hd]
      simpa [he,xw.ne,xz] using hit
    have union : ends e ∪ ends d=insert (j x) {j w,j z} := by
      ext i; simp [he,hd]
    exact union ▸ rows.pair e d ne
end ThresholdPeelSchedule
