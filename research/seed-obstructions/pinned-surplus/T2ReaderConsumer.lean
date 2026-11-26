import T2RawIsolation

namespace T2ReaderConsumer
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

theorem agree_last (w : List Bool) (a b : Bool) :
    AgreeOff w.length (w++[a]) (w++[b]) := by
  refine ⟨by simp, ?_⟩
  intro i ne
  by_cases lt : i < w.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
  · have le : w.length ≤ i := Nat.le_of_not_gt lt
    have beyond : 1 ≤ i-w.length := by omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_right le,
      List.getElem?_eq_none (show [a].length ≤ i-w.length by simpa using beyond),
      List.getElem?_eq_none (show [b].length ≤ i-w.length by simpa using beyond)]

/-- A sole reader transmitting a distinction must itself have a downstream
consumer whenever the output is neither the raw input nor that reader. -/
theorem exists_consumer (pre post : List Gate) (g : Gate) {x out : Nat} {u v : List Bool}
    (raw : AgreeOff x u v) (off : out ≠ x) (preMiss : ∀ row ∈ pre,x ∉ row.inputs)
    (postMiss : ∀ row ∈ post,x ∉ row.inputs) (obs : out ≠ (run pre v).length)
    (diff : Circuit.eval ⟨pre ++ g::post,out⟩ u ≠ Circuit.eval ⟨pre ++ g::post,out⟩ v) :
    ∃ row ∈ post, (run pre v).length ∈ row.inputs := by
  by_contra! absent
  have hpre := unread_run pre raw preMiss
  have first := (unread_run post (agree_push hpre (val g (run pre u))) postMiss).2 out off
  have second := (unread_run post (agree_last (run pre v) (val g (run pre u))
     (val g (run pre v))) absent).2 out obs
  apply diff
  change (run (pre ++ g::post) u).getD out false = (run (pre ++ g::post) v).getD out false
  simpa [run,val,List.foldl_append] using first.trans second

#print axioms exists_consumer
end T2ReaderConsumer
