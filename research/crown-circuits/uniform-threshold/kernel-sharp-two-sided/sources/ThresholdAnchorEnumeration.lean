import ThresholdRemoteSchedule
namespace ThresholdPeelSchedule
variable {ι : Type*} {m : Nat}

theorem index_names (tag : Fin m → ι) (pair : ι → Fin m × Fin m)
    (indices : List ι) (nd : indices.Nodup)
    (left : ∀ c∈indices, tag (pair c).1=c)
    (right : ∀ c∈indices, tag (pair c).2=c)
    (distinct : ∀ c∈indices, (pair c).1≠(pair c).2) : (names (indices.map pair)).Nodup := by
  induction indices with
  | nil => simp [names]
  | cons c cs ih =>
    have h := List.nodup_cons.mp nd
    have loc {i : Fin m} (mem : i∈names (cs.map pair)) : ∃ d∈cs, tag i=d := by
      obtain ⟨q,hq,hit⟩ := List.mem_flatMap.mp mem
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
      have hd' : d∈c::cs := .tail _ hd
      rcases List.mem_cons.mp hit with rfl | hit
      · exact ⟨d,hd,left d hd'⟩
      · obtain rfl := List.mem_singleton.mp hit
        exact ⟨d,hd,right d hd'⟩
    have fresh (i : Fin m) (eq : tag i=c) : i∉names (cs.map pair) := by
      intro hit
      obtain ⟨d,hd,ed⟩ := loc hit
      exact h.1 ((eq.symm.trans ed).symm ▸ hd)
    change ((pair c).1::(pair c).2::names (cs.map pair)).Nodup
    exact List.nodup_cons.mpr ⟨by simp [distinct c (by simp),fresh _ (left c (by simp))],
      List.nodup_cons.mpr ⟨fresh _ (right c (by simp)),ih h.2
        (fun d hd => left d (.tail _ hd)) (fun d hd => right d (.tail _ hd))
        (fun d hd => distinct d (.tail _ hd))⟩⟩
end ThresholdPeelSchedule
