import ThresholdPeelSchedule
namespace ThresholdPeelSchedule

structure EdgeRows {m} {E : Type*} (ends : E → Pins m) (f : Pins m → Bool) : Prop where
  single : ∀ e, f (ends e)=false
  pair : ∀ e d, e≠d → f (ends e ∪ ends d)=true

theorem ready_interior_edges {m} {E : Type*} {ends : E → Pins m} {f : Pins m → Bool}
    (rep : EdgeRows ends f) {u z : Pins m} {p : Fin m} (e d : E)
    (ed : e≠d) (change : ends e ∪ ends d=insert p (ends e))
    (sub : insert p (ends e) ⊆ u) (fresh : p∉ends e)
    (zsub : z ⊆ u) (ret : p∉z) (pos : f z=true) : Ready f u (.interior p) :=
  ⟨ends e,z,sub,zsub,fresh,ret,rep.single e,change ▸ rep.pair e d ed,pos⟩

theorem ready_remote_edges {m} {E : Type*} {ends : E → Pins m} {f : Pins m → Bool}
    (rep : EdgeRows ends f) {u z : Pins m} {a b : Fin m} (e d : E)
    (ed : e≠d) (ab : a≠b) (anchor : ends d={a,b})
    (sub : insert b (insert a (ends e)) ⊆ u) (af : a∉ends e) (bf : b∉ends e)
    (zsub : z ⊆ u) (az : a∉z) (bz : b∉z) (pos : f z=true) : Ready f u (.remote a b) := by
  have union : ends e ∪ ends d=insert b (insert a (ends e)) := by
    ext i; simp [anchor]; tauto
  exact ⟨ab,ends e,z,sub,zsub,af,bf,az,bz,rep.single e,union ▸ rep.pair e d ed,pos⟩
end ThresholdPeelSchedule
