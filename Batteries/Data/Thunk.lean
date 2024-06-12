namespace Thunk

@[ext]
theorem ext {α : Type u} {a b : Thunk α} (eq : a.get = b.get) : a = b := by
  have ⟨_⟩ := a
  have ⟨_⟩ := b
  congr
  exact funext fun _ => eq

end Thunk
