import Mathlib.SetTheory.Cardinal.Basic

namespace Cardinal

instance countable_of_mk_eq_aleph0 {α : Type w} (h : #α = ℵ₀) : Countable α := by
  apply mk_le_aleph0_iff.mp
  rw [h]
