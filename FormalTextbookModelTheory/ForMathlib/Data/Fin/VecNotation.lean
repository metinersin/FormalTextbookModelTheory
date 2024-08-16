import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin

namespace Matrix

variable {α β: Type*}

lemma Vector_eq_VecNotation₂ (v : Fin 2 → α) : v = ![v 0, v 1] := by
  simp only [vecCons]
  induction (‹_› : Fin _ → α) using Fin.consCases
  simp only [Fin.cons_eq_cons]
  induction (‹_› : Fin _ → α) using Fin.consCases
  simp only [Fin.cons_eq_cons]
  simp only [Fin.cons_zero, Fin.cons_one, true_and]
  apply (by infer_instance : Subsingleton (Fin 0 → α)).allEq

@[simp]
lemma comp_VecNotation₂ (f : α → β) (x y : α) : f ∘ ![x, y] = ![f x, f y] := by
  ext x
  rcases x with ⟨i, h⟩
  match i with
  | 0 => rfl
  | 1 => rfl

end Matrix
