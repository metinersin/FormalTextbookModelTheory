import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Order

universe u v w

open Cardinal
open FirstOrder Language Structure

namespace FirstOrder.Language

class IsRelational₂ (L : Language.{u, v}) extends IsRelational L : Prop where
  only_rel₂ : ∀ {n}, n ≠ 2 → IsEmpty (L.Relations n)

namespace Structure --region Structure

variable {L : Language.{u, v}} {M : Type w}

section Relational

lemma funMap_eq_funMap_of_relational [IsRelational L] (𝓜₁ 𝓜₂ : L.Structure M)
    : @funMap L M 𝓜₁ = @funMap L M 𝓜₂ := by
  rw [Subsingleton.elim (@funMap L M 𝓜₁) (@funMap L M 𝓜₂)]

lemma funMap_eq_funMap_of_relational' [IsRelational L] (𝓜₁ 𝓜₂ : L.Structure M)
    {n} (nFun : L.Functions n) (x : Fin n → M)
    : 𝓜₁.funMap nFun x = 𝓜₂.funMap nFun x := by
  rw [Subsingleton.elim (𝓜₁.funMap) (𝓜₂.funMap)]

@[ext]
lemma structure_eq_structure_of_relational [IsRelational L]
    {𝓜₁ 𝓜₂ : L.Structure M} (h : @RelMap L M 𝓜₁ = @RelMap L M 𝓜₂) : 𝓜₁ = 𝓜₂ := by
  ext1
  · apply funMap_eq_funMap_of_relational
  · apply h

lemma structure_eq_of_structure_of_relational_iff [IsRelational L]
    {𝓜₁ 𝓜₂: L.Structure M} : 𝓜₁ = 𝓜₂ ↔ @RelMap L M 𝓜₁ = @RelMap L M 𝓜₂ := by
  constructor <;> intro h
  · simp only [h, implies_true]
  · ext1; exact h

lemma structure_eq_of_structure_of_relational_iff' [IsRelational L]
    {𝓜₁ 𝓜₂: L.Structure M} : 𝓜₁ = 𝓜₂ ↔ ∀ {n} r x, @RelMap L M 𝓜₁ n r x = @RelMap L M 𝓜₂ n r x := by
  constructor <;> intro h
  · simp only [h, implies_true]
  · ext1; funext n r x; exact h r x

end Relational

section Relational₂

lemma RelMap_eq_RelMap_of_relational₂ [IsRelational₂ L] (𝓜₁ 𝓜₂ : L.Structure M)
    {n} (hn : n ≠ 2) : @RelMap L M 𝓜₁ n = @RelMap L M 𝓜₂ n := by
  have : IsEmpty (L.Relations n) := by exact IsRelational₂.only_rel₂ hn
  rw [Subsingleton.elim (@RelMap L M 𝓜₁ n) (@RelMap L M 𝓜₂ n)]

lemma RelMap_eq_RelMap_of_relational₂' [IsRelational₂ L] (𝓜₁ 𝓜₂ : L.Structure M)
    {n} (hn : n ≠ 2) (nRel : L.Relations n) (x : Fin n → M) :
    𝓜₁.RelMap nRel x ↔ 𝓜₂.RelMap nRel x := by
  have : IsEmpty (L.Relations n) := by exact IsRelational₂.only_rel₂ hn
  rw [Subsingleton.elim (𝓜₁.RelMap) (𝓜₂.RelMap)]

@[ext]
lemma structure_eq_structure_of_relational₂ [IsRelational₂ L]
    {𝓜₁ 𝓜₂ : L.Structure M}
    (h : @RelMap L M 𝓜₁ 2 = @RelMap L M 𝓜₂ 2) : 𝓜₁ = 𝓜₂ := by
  ext1
  funext n
  by_cases h' : n = 2
  · subst h'
    exact h
  · apply RelMap_eq_RelMap_of_relational₂
    exact h'

lemma structure_eq_of_structure_of_relational₂_iff [IsRelational₂ L]
    {𝓜₁ 𝓜₂ : L.Structure M} : 𝓜₁ = 𝓜₂ ↔ @RelMap L M 𝓜₁ 2 = @RelMap L M 𝓜₂ 2 := by
  constructor <;> intro h
  · simp only [h, implies_true]
  · ext1; exact h

end Relational₂

end Structure --end

end FirstOrder.Language
