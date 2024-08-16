import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order

namespace FirstOrder.Language

section

variable (L : Language) [L.IsOrdered]

@[simp]
theorem reflexive_mem_dlo : leSymb.reflexive ∈ L.dlo := by
  unfold dlo linearOrderTheory
  left; left; rfl

@[simp]
theorem transitive_mem_dlo : leSymb.transitive ∈ L.dlo := by
  unfold dlo linearOrderTheory
  left; right; right; left; rfl

@[simp]
theorem antisymmetric_mem_dlo : leSymb.antisymmetric ∈ L.dlo := by
  unfold dlo linearOrderTheory
  left; right; left; rfl

@[simp]
theorem total_mem_dlo : leSymb.total ∈ L.dlo := by
  unfold dlo linearOrderTheory
  left; right; right; right; rfl

@[simp]
theorem noBotOrder_mem_dlo : L.noBotOrderSentence ∈ L.dlo := by
  unfold dlo linearOrderTheory
  right; right; left; rfl

@[simp]
theorem noTopOrder_mem_dlo : L.noTopOrderSentence ∈ L.dlo := by
  unfold dlo linearOrderTheory
  right; left; rfl

@[simp]
theorem denselyOrdered_mem_dlo : L.denselyOrderedSentence ∈ L.dlo := by
  unfold dlo linearOrderTheory
  right; right; right; rfl

end

namespace Relations

open Structure
open BoundedFormula

variable {L : Language.{u, v}} [instIsOrdered : L.IsOrdered]
variable {M : Type w} [instStructure : L.Structure M]

local infix:50 " ≼ " => fun x y : M =>  @RelMap L M instStructure 2 (@leSymb L instIsOrdered) ![x, y]
local infix:50 " ≺ " => fun x y : M => x ≼ y ∧ ¬ y ≼ x

@[simp]
theorem realize_noBot : M ⊨ L.noBotOrderSentence ↔ ∀ x, ∃ y, ¬ x ≼ y := by
  unfold noBotOrderSentence Sentence.Realize Formula.Realize Term.le
  simp only [realize_all, realize_ex, realize_not, realize_rel₂]
  rfl

@[simp]
theorem realize_noTop : M ⊨ L.noTopOrderSentence ↔ ∀ x, ∃ y, ¬ y ≼ x := by
  unfold noTopOrderSentence Sentence.Realize Formula.Realize Term.le
  simp only [realize_all, realize_ex, realize_not, realize_rel₂]
  rfl

@[simp]
theorem realize_denselyOrdered : M ⊨ L.denselyOrderedSentence ↔ ∀ x y, x ≺ y → ∃ z, x ≺ z ∧ z ≺ y := by
  unfold denselyOrderedSentence Sentence.Realize Formula.Realize Term.lt Term.le
  simp only [realize_all, realize_imp, realize_inf, realize_rel₂, realize_not, realize_ex]
  rfl

end Relations

end FirstOrder.Language
