import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Order
import Mathlib.Order.CountableDenseLinearOrder
import FormalTextbookModelTheory.ForMathlib.Order

open Cardinal
open FirstOrder
open Language
open Order

namespace FirstOrder.Language.Order

-- def to_Lle_homomorphism {M N : Type w} [L≤.Structure M] [L≤.Structure N] (f : M →o N) : M →[L≤] N :=
--   by sorry

theorem aleph0_categorical_of_dlo : aleph0.Categorical L≤.dlo := by
  unfold Categorical
  rintro ⟨M⟩ ⟨N⟩ hM hN
  simp only at *
  constructor

  have instLinearOrderM : LinearOrder M := by exact inst_LinearOrder_of_dlo L≤
  have instLinearOrderN : LinearOrder N := by exact inst_LinearOrder_of_dlo L≤
  have instDensolyOrderedM : @DenselyOrdered M (inst_Preorder_of_dlo L≤).toLT := by
    exact inst_DenselyOrdered_of_dlo L≤

  sorry

#check iso_of_countable_dense

end FirstOrder.Language.Order
