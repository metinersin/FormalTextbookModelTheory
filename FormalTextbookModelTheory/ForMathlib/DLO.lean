import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Order

open Cardinal
open FirstOrder

universe u v w

notation "L≤" => Language.order

theorem aleph0_categorical_of_dlo : aleph0.Categorical L≤.dlo := by
  sorry

#check aleph0_categorical_of_dlo

-- Here, we will put definitions and theorems about the theory
-- of dense linear orders without endpoints.
