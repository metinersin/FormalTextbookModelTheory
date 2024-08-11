import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Order
import Mathlib.Order.CountableDenseLinearOrder

import FormalTextbookModelTheory.ForMathlib2.Matrix
import FormalTextbookModelTheory.ForMathlib2.Cardinal

open Cardinal
open FirstOrder Language Structure Theory Order
open Matrix (Vector_eq_VecNotation₂ comp_VecNotation₂)

namespace FirstOrder.Language.Order --region

section

variable {M : Type w} [instStructure : Language.order.Structure M]

instance instLE : LE M where
  le := fun x y => instStructure.RelMap leSymb ![x, y]

@[simp]
lemma orderStructure_of_LE : @orderStructure M instLE = instStructure := by
  ext1
  · funext _ r
    exfalso
    exact IsEmpty.elim (by infer_instance) r
  · funext n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp only [Language.order, mk₂_Relations, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, (by apply Subsingleton.allEq : r = leSymb)]
      simp only [orderStructure, LE.le, Structure.relMap_apply₂]

instance : @OrderedStructure Language.order M _ instLE instStructure := by
  simp only [OrderedStructure, orderLHom_order, orderStructure_of_LE]
  exact @LHom.id_isExpansionOn Language.order M instStructure

end

section

variable {M : Type w} [Language.order.Structure M]
variable {N : Type w} [Language.order.Structure N]

def toLEmbedding (φ : M ↪o N) : M ↪[Language.order] N where
  toEmbedding := φ.toEmbedding
  map_fun' := by
    intro n f
    exfalso
    exact IsEmpty.elim (by infer_instance) f
  map_rel' := by
    intro n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp [Language.order, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, comp_VecNotation₂ φ.toFun,
          (by apply Subsingleton.allEq : r = leSymb), relMap_leSymb, relMap_leSymb]
      exact φ.map_rel_iff

def toLIso (φ : M ≃o N) : M ≃[Language.order] N where
  toEquiv := φ.toEquiv
  map_fun' := (toLEmbedding (φ.toOrderEmbedding)).map_fun'
  map_rel' := (toLEmbedding (φ.toOrderEmbedding)).map_rel'

end

namespace DLO --region

section

variable (M : Type w) [Language.order.Structure M]
variable [M ⊨ Language.order.dlo]

protected lemma realize_reflexive : M ⊨ (leSymb (L := Language.order)).reflexive := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; left; rfl

protected lemma realize_transitive : M ⊨ (leSymb (L := Language.order)).transitive := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; right; left; rfl

protected lemma realize_antisymmetric : M ⊨ (leSymb (L := Language.order)).antisymmetric := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; left; rfl

protected lemma realize_total : M ⊨ (leSymb (L := Language.order)).total := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; right; right; rfl

protected lemma realize_denselyOrderedSentence : M ⊨ Language.order.denselyOrderedSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; right; right; rfl

protected lemma realize_noBotOrderSentence : M ⊨ Language.order.noBotOrderSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; right; left; rfl

protected lemma realize_noTopOrderSentence : M ⊨ Language.order.noTopOrderSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; left; rfl

end

section

variable {M : Type w} [instStructure : Language.order.Structure M]
variable [instModel : M ⊨ Language.order.dlo]

instance instPreorder : Preorder M where
  le := (@instLE M instStructure).le
  le_refl := by
    have := DLO.realize_reflexive M
    simp only [Relations.realize_reflexive] at this
    exact this
  le_trans := by
    have := DLO.realize_transitive M
    simp only [Relations.realize_transitive] at this
    exact this

@[simp]
lemma toLE_of_Preorder
    : (@instPreorder M instStructure instModel).toLE = @instLE M instStructure := rfl

noncomputable instance instLinearOrder : LinearOrder M where
  -- le := (@instLE M instStructure).le
  -- le_refl := by
  --   have := DLO.realize_reflexive M
  --   simp only [Relations.realize_reflexive] at this
  --   exact this
  -- le_trans := by
  --   have := DLO.realize_transitive M
  --   simp only [Relations.realize_transitive] at this
  --   exact this
  toPreorder := @instPreorder M instStructure instModel
  le_antisymm := by
    have := DLO.realize_antisymmetric M
    simp only [Relations.realize_antisymmetric] at this
    exact this
  le_total := by
    have := DLO.realize_total M
    simp only [Relations.realize_total] at this
    exact this
  decidableLE := by apply Classical.decRel

@[simp]
lemma toLE_of_LinearOrder
    : (@instLinearOrder M instStructure instModel).toLE = @instLE M instStructure := rfl

instance : @NoMinOrder M instLinearOrder.toLT where
  exists_lt := by
    have := DLO.realize_noBotOrderSentence M
    simp only [noBotOrderSentence] at this
    intro a
    replace this := this a
    simp at this
    rcases this with ⟨b, h⟩
    use b
    exact h

instance : @NoMaxOrder M instLinearOrder.toLT where
  exists_gt := by
    have := DLO.realize_noTopOrderSentence M
    simp only [noTopOrderSentence] at this
    intro a
    replace this := this a
    simp at this
    rcases this with ⟨b, h⟩
    use b
    exact h

instance instDenselyOrdered : DenselyOrdered M where
  dense := by
    have := DLO.realize_denselyOrderedSentence M
    simp only [denselyOrderedSentence] at this
    intro a₁ a₂ h
    replace this := this a₁ a₂
    simp only [BoundedFormula.realize_imp, Term.realize_lt, Term.realize_var,
               BoundedFormula.realize_ex, BoundedFormula.realize_inf] at this
    replace this := this h
    rcases this with ⟨a, h₁, h₂⟩
    use a
    exact ⟨h₁, h₂⟩

end

/--
This is my docstring
-/
theorem aleph0_categorical_of_dlo : aleph0.Categorical Language.order.dlo := by
  unfold Categorical
  rintro ⟨M⟩ ⟨N⟩ hM hN
  simp only at *
  apply Nonempty.map toLIso
  have := countable_of_mk_eq_aleph0 hM
  have := countable_of_mk_eq_aleph0 hN
  apply iso_of_countable_dense

end DLO --end

end FirstOrder.Language.Order --end
